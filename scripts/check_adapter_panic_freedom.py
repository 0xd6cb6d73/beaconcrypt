#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Inventory the selected adapter extraction and reproduce its safety contracts.

The inventory contains names and classifications, never Lean propositions. The
normal-return conclusion is reconstructed from each generated signature. The
closed contract registry below is reviewed code: changing a precondition requires
reviewing this checker, rather than adding an arbitrary premise to a manifest.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import extract_adapter_authentication as authentication

NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9.]*\Z")
DECLARATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?def\s+([\w.]+)", re.M)
PURE_DICTIONARY_TYPES = {
    "core.fmt.Debug",
    "core.ops.function.FnOnce",
    "core.ops.function.FnMut",
    "core.ops.function.Fn",
    "core.hash.BuildHasher",
    "shared.SignaturePk",
    "rand_core.TryRng",
    "rand_core.TryCryptoRng",
    "BeaconcryptCore.Refinement.AdapterWirePrimitive.Serializer",
}
# A new extraction cohort requires an explicit review of its source boundary.
COHORTS = {
    "AdapterAuthenticationExtraction": "extract_adapter_authentication",
    "AdapterInitAuthenticationExtraction": "extract_adapter_init_authentication",
    "AdapterRecordExtraction": "extract_adapter_record",
    "AdapterRecordSendExtraction": "extract_adapter_record_send",
    "AdapterSealExtraction": "extract_adapter_seal",
    "AdapterSealJoinExtraction": "extract_adapter_seal_join",
    "AdapterRecordHelpersExtraction": "extract_adapter_record_helpers",
    "AdapterRecordRoutingExtraction": "extract_adapter_record_routing",
    "AdapterWireExtraction": "extract_adapter_wire",
    "AdapterRegistrationWriterExtraction": "extract_adapter_registration_writer",
    "AdapterPublicWrapperExtraction": "extract_adapter_public_wrappers",
    "AdapterPublicServerEntryExtraction": "extract_adapter_public_server_entry",
    "AdapterPublicOrdinaryExtraction": "extract_adapter_public_ordinary",
    "AdapterBeaconConstructorExtraction": "extract_adapter_beacon_constructor",
    "AdapterServerConstructorExtraction": "extract_adapter_server_constructor",
    "AdapterRatchetKdfExtraction": "extract_adapter_ratchet_kdf",
}
# The new source bodies are identical under both production role-only profiles.
COMPARED_FEATURE_PROFILES = {
    "AdapterRatchetKdfExtraction": {
        "canonical": {
            "default_features": False,
            "features": ["beacon", "server", "pqxdh"],
        },
        "beacon": {"default_features": False, "features": ["beacon", "pqxdh"]},
        "server": {"default_features": False, "features": ["server", "pqxdh"]},
    }
}
INTERPRETER_LIFTS = {
    "AdapterAuthenticationRequestExtraction",
    "AdapterInitAuthenticationRequestExtraction",
    "AdapterRecordRequestExtraction",
    "AdapterRecordSendRequestExtraction",
    "AdapterSealRequestExtraction",
    "AdapterSealJoinRequestExtraction",
    "AdapterRecordHelperRequestExtraction",
    "AdapterWireRequestExtraction",
    "AdapterRegistrationWriterRequestExtraction",
    "AdapterPublicWrapperRequestExtraction",
    "AdapterPublicServerEntryRequestExtraction",
    "AdapterPublicOrdinaryRequestExtraction",
    "AdapterBeaconConstructorRequestExtraction",
    "AdapterServerConstructorRequestExtraction",
    "AdapterPublicFinishObservedExtraction",
    "AdapterPublicBuildObservedExtraction",
}
INTENTIONAL_PANICS = {
    "beaconcrypt_constructor.beacon.Beacon.new",
    "beaconcrypt_server_constructor.server.Server.new",
}
# These are interfaces for individual dependencies, not conclusions about the
# extracted controllers. Additional state conditions are listed by operation
# below; a JSON entry cannot add or replace either kind of premise.
CONTRACTS = {
    "AdapterAuthenticationExtraction": "BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication.Contracts",
    "AdapterInitAuthenticationExtraction": "BeaconcryptCore.PanicFreedom.AdapterInitAuthentication.Contracts",
    "AdapterRecordExtraction": "BeaconcryptCore.PanicFreedom.AdapterRecordReceive.Contracts",
    "AdapterRecordSendExtraction": "BeaconcryptCore.PanicFreedom.AdapterRecordSend.Contracts",
    "AdapterRecordRoutingExtraction": "BeaconcryptCore.PanicFreedom.AdapterRecordRouting.Contracts",
    "AdapterRecordHelpersExtraction": "BeaconcryptCore.PanicFreedom.AdapterWire.Contracts",
    "AdapterSealExtraction": "BeaconcryptCore.PanicFreedom.AdapterSeal.Contracts",
    "AdapterSealJoinExtraction": "BeaconcryptCore.PanicFreedom.AdapterWire.Contracts",
    "AdapterWireExtraction": "BeaconcryptCore.PanicFreedom.AdapterWire.Contracts",
    "AdapterRegistrationWriterExtraction": "BeaconcryptCore.PanicFreedom.AdapterRegistrationWriter.Contracts",
    "AdapterBeaconConstructorExtraction": "BeaconcryptCore.PanicFreedom.AdapterConstructors.BeaconContracts",
    "AdapterServerConstructorExtraction": "BeaconcryptCore.PanicFreedom.AdapterConstructors.ServerContracts",
}
UNCONDITIONAL = {
    "beaconcrypt_public_wrapper.beacon.Beacon.identity_pk",
    "beaconcrypt_public_wrapper.beacon.Beacon.identity_sk",
    "beaconcrypt_public_wrapper.ratchet.RatchetKernelSlot.new",
    "beaconcrypt_public_wrapper.ratchet.RatchetManager.from_kernel",
    "beaconcrypt_public_wrapper.server.Server.identity_pk",
    "beaconcrypt_public_wrapper.server.Server.identity_key_kid",
    "beaconcrypt_public_wrapper.server.Server.identity_sk",
    "beaconcrypt_public_wrapper.shared.map_peer_ratchet",
    "beaconcrypt_public_wrapper.shared.EstablishedRemote.from_peer",
    "beaconcrypt_public_ordinary.server.ReceiveTransition.into_option",
    "beaconcrypt_public_ordinary.server.Server.identity_key_kid",
    "beaconcrypt_public_ordinary.shared.EstablishedRemote.ratchet_mut",
    "beaconcrypt_public_ordinary.shared.EstablishedRemote.binding",
    "beaconcrypt_public_ordinary.wire.frame_len",
    "beaconcrypt_public_ordinary.ratchet.RatchetStatus.impl.send_sequence",
    "beaconcrypt_public_ordinary.ratchet.decode_crypto_frame",
    "beaconcrypt_public_ordinary.ratchet.encrypted_frame_sender",
}
PUBLIC_TRIVIAL_CONTRACTS = {
    "beaconcrypt_public_wrapper.beacon.Beacon.mldsa_public_key",
    "beaconcrypt_public_wrapper.server.Server.mldsa_public_key",
    "beaconcrypt_public_wrapper.server.Server.authentication_pin",
}
ORDINARY = "BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary"
SOURCE_COMPOSITION = {
    "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response": "BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource",
}
DECODER_SOURCE = "BeaconcryptCore.PanicFreedom.AdapterRegistrationDecoderSource"
DECODER_COMPOSITION = {
    "beaconcrypt_public_wrapper.server.Server.authenticate_registration_lookup": "AuthenticationContracts",
    "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration": "FinishContracts",
    "beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng": "AuthenticationContracts",
}
WRITER_SOURCE = "BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSource"
PUBLIC_WRITER_SOURCE = (
    "BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationWriterSource"
)
WRITER_SELECTION = "BeaconcryptCore.Computational.RegistrationNativeSourceEncoders"
WRITER_COMPOSITION = {
    "beaconcrypt_registration_writer.wire.encode_init": "init",
    "beaconcrypt_registration_writer.wire.encode_response": "response",
    "beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng": "bundle",
    "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response": "build",
}
KDF_SOURCE = "BeaconcryptCore.PanicFreedom.AdapterRatchetKdfSource"
KDF_COMPOSITION = {
    "beaconcrypt_record_send.ratchet.execute_record_send": (
        "send",
        "execute_record_send",
    ),
    "beaconcrypt.ratchet.execute_record_receive": ("receive", "execute_record_receive"),
    "beaconcrypt_public_ordinary.beacon.Beacon.encrypt_message": (
        "send",
        "beacon_encrypt_message",
    ),
    "beaconcrypt_public_ordinary.beacon.Beacon.decrypt_message": (
        "receive",
        "beacon_decrypt_message",
    ),
    "beaconcrypt_public_ordinary.server.Server.encrypt_message": (
        "send",
        "server_encrypt_message",
    ),
    "beaconcrypt_public_ordinary.server.Server.decrypt_message": (
        "receive",
        "server_decrypt_message",
    ),
    "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration": (
        "finish",
        "finish_registration",
    ),
    "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response": (
        "build",
        "build_registration_response",
    ),
}
PRESERVATION_PREDICATES = {
    **{
        "beaconcrypt_public_ordinary."
        + operation: f"{ORDINARY}.ValidManager {{result}}.2"
        for operation in (
            "ratchet.encrypt_with_ratchet",
            "ratchet.encrypt_message_with_ratchet",
            "ratchet.decrypt_payload_with_ratchet",
            "ratchet.decrypt_message_with_ratchet",
        )
    },
    **{
        "beaconcrypt_public_ordinary."
        + operation: f"{ORDINARY}.ValidBeacon {{result}}.2"
        for operation in (
            "beacon.Beacon.encrypt_message",
            "beacon.Beacon.decrypt_message",
        )
    },
    **{
        "beaconcrypt_public_ordinary."
        + operation: f"{ORDINARY}.ValidServer {{result}}.2"
        for operation in (
            "server.Server.encrypt_message",
            "server.Server.decrypt_message_transition",
            "server.Server.decrypt_message",
        )
    },
    "beaconcrypt_public_ordinary.server.Server.ratchet_manager_mut": f"{ORDINARY}.ValidOptionalManager {{result}}.1 ∧ ∀ replacement, "
    f"{ORDINARY}.ValidOptionalManager replacement → {ORDINARY}.ValidServer ({{result}}.2 replacement)",
    "beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng": f"{ORDINARY}.ValidBeacon {{result}}.2.1",
    "beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng": f"{ORDINARY}.ValidServer {{result}}.2.1",
    "beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng": f"{ORDINARY}.ValidServer {{result}}.2.1",
    "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration": f"{ORDINARY}.ValidBeacon {{result}}.2",
    "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop": "BeaconcryptCore.PanicFreedom.AdapterPublicFinishSafety.ValidFinishedState {result}.2.2",
    "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop.body": "BeaconcryptCore.PanicFreedom.AdapterPublicFinishSafety.BodyInvariant {result}",
    "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response": f"{ORDINARY}.ValidServer {{result}}.2",
    **{
        f"{namespace}.{role}.{role_class}.{operation}": f"match {{result}}{'.1' if operation.endswith('with_rng') else ''} with "
        f"| .Ok constructed => {ORDINARY}.Valid{role_class} constructed | .Err _ => True"
        for namespace, role, role_class in (
            ("beaconcrypt_constructor", "beacon", "Beacon"),
            ("beaconcrypt_server_constructor", "server", "Server"),
        )
        for operation in ("try_new_with_rng", "try_new")
    },
}


def assumptions(cohort: str, definition: "Definition") -> list[str]:
    """Closed, reviewed premise policy; never read propositions from JSON."""
    # Error-conversion closures are directly total and need no primitive law.
    if definition.role == "closure-helper" and "Constructor" in cohort:
        return []
    if definition.name in UNCONDITIONAL:
        return []
    if (
        cohort
        in {
            "AdapterRecordExtraction",
            "AdapterRecordSendExtraction",
            "AdapterRecordHelpersExtraction",
        }
        and definition.role == "closure-helper"
    ):
        return []
    if definition.name in PUBLIC_TRIVIAL_CONTRACTS:
        return [
            "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterPublicTrivial.Contracts)"
        ]
    if definition.name == "beaconcrypt_public_wrapper.auth.fingerprint_pin":
        return [
            "(_adapter_hash : ∀ request, BeaconcryptCore.PanicFreedom.AdapterNormal.Normal "
            "(beaconcrypt.auth.Operations.hash request))"
        ]
    if cohort in {
        "AdapterBeaconConstructorExtraction",
        "AdapterServerConstructorExtraction",
    }:
        if definition.local_name.endswith(".try_new_with_rng"):
            generator = selected_rng(definition)
        elif definition.local_name.endswith(".try_new"):
            generator = "BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard.os"
        else:
            raise ValueError(
                "no reviewed selected-constructor contract for " + definition.name
            )
        return [f"(_adapter_contracts : {CONTRACTS[cohort]} {generator})"]
    if cohort == "AdapterPublicOrdinaryExtraction":
        ordinary = "BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary"
        local_name = definition.local_name
        if local_name in {
            "ratchet.RatchetKernelSlot.take",
            "ratchet.RatchetKernelSlot.Insts.CoreOpsDerefDerefConcreteRatchetKernel.deref",
        }:
            return [f"(_adapter_valid : {ordinary}.Populated self)"]
        if local_name == "ratchet.RatchetKernelSlot.put":
            return [f"(_adapter_valid : {ordinary}.Empty self)"]
        if local_name in {
            "ratchet.RatchetManager.status",
            "ratchet.RatchetManager.send_sequence",
        }:
            return [f"(_adapter_valid : {ordinary}.ValidManager self)"]
        if local_name in {
            "server.Server.associated_data",
            "server.Server.ratchet_manager_mut",
        }:
            result = [f"(_adapter_lookups : {ordinary}.LookupContracts)"]
            if local_name.endswith("ratchet_manager_mut"):
                result.append(f"(_adapter_valid : {ordinary}.ValidServer self)")
            return result
        send = local_name in {
            "ratchet.encrypt_with_ratchet",
            "ratchet.encrypt_message_with_ratchet",
            "beacon.Beacon.encrypt_message",
            "server.Server.encrypt_message",
        }
        receive = local_name in {
            "ratchet.decrypt_payload_with_ratchet",
            "ratchet.decrypt_message_with_ratchet",
            "beacon.Beacon.decrypt_message",
            "server.Server.decrypt_message_transition",
            "server.Server.decrypt_message",
        }
        if send or receive:
            dependency = "AdapterRecordSend" if send else "AdapterRecordReceive"
            result = [
                f"(_adapter_record : BeaconcryptCore.PanicFreedom.{dependency}.Contracts)"
            ]
            if local_name.startswith("ratchet."):
                result.append(f"(_adapter_valid : {ordinary}.ValidManager ratchet1)")
            elif local_name.startswith("beacon."):
                result.append(f"(_adapter_valid : {ordinary}.ValidBeacon self)")
            else:
                result += [
                    f"(_adapter_lookups : {ordinary}.LookupContracts)",
                    f"(_adapter_valid : {ordinary}.ValidServer self)",
                ]
            return result
        raise ValueError(
            "no reviewed ordinary-operation precondition: " + definition.name
        )
    loops = "BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops"
    if cohort == "AdapterPublicWrapperExtraction":
        if "_proof_beacon_init_ready" in definition.local_name:
            return [f"(_adapter_contracts : {loops}.InitContracts)"]
        if "finish_registration_loop" in definition.local_name:
            return [
                "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterRecordReceive.Contracts)"
            ]
        if definition.local_name.startswith("pqxdh.execute_"):
            result = [f"(_adapter_contracts : {loops}.AgreementContracts)"]
            if definition.local_name == "pqxdh.execute_beacon_agreement":
                generator = "beaconcrypt_public_wrapper.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError"
            elif definition.role != "closure-helper":
                generator = selected_rng(definition)
            elif ".closure_2.Insts." in definition.local_name:
                return result + [
                    f"(_adapter_rng : {loops}.EncapsulationContracts {selected_rng(definition)})"
                ]
            else:
                return result
            return result + [
                f"(_adapter_rng : {loops}.AgreementRngContracts {generator})"
            ]
    if (
        definition.name
        == "beaconcrypt_public_wrapper.server.Server.authenticate_registration_lookup"
    ):
        return [
            "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterPublicServer.AuthenticationContracts)"
        ]
    if (
        definition.name
        == "beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng"
    ):
        return [
            "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterPublicBeacon.BundleContracts)",
            f"(_adapter_rng : {loops}.GenerationContracts {selected_rng(definition)})",
        ]
    if (
        definition.name
        == "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration"
    ):
        return [
            "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterPublicBeaconFinish.Contracts)"
        ]
    if definition.name == "beaconcrypt_public_wrapper.server.registration_response_len":
        return []
    if definition.name in {
        "beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng",
        "beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng",
    }:
        result = [
            f"(_adapter_contracts : {loops}.AgreementContracts)",
            f"(_adapter_rng : {loops}.AgreementRngContracts {selected_rng(definition)})",
            "(_adapter_replay : BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept.ReplayContracts)",
        ]
        if cohort == "AdapterPublicServerEntryExtraction":
            result.append(
                "(_adapter_authentication : BeaconcryptCore.PanicFreedom.AdapterPublicServer.AuthenticationContracts)"
            )
        return result
    if (
        definition.name
        == "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response"
    ):
        return [
            "(_adapter_contracts : BeaconcryptCore.PanicFreedom.AdapterPublicServerBuild.Contracts)"
        ]
    if cohort == "AdapterRatchetKdfExtraction":
        sizes = {
            "ratchet.symmetric_ratchet_hkdf": "OUTPUT_SIZE",
            "ratchet.ratchet_hkdf": "76#usize",
            "ratchet.initial_ratchet_hkdf": "64#usize",
        }
        if definition.local_name not in sizes:
            raise ValueError(
                "unreviewed native ratchet KDF operation: " + definition.name
            )
        size = sizes[definition.local_name]
        result = [
            f"(_adapter_kdf : BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.Contracts {size})"
        ]
        if size == "OUTPUT_SIZE":
            result.append("(_adapter_output_bound : OUTPUT_SIZE.val ≤ 16320)")
        return result
    if cohort not in CONTRACTS:
        raise ValueError(
            f"no reviewed external-operation contract for {definition.name}"
        )
    result = [f"(_adapter_contracts : {CONTRACTS[cohort]})"]
    if cohort == "AdapterWireExtraction":
        result += [
            "(_adapter_serializer_normal : BeaconcryptCore.PanicFreedom.AdapterWire.SerializerNormal "
            "coreopsfunctionFnOnceT0TupleMutSliceU8UsizeInst)"
        ]
    if cohort == "AdapterRegistrationWriterExtraction":
        result += [
            "(_adapter_wire_contracts : BeaconcryptCore.PanicFreedom.AdapterWire.Contracts)"
        ]
    return result


@dataclass(frozen=True)
class Definition:
    name: str
    local_name: str
    namespace: str
    binders: str
    arguments: str
    return_type: str
    monadic: bool
    role: str
    openings: tuple[str, ...] = ()


def code(source: str) -> str:
    """Erase nested comments and strings without changing source positions."""
    return authentication.lean_code_without_comments_or_strings(source.encode())


def binder_groups(binders: str, name: str) -> list[tuple[str, list[str], str]]:
    """Read balanced generated binders, retaining their names and exact types."""
    result = []
    seen = set()
    remaining = binders
    while remaining.strip():
        remaining = remaining.lstrip()
        opening = remaining[0]
        if opening not in "({[":
            raise ValueError(f"unsupported binder for {name}: {remaining}")
        depth = 0
        for offset, character in enumerate(remaining):
            if character in "({[":
                depth += 1
            elif character in ")}]":
                depth -= 1
                if depth == 0:
                    break
        else:
            raise ValueError(f"unclosed binder for {name}")
        group, remaining = remaining[1:offset], remaining[offset + 1 :]
        if ":" not in group:
            raise ValueError(f"unnamed binder for {name}: {group}")
        variables, type_name = group.split(":", 1)
        if not type_name.strip():
            raise ValueError(f"missing binder type for {name}: {group}")
        named = []
        for variable in variables.split():
            # Anonymous generated arguments must be named in the checked wrapper.
            if variable == "_":
                variable = "adapter_unit_argument"
            if not NAME.fullmatch(variable):
                raise ValueError(f"unsupported binder name for {name}: {variable}")
            if variable in seen:
                raise ValueError(
                    f"duplicate or colliding binder for {name}: {variable}"
                )
            seen.add(variable)
            named.append(variable)
        if not named:
            raise ValueError(f"unnamed binder for {name}: {group}")
        result.append((opening, named, type_name.strip()))
    return result


def arguments(binders: str, name: str) -> str:
    result = []
    for opening, variables, _ in binder_groups(binders, name):
        result.extend(
            f"({variable} := {variable})" if opening in "{[" else variable
            for variable in variables
        )
    return " ".join(result)


def selected_rng(definition: Definition) -> str:
    """Bind execution laws to the actual generated RNG argument, never a family."""
    selected = []
    for _, variables, type_name in binder_groups(definition.binders, definition.name):
        if "rand_core.TryCryptoRng" not in type_name:
            continue
        if len(variables) != 1 or not re.fullmatch(
            r"rand_core\.TryCryptoRng\s+[A-Za-z_][A-Za-z_0-9]*\s+[A-Za-z_][A-Za-z_0-9]*",
            type_name,
        ):
            raise ValueError(
                f"unreviewed RNG binder for {definition.name}: {type_name}"
            )
        selected.extend(variables)
    if len(selected) != 1:
        raise ValueError(
            f"expected exactly one selected RNG for {definition.name}: {selected}"
        )
    return selected[0]


def declarations(source: str) -> tuple[str, list[str], dict[str, Definition]]:
    stripped = code(source)
    namespaces = re.findall(r"^namespace\s+(\S+)", stripped, re.M)
    if len(namespaces) != 1 or not NAME.fullmatch(namespaces[0]):
        raise ValueError("generated module must have exactly one reviewed namespace")
    namespace = namespaces[0]
    openings = tuple(re.findall(r"^open\s+([^\n]+)", stripped, re.M))
    instances = re.findall(r"^variable\s+(\[[^\n]+\])\s*$", stripped, re.M)
    if len(instances) != len(re.findall(r"^variable\b", stripped, re.M)):
        raise ValueError("unparsed global instance binder")
    matches = list(DECLARATION.finditer(stripped))
    if len(matches) != len(re.findall(r"\bdef\s", stripped)):
        raise ValueError("unparsed generated definition; review the adapter parser")
    result = {}
    for index, match in enumerate(matches):
        local_name = match[1]
        name = namespace + "." + local_name
        end = matches[index + 1].start() if index + 1 < len(matches) else len(stripped)
        block = stripped[match.end() : end]
        if ":=" not in block:
            raise ValueError(f"missing body for {name}")
        header = block.split(":=", 1)[0]
        depth = 0
        colon = None
        for offset, character in enumerate(header):
            if character in "({[":
                depth += 1
            elif character in ")}]":
                depth -= 1
            elif character == ":" and depth == 0:
                colon = offset
                break
        if colon is None:
            raise ValueError(f"missing return type for {name}")
        binders = header[:colon].strip()
        binders = re.sub(r"\(_\s*:", "(adapter_unit_argument :", binders)
        return_type = header[colon + 1 :].strip()
        monadic = bool(re.match(r"RustM(?:\s|$)", return_type))
        if not monadic:
            returned_type = re.match(r"[\w.]+", return_type)
            if (
                ".Insts." not in name
                or returned_type is None
                or returned_type[0] not in PURE_DICTIONARY_TYPES
            ):
                raise ValueError(
                    f"unreviewed non-RustM return shape for {name}: {return_type}"
                )
            role = "pure-instance"
        elif name in INTENTIONAL_PANICS:
            if "core.result.Result.expect" not in block.split(":=", 1)[1]:
                raise ValueError(
                    "intentional constructor exception lost its Result.expect: " + name
                )
            role = "intentional-panic"
        elif re.search(r"\.closure(?:_\d+)?\.Insts\.", name):
            role = "closure-helper"
        elif "rust_loop" in match[0]:
            role = "loop-helper"
        elif "_proof_" in name:
            role = "specialized-extraction-helper"
        else:
            # Original source comments are retained by the source/provenance gate.
            preceding = source[: match.start()]
            comment = preceding[preceding.rfind("/--") :]
            role = (
                "production-entry"
                if "Visibility: public" in comment
                else "internal-helper"
            )
        if name in result:
            raise ValueError(f"duplicate generated definition: {name}")
        result[name] = Definition(
            name,
            local_name,
            namespace,
            binders,
            arguments(binders, name),
            return_type,
            monadic,
            role,
            openings,
        )
    return namespace, instances, result


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def modeled_declarations(source: str) -> list[str]:
    namespaces, declarations = [], []
    events = re.compile(
        r"^(?:@\[[^\]]*\]\s*)?"
        r"(namespace|end|def|abbrev|class|structure|inductive)\s+([\w.]+)",
        re.M,
    )
    for event in events.finditer(code(source)):
        command, identifier = event[1], event[2]
        if command == "namespace":
            namespaces.append(identifier)
        elif command == "end":
            if namespaces and identifier == namespaces[-1]:
                namespaces.pop()
        else:
            declarations.append(".".join([*namespaces, identifier]))
    return declarations


def interpreter_lifts(proof: Path) -> dict:
    actual = {path.stem for path in proof.glob("Adapter*Extraction.lean")}
    if actual != INTERPRETER_LIFTS:
        raise ValueError(
            f"interpreter-lift roster drift: missing={sorted(INTERPRETER_LIFTS-actual)}, "
            f"new={sorted(actual-INTERPRETER_LIFTS)}"
        )
    result = {}
    for name in sorted(actual):
        path = proof / (name + ".lean")
        source = code(path.read_text())
        namespaces = []
        declarations = []
        events = re.compile(
            r"^(?:@\[[^\]]*\]\s*)?"
            r"(namespace|end|def|abbrev|class|structure)\s+([\w.]+)",
            re.M,
        )
        definition_count = 0
        for event in events.finditer(source):
            command, identifier = event[1], event[2]
            if command == "namespace":
                namespaces.append(identifier)
            elif command == "end":
                if namespaces and identifier == namespaces[-1]:
                    namespaces.pop()
            else:
                declarations.append(".".join([*namespaces, identifier]))
                definition_count += command == "def"
        if definition_count != len(re.findall(r"\bdef\s", source)):
            raise ValueError("unparsed interpreter-lift definition: " + name)
        result[name] = {
            "classification": "interpreter-request-or-observation-lift",
            "native_RustM_totality_certificate": False,
            "sha256": sha256(path),
            "declarations": declarations,
            "execution_boundary": "normality requires a selected interpreter plus correspondence and execution contracts",
        }
    return result


def compared_profile_inventory(cohort: str, directory: Path) -> dict | None:
    if cohort not in COMPARED_FEATURE_PROFILES:
        return None
    provenance = json.loads((directory / "provenance.json").read_text())
    expected = COMPARED_FEATURE_PROFILES[cohort]
    if provenance.get("feature_profiles") != expected:
        raise ValueError("compared feature-profile configuration drift: " + cohort)
    comparisons = provenance.get("profile_comparisons")
    if not isinstance(comparisons, dict) or set(comparisons) != set(expected):
        raise ValueError("compared feature-profile roster drift: " + cohort)
    installed = {name: sha256(directory / name) for name in ("Types.lean", "Funs.lean")}
    for name, comparison in comparisons.items():
        if not isinstance(comparison, dict) or set(comparison) != {
            "raw_generated_sha256",
            "normalized_generated_sha256",
        }:
            raise ValueError("compared feature-profile fields drift: " + name)
        if comparison["raw_generated_sha256"] != provenance["raw_generated_sha256"]:
            raise ValueError("compared feature-profile raw output drift: " + name)
        if comparison["normalized_generated_sha256"] != installed:
            raise ValueError("compared feature-profile installed output drift: " + name)
    return {
        name: {**configuration, "generated_sha256": installed}
        for name, configuration in expected.items()
    }


def inventory(
    root: Path,
) -> tuple[dict, dict[str, tuple[str, list[str], dict[str, Definition]]]]:
    proof = root / "beaconcrypt-core/proofs/lean/BeaconcryptCore"
    actual = {path.parent.name for path in proof.glob("Adapter*Extraction/Funs.lean")}
    if actual != set(COHORTS):
        raise ValueError(
            f"adapter extraction cohort drift: missing={sorted(set(COHORTS)-actual)}, "
            f"new={sorted(actual-set(COHORTS))}"
        )
    output, parsed = {}, {}
    for cohort, script in sorted(COHORTS.items()):
        directory = proof / cohort
        namespace, instances, definitions = declarations(
            (directory / "Funs.lean").read_text()
        )
        parsed[cohort] = namespace, instances, definitions
        script_source = (root / "scripts" / (script + ".py")).read_text()
        profiles = set(re.findall(r'"--features=([^"\n]+)"', script_source))
        if len(profiles) != 1 or '"--no-default-features"' not in script_source:
            raise ValueError(f"unreviewed feature profile for {cohort}")
        external = {}
        for filename in ("TypesExternal.lean", "FunsExternal.lean"):
            source = (directory / filename).read_text()
            external[filename] = {
                "sha256": sha256(directory / filename),
                "declarations": modeled_declarations(source),
            }
        output[cohort] = {
            "extractor": "scripts/" + script + ".py",
            "features": sorted(next(iter(profiles)).split(",")),
            "default_features": False,
            "namespace": namespace,
            "opening_commands": list(next(iter(definitions.values())).openings),
            "instance_parameters": instances,
            "generated_sha256": {
                filename: sha256(directory / filename)
                for filename in ("Funs.lean", "Types.lean")
            },
            "external_models": external,
            "definitions": {
                name: {
                    "role": definition.role,
                    "monadic": definition.monadic,
                    "binders": definition.binders,
                    "return_type": definition.return_type,
                }
                for name, definition in sorted(definitions.items())
            },
        }
        compared = compared_profile_inventory(cohort, directory)
        if compared is not None:
            output[cohort]["compared_feature_profiles"] = compared
    exceptions = {
        name
        for _, _, ds in parsed.values()
        for name in ds
        if name in INTENTIONAL_PANICS
    }
    if exceptions != INTENTIONAL_PANICS:
        raise ValueError("intentional constructor-panic exception drift")
    return {
        "native_cohorts": output,
        "interpreter_lifts": interpreter_lifts(proof),
    }, parsed


def preservation_assumptions(cohort: str, definition: Definition) -> list[str]:
    result = assumptions(cohort, definition)
    if definition.name in {
        "beaconcrypt_public_wrapper.beacon.Beacon.get_registration_bundle_with_rng",
        "beaconcrypt_public_wrapper.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration",
    }:
        result = [*result, f"(_adapter_valid : {ORDINARY}.ValidBeacon self)"]
    if definition.name in {
        "beaconcrypt_public_wrapper.server.Server.get_shared_secret_from_lookup_with_rng",
        "beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng",
    }:
        result = [
            *result,
            "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
            f"(_adapter_valid : {ORDINARY}.ValidServer self)",
        ]
    if (
        definition.name
        == "beaconcrypt_public_wrapper.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response"
    ):
        result += [
            "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
            "(_adapter_laws : BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState.ContainerContracts)",
            f"(_adapter_valid : {ORDINARY}.ValidServer self)",
        ]
    if (
        cohort == "AdapterServerConstructorExtraction"
        and definition.role != "closure-helper"
    ):
        result += [
            "[_adapter_allocator : BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]",
            "[_adapter_local : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]",
            "[_adapter_containers : BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]",
            "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
            "(_adapter_initialization : BeaconcryptCore.PanicFreedom.AdapterConstructorValidity.InitializationContracts)",
        ]
    return result


REQUIRED_SOURCE_SAFETY_MODULES = {
    "AdapterRegistrationDecoderSource",
    "AdapterRegistrationWriterCallers",
    "AdapterRegistrationWriterSource",
    "AdapterRegistrationWriterSourceRegression",
    "AdapterPublicRegistrationWriterSource",
    "AdapterFiniteCalls",
    "AdapterFiniteCallsCoverage",
    "AdapterFiniteCallsSource",
    "AdapterFiniteCallsKdfSource",
    "AdapterRatchetKdf",
    "AdapterRatchetKdfSource",
    "AdapterRatchetKdfRegression",
}


# Typed, independently compiled guards pin native routing, structural iteration,
# construction, and the exact normal-return/valid-state conclusions. Their
# statements live in reviewed Lean code, never in an arbitrary JSON proposition.
REQUIRED_SOURCE_THEOREMS = [
    "BeaconcryptCore.PanicFreedom.AdapterFiniteCallsCoverage." + role + suffix
    for role in ("beacon", "server")
    for suffix in (
        "_finish_native" if role == "beacon" else "_build_native",
        "_bundle_native" if role == "beacon" else "_accept_native",
        "_send_native",
        "_receive_native",
        "_nil_exact",
        "_cons_exact",
        "_sequence_normal_valid",
        "_constructor_native",
        "_constructor_sequence_normal_valid",
        "_successful_constructor_sequence_normal_valid",
        "_hosted_constructor_native",
        "_hosted_constructor_sequence_normal_valid",
        "_hosted_successful_constructor_sequence_normal_valid",
    )
] + [
    "BeaconcryptCore.PanicFreedom.AdapterFiniteCallsKdfSource." + endpoint
    for endpoint in (
        "beacon_calls_preserve",
        "server_calls_preserve",
        "constructor_and_beacon_calls_preserve",
        "constructor_and_server_calls_preserve",
        "hosted_constructor_and_beacon_calls_preserve",
        "hosted_constructor_and_server_calls_preserve",
    )
]


def safety_modules(root: Path) -> list[str]:
    proof = root / "beaconcrypt-core/proofs/lean/BeaconcryptCore/PanicFreedom"
    actual = {path.stem for path in proof.glob("Adapter*.lean")}
    missing = REQUIRED_SOURCE_SAFETY_MODULES - actual
    if missing:
        raise ValueError(f"required source-safety module omission: {sorted(missing)}")
    return sorted(
        "BeaconcryptCore.PanicFreedom." + path.stem
        for path in (
            root / "beaconcrypt-core/proofs/lean/BeaconcryptCore/PanicFreedom"
        ).glob("Adapter*.lean")
        if path.stem != "AdapterCoverage"
    )


def source_composition_assumptions(name: str, preserve: bool) -> list[str]:
    """Fixed primitive/structural boundary for the source-selected public builder."""
    source = SOURCE_COMPOSITION[name]
    result = [
        "[_adapter_seal_primitives : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]",
        "[_adapter_frame_fallback : BeaconcryptCore.Refinement.FrameDispatchFallback.Operations]",
        "(_adapter_seal_fallback : BeaconcryptCore.Refinement.AdapterSealJoinCallbacks.Operations)",
        "(_adapter_writer_fallback : BeaconcryptCore.Refinement.RecordRoutingCallbacks.Operations)",
        f"(_adapter_source_contracts : {source}.Contracts)",
    ]
    if preserve:
        result += [
            "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
            "(_adapter_laws : BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState.ContainerContracts)",
            f"(_adapter_valid : {ORDINARY}.ValidServer self)",
        ]
    return result


def decoder_composition_assumptions(
    definition: Definition, preserve: bool
) -> list[str]:
    """Actual extracted decoders; no normality premise for an opaque codec."""
    result = [
        "[_adapter_validator : BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations]",
        f"(_adapter_decoded_contracts : {DECODER_SOURCE}.{DECODER_COMPOSITION[definition.name]})",
    ]
    if definition.name.startswith("beaconcrypt_public_server_entry."):
        loops = "BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops"
        result += [
            f"(_adapter_agreement : {loops}.AgreementContracts)",
            f"(_adapter_rng : {loops}.AgreementRngContracts {selected_rng(definition)})",
            "(_adapter_replay : BeaconcryptCore.PanicFreedom.AdapterPublicServerAccept.ReplayContracts)",
        ]
        if preserve:
            result += [
                "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
                f"(_adapter_valid : {ORDINARY}.ValidServer self)",
            ]
    elif preserve:
        result += [f"(_adapter_valid : {ORDINARY}.ValidBeacon self)"]
    return result


def writer_composition_assumptions(definition: Definition, preserve: bool) -> list[str]:
    """Source serializers at native signed-view callers and sized helper inputs."""
    kind = WRITER_COMPOSITION[definition.name]
    result = [
        "(_adapter_other : BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.OtherBranches)",
    ]
    if kind in {"init", "response"}:
        shape = "Init" if kind == "init" else "Response"
        result += [
            "(_adapter_allocation : BeaconcryptCore.PanicFreedom.AdapterWire.Contracts)",
            f"(_adapter_shape : BeaconcryptCore.Refinement.RegistrationSerializer{shape}Bytes.{shape}Shape {kind})",
        ]
    else:
        contract = "BundleContracts" if kind == "bundle" else "ResponseContracts"
        if kind == "bundle":
            result += [
                f"(_adapter_writer_source_contracts : {PUBLIC_WRITER_SOURCE}.{contract})",
                "(_adapter_rng : BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops.GenerationContracts "
                + selected_rng(definition)
                + ")",
            ]
        else:
            result += [
                "[_adapter_seal_primitives : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]",
                "[_adapter_frame_fallback : BeaconcryptCore.Refinement.FrameDispatchFallback.Operations]",
                f"(_adapter_writer_source_contracts : {PUBLIC_WRITER_SOURCE}.{contract})",
                "(_adapter_seal_fallback : BeaconcryptCore.Refinement.AdapterSealJoinCallbacks.Operations)",
                "(_adapter_writer_fallback : BeaconcryptCore.Refinement.RecordRoutingCallbacks.Operations)",
            ]
        if preserve:
            if kind == "build":
                result += [
                    "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
                    "(_adapter_laws : BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState.ContainerContracts)",
                ]
            state = "Beacon" if kind == "bundle" else "Server"
            result += [f"(_adapter_valid : {ORDINARY}.Valid{state} self)"]
    return result


def kdf_composition_assumptions(
    definition: Definition, instance_binders: list[str], preserve: bool
) -> list[str]:
    """Selected API success/borrow laws replace opaque ratchet KDF normality."""
    kind, _ = KDF_COMPOSITION[definition.name]
    result = []
    required = [
        "BeaconcryptCore.Refinement.PublicWrapperPlatform.Material",
        "BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations",
        "BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations",
        "BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive.Operations",
    ]
    if kind == "finish":
        required += [
            "BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations"
        ]
    if kind == "build":
        required += [
            "BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations",
            "BeaconcryptCore.Refinement.FrameDispatchFallback.Operations",
        ]
    for index, instance in enumerate(required):
        if not any(
            binder.endswith(": " + instance + "]") for binder in instance_binders
        ):
            result.append(f"[_adapter_kdf_instance_{index:02d} : {instance}]")
    result += [
        "(_adapter_ongoing : BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.Contracts 76#usize)"
    ]
    if kind in {"finish", "build"}:
        result += [
            "(_adapter_initial : BeaconcryptCore.PanicFreedom.AdapterRatchetKdf.Contracts 64#usize)"
        ]
    contract = {
        "send": "SendContracts",
        "receive": "ReceiveContracts",
        "finish": "FinishContracts",
        "build": "ResponseContracts",
    }[kind]
    result += [f"(_adapter_kdf_leaves : {KDF_SOURCE}.{contract})"]
    if kind == "build":
        result += [
            "(_adapter_other : BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.OtherBranches)",
            "(_adapter_seal_fallback : BeaconcryptCore.Refinement.AdapterSealJoinCallbacks.Operations)",
            "(_adapter_writer_fallback : BeaconcryptCore.Refinement.RecordRoutingCallbacks.Operations)",
        ]
        if preserve:
            result += [
                "[_adapter_lookup : BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]",
                "(_adapter_laws : BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildState.ContainerContracts)",
            ]
    if definition.name.startswith("beaconcrypt_public_ordinary.server."):
        result += [f"(_adapter_lookups : {ORDINARY}.LookupContracts)"]
    if definition.name.startswith("beaconcrypt_public_ordinary.") or preserve:
        state = "Server" if ".server." in definition.name else "Beacon"
        result += [f"(_adapter_valid : {ORDINARY}.Valid{state} self)"]
    return result


def kdf_selection(kind: str) -> list[str]:
    if kind in {"send", "receive"}:
        dictionary = (
            "beaconcrypt_record_send.ratchet.Operations"
            if kind == "send"
            else "beaconcrypt.ratchet.Operations"
        )
        selector = (
            "sourceSendOperations" if kind == "send" else "sourceReceiveOperations"
        )
        return [f"letI := {KDF_SOURCE}.{selector} (inferInstance : {dictionary})"]
    result = [
        f"letI := {KDF_SOURCE}.sourceReceiveOperations (inferInstance : beaconcrypt.ratchet.Operations)",
        f"letI := {KDF_SOURCE}.sourceLocalOperations (inferInstance : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations)",
    ]
    if kind == "finish":
        result += [f"letI := {DECODER_SOURCE}.sourceCodecs"]
    else:
        result += [
            f"letI := {WRITER_SELECTION}.sourceOperations _adapter_other",
            "letI := BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.sourceLocalOperations "
            "(inferInstance : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations) "
            "_adapter_seal_fallback _adapter_writer_fallback",
        ]
    return result


def render(
    parsed: dict, certificates: dict, additional_modules: list[str] | None = None
) -> str:
    operations = {
        name: (cohort, definition)
        for cohort, (_, _, definitions) in parsed.items()
        for name, definition in definitions.items()
        if definition.monadic and definition.role != "intentional-panic"
    }
    if set(certificates) != set(operations):
        raise ValueError(
            f"adapter operation coverage differs: missing={sorted(set(operations)-set(certificates))}, "
            f"extra={sorted(set(certificates)-set(operations))}"
        )
    imports = set(additional_modules or [])
    imports.update(
        "BeaconcryptCore." + cohort + ".Funs" for cohort in parsed if cohort in COHORTS
    )
    for name, certificate in certificates.items():
        required = {"module", "theorem", "form"}
        if name in PRESERVATION_PREDICATES:
            required.add("preservation")
        if name in SOURCE_COMPOSITION:
            required.add("source_composition")
            imports.add(SOURCE_COMPOSITION[name])
        if name in DECODER_COMPOSITION:
            required.add("decoder_composition")
            imports.add(DECODER_SOURCE)
        if name in WRITER_COMPOSITION:
            required.add("writer_composition")
            imports.update((WRITER_SOURCE, PUBLIC_WRITER_SOURCE))
        if name in KDF_COMPOSITION:
            required.add("kdf_composition")
            imports.add(KDF_SOURCE)
        if set(certificate) != required:
            raise ValueError(f"invalid certificate fields for {name}")
        if not NAME.fullmatch(certificate["module"]) or not NAME.fullmatch(
            certificate["theorem"]
        ):
            raise ValueError(f"invalid certificate name for {name}")
        if certificate["form"] not in {"exists", "equation"}:
            raise ValueError(f"invalid certificate form for {name}")
        imports.add(certificate["module"])
        if name in PRESERVATION_PREDICATES:
            preserved = certificate["preservation"]
            if set(preserved) != {"module", "theorem"} or not all(
                NAME.fullmatch(value) for value in preserved.values()
            ):
                raise ValueError(f"invalid preservation certificate for {name}")
            imports.add(preserved["module"])
        if name in SOURCE_COMPOSITION:
            composed = certificate["source_composition"]
            if set(composed) != {"module", "theorem", "preservation"} or not all(
                NAME.fullmatch(composed[key]) for key in ("module", "theorem")
            ):
                raise ValueError(f"invalid source composition certificate for {name}")
            preserved = composed["preservation"]
            if set(preserved) != {"module", "theorem"} or not all(
                NAME.fullmatch(value) for value in preserved.values()
            ):
                raise ValueError(f"invalid source preservation certificate for {name}")
            imports.update((composed["module"], preserved["module"]))
        if name in DECODER_COMPOSITION:
            composed = certificate["decoder_composition"]
            fields = {"module", "theorem"}
            if name in PRESERVATION_PREDICATES:
                fields.add("preservation")
            if set(composed) != fields or not all(
                NAME.fullmatch(composed[key]) for key in ("module", "theorem")
            ):
                raise ValueError(f"invalid decoder composition certificate for {name}")
            imports.add(composed["module"])
            if name in PRESERVATION_PREDICATES:
                preserved = composed["preservation"]
                if set(preserved) != {"module", "theorem"} or not all(
                    NAME.fullmatch(value) for value in preserved.values()
                ):
                    raise ValueError(
                        f"invalid decoder preservation certificate for {name}"
                    )
                imports.add(preserved["module"])
        if name in WRITER_COMPOSITION:
            composed = certificate["writer_composition"]
            fields = {"module", "theorem"}
            if name in PRESERVATION_PREDICATES:
                fields.add("preservation")
            if set(composed) != fields or not all(
                NAME.fullmatch(composed[key]) for key in ("module", "theorem")
            ):
                raise ValueError(f"invalid writer composition certificate for {name}")
            imports.add(composed["module"])
            if name in PRESERVATION_PREDICATES:
                preserved = composed["preservation"]
                if set(preserved) != {"module", "theorem"} or not all(
                    NAME.fullmatch(value) for value in preserved.values()
                ):
                    raise ValueError(
                        f"invalid writer preservation certificate for {name}"
                    )
                imports.add(preserved["module"])
        if name in KDF_COMPOSITION:
            composed = certificate["kdf_composition"]
            fields = {"module", "theorem"}
            if name in PRESERVATION_PREDICATES:
                fields.add("preservation")
            if set(composed) != fields or not all(
                NAME.fullmatch(composed[key]) for key in ("module", "theorem")
            ):
                raise ValueError(f"invalid KDF composition certificate for {name}")
            imports.add(composed["module"])
            if name in PRESERVATION_PREDICATES:
                preserved = composed["preservation"]
                if set(preserved) != {"module", "theorem"} or not all(
                    NAME.fullmatch(value) for value in preserved.values()
                ):
                    raise ValueError(f"invalid KDF preservation certificate for {name}")
                imports.add(preserved["module"])
    lines = [f"import {module}" for module in sorted(imports)]
    lines += [
        "import Lean.Util.CollectAxioms",
        "import Lean.Elab.Command",
        "import Lean.Elab.Tactic.ElabTerm",
        "import Lean.Meta.Tactic.Assumption",
        "",
        "/-! Generated by scripts/check_adapter_panic_freedom.py from the exact adapter signatures and closed external-contract registry. RustM.ok may contain ordinary rejection or dependency errors. -/",
        "",
        "open CoreModels Aeneas",
        "open Aeneas.Std hiding namespace core alloc",
        "open RustM",
        "set_option autoImplicit false",
        "set_option warningAsError true",
        "",
        "namespace BeaconcryptCore.PanicFreedom.AdapterCoverage",
        "",
        "-- Apply exactly the named certificate, then discharge only its premises from the local context.",
        'elab "adapter_certificate " certificate:term : tactic =>',
        "  Lean.Elab.Tactic.evalApplyLikeTactic (fun goal expression => do",
        "    let remaining ← goal.apply expression",
        "    for premise in remaining do premise.assumption",
        "    pure []) certificate",
        "",
    ]
    names = []
    number = 0
    for cohort, (namespace, instances, definitions) in parsed.items():
        lines += [f"section {cohort}", f"open {namespace}"]
        if definitions:
            lines += [
                f"open {opening}"
                for opening in next(iter(definitions.values())).openings
            ]
        instance_binders = []
        for instance in instances:
            for specification in re.findall(r"\[([^\]]+)\]", instance):
                if ":" in specification:
                    raise ValueError(
                        "review named extracted dictionary binder: " + specification
                    )
                instance_binders.append(
                    f"[_adapter_instance_{len(instance_binders):02d} : {specification}]"
                )
        lines += [""]
        for name, definition in sorted(definitions.items()):
            if not definition.monadic:
                lines += [f"-- Pure dictionary definition (no RustM execution): {name}"]
                continue
            if definition.role == "intentional-panic":
                lines += [
                    f"-- Intentional Result.expect panic; unconditional totality excluded: {name}"
                ]
                continue
            certificate = certificates[name]
            checked_name = f"operation_{number:03d}"
            names.append(checked_name)
            number += 1
            identifiers = set(
                re.findall(r"[A-Za-z_][A-Za-z_0-9]*", f"{name} {definition.binders}")
            )
            witness = "adapter_result"
            while witness in identifiers:
                witness += "_"
            lines += [
                f"-- {definition.role}: {name}",
                f"theorem {checked_name} {' '.join(instance_binders)} {definition.binders}",
            ]
            lines += [f"    {premise}" for premise in assumptions(cohort, definition)]
            lines += [
                f"    : ∃ {witness}, {name} {definition.arguments} = ok {witness} := by"
            ]
            if certificate["form"] == "exists":
                lines += [f"  adapter_certificate {certificate['theorem']}"]
            else:
                lines += [
                    f"  refine ⟨_, ?_⟩",
                    f"  adapter_certificate {certificate['theorem']}",
                ]
            lines += [""]
            if name in PRESERVATION_PREDICATES:
                preserved_name = checked_name + "_preserves"
                names.append(preserved_name)
                predicate = PRESERVATION_PREDICATES[name].format(result=witness)
                lines += [
                    f"-- The returned state supports the next public operation, including rejection paths.",
                    f"theorem {preserved_name} {' '.join(instance_binders)} {definition.binders}",
                ]
                lines += [
                    f"    {premise}"
                    for premise in preservation_assumptions(cohort, definition)
                ]
                lines += [
                    f"    : ∃ {witness}, {name} {definition.arguments} = ok {witness} ∧ ({predicate}) := by",
                    f"  adapter_certificate {certificate['preservation']['theorem']}",
                    "",
                ]
            if name in SOURCE_COMPOSITION:
                source = SOURCE_COMPOSITION[name]
                composed = certificate["source_composition"]
                for preserve in (False, True):
                    checked_source_name = (
                        checked_name + "_source" + ("_preserves" if preserve else "")
                    )
                    names.append(checked_source_name)
                    endpoint = composed["preservation"] if preserve else composed
                    lines += [
                        "-- Original public controller with source-selected children and no opaque seal/write normality premise.",
                        f"theorem {checked_source_name} {' '.join(instance_binders)} {definition.binders}",
                    ]
                    lines += [
                        f"    {premise}"
                        for premise in source_composition_assumptions(name, preserve)
                    ]
                    postcondition = (
                        " ∧ ("
                        + PRESERVATION_PREDICATES[name].format(result=witness)
                        + ")"
                        if preserve
                        else ""
                    )
                    lines += [
                        "    : letI := " + source + ".sourceLocalOperations "
                        "(inferInstance : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations) "
                        "_adapter_seal_fallback _adapter_writer_fallback",
                        f"      ∃ {witness}, {name} {definition.arguments} = ok {witness}{postcondition} := by",
                        f"  adapter_certificate {endpoint['theorem']}",
                        "",
                    ]
            if name in DECODER_COMPOSITION:
                composed = certificate["decoder_composition"]
                # The source-selected wrapper has no ambient opaque Codecs dictionary.
                decoder_instances = [
                    binder
                    for binder in instance_binders
                    if not binder.endswith("PublicWrapperPlatform.Codecs]")
                ]
                for preserve in (
                    (False, True) if name in PRESERVATION_PREDICATES else (False,)
                ):
                    checked_decoder_name = (
                        checked_name + "_decoders" + ("_preserves" if preserve else "")
                    )
                    names.append(checked_decoder_name)
                    endpoint = composed["preservation"] if preserve else composed
                    postcondition = (
                        " ∧ ("
                        + PRESERVATION_PREDICATES[name].format(result=witness)
                        + ")"
                        if preserve
                        else ""
                    )
                    lines += [
                        "-- Actual arbitrary-slice source decoders, including malformed-input rejection.",
                        f"theorem {checked_decoder_name} {' '.join(decoder_instances)} {definition.binders}",
                    ]
                    lines += [
                        f"    {premise}"
                        for premise in decoder_composition_assumptions(
                            definition, preserve
                        )
                    ]
                    lines += [
                        f"    : letI := {DECODER_SOURCE}.sourceCodecs",
                        f"      ∃ {witness}, {name} {definition.arguments} = ok {witness}{postcondition} := by",
                        f"  adapter_certificate {endpoint['theorem']}",
                        "",
                    ]
            if name in WRITER_COMPOSITION:
                composed = certificate["writer_composition"]
                writer_instances = [
                    binder
                    for binder in instance_binders
                    if not binder.endswith("RegistrationWriterPrimitive.Operations]")
                ]
                for preserve in (
                    (False, True) if name in PRESERVATION_PREDICATES else (False,)
                ):
                    checked_writer_name = (
                        checked_name + "_writers" + ("_preserves" if preserve else "")
                    )
                    names.append(checked_writer_name)
                    endpoint = composed["preservation"] if preserve else composed
                    postcondition = (
                        " ∧ ("
                        + PRESERVATION_PREDICATES[name].format(result=witness)
                        + ")"
                        if preserve
                        else ""
                    )
                    lines += [
                        "-- Actual serializers; signed public callers derive packet shape and native sizing derives room.",
                        f"theorem {checked_writer_name} {' '.join(writer_instances)} {definition.binders}",
                    ]
                    lines += [
                        f"    {premise}"
                        for premise in writer_composition_assumptions(
                            definition, preserve
                        )
                    ]
                    lines += [
                        f"    : letI := {WRITER_SELECTION}.sourceOperations _adapter_other"
                    ]
                    if WRITER_COMPOSITION[name] == "build":
                        lines += [
                            "      letI := BeaconcryptCore.PanicFreedom.AdapterPublicServerBuildSource.sourceLocalOperations "
                            "(inferInstance : BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations) "
                            "_adapter_seal_fallback _adapter_writer_fallback"
                        ]
                    lines += [
                        f"      ∃ {witness}, {name} {definition.arguments} = ok {witness}{postcondition} := by",
                        f"  adapter_certificate {endpoint['theorem']}",
                        "",
                    ]
            if name in KDF_COMPOSITION:
                composed = certificate["kdf_composition"]
                kind = KDF_COMPOSITION[name][0]
                replaced = {
                    "finish": "PublicWrapperPlatform.Codecs]",
                    "build": "RegistrationWriterPrimitive.Operations]",
                }.get(kind)
                kdf_instances = [
                    binder
                    for binder in instance_binders
                    if not replaced or not binder.endswith(replaced)
                ]
                for preserve in (
                    (False, True) if name in PRESERVATION_PREDICATES else (False,)
                ):
                    checked_kdf_name = (
                        checked_name + "_kdf" + ("_preserves" if preserve else "")
                    )
                    names.append(checked_kdf_name)
                    endpoint = composed["preservation"] if preserve else composed
                    postcondition = (
                        " ∧ ("
                        + PRESERVATION_PREDICATES[name].format(result=witness)
                        + ")"
                        if preserve
                        else ""
                    )
                    lines += [
                        "-- Actual ratchet KDF wrappers, using selected-width HKDF API contracts and reached borrow shape.",
                        f"theorem {checked_kdf_name} {' '.join(kdf_instances)} {definition.binders}",
                    ]
                    lines += [
                        f"    {premise}"
                        for premise in kdf_composition_assumptions(
                            definition, kdf_instances, preserve
                        )
                    ]
                    selections = kdf_selection(KDF_COMPOSITION[name][0])
                    lines += ["    : " + selections[0]] + [
                        "      " + selected for selected in selections[1:]
                    ]
                    lines += [
                        f"      ∃ {witness}, {name} {definition.arguments} = ok {witness}{postcondition} := by",
                        f"  adapter_certificate {endpoint['theorem']}",
                        "",
                    ]
        lines += [f"end {cohort}", ""]
    if set(certificates) & set(DECODER_COMPOSITION):
        for operation, field in (
            ("init", "decodeInit"),
            ("response", "decodeResponse"),
        ):
            checked = "source_decoder_" + operation
            names.append(checked)
            lines += [
                "-- Pin the selected dictionary to the original extracted decoder, not just a normally returning codec.",
                f"theorem {checked} [_adapter_validator : BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations] (input : Slice U8) :",
                f"    {DECODER_SOURCE}.sourceCodecs.{field} input = beaconcrypt_parse.extraction_decode_{operation} input := by",
                f"  adapter_certificate {DECODER_SOURCE}.source_{operation}",
                "",
            ]
    if set(certificates) & set(WRITER_COMPOSITION):
        for operation, packet in (("init", "initkex"), ("response", "kexresponse")):
            checked = "source_writer_" + operation
            names.append(checked)
            lines += [
                "-- Pin the selected serializer leaf to the original extraction on every input and buffer.",
                f"theorem {checked} (other : BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.OtherBranches)",
                f"    (packet : beaconcrypt_parse.transport.{packet}) (output : Slice U8) :",
                f"    @beaconcrypt_parse.encode_{operation} ({WRITER_SELECTION}.sourceOperations other) packet output =",
                f"      @beaconcrypt_parse.extraction_encode_{operation} (BeaconcryptCore.Refinement.RegistrationSerializerReachableSource.operations other) packet output := by",
                f"  adapter_certificate {WRITER_SELECTION}.runtime_{operation}_binding",
                "",
            ]
    if set(certificates) & set(KDF_COMPOSITION):
        for operation, dictionary, field, native in (
            (
                "send",
                "beaconcrypt_record_send.ratchet.Operations",
                "kdf",
                "ratchet_hkdf",
            ),
            ("receive", "beaconcrypt.ratchet.Operations", "kdf", "ratchet_hkdf"),
            (
                "initial",
                "BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations",
                "ratchet_initial_ratchet_hkdf",
                "initial_ratchet_hkdf",
            ),
        ):
            checked = "source_kdf_" + operation
            names.append(checked)
            selector = {
                "send": "sourceSendOperations",
                "receive": "sourceReceiveOperations",
                "initial": "sourceLocalOperations",
            }[operation]
            lines += [
                f"theorem {checked} [_adapter_material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]",
                "    [_adapter_platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]",
                "    [_adapter_primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]",
                "    [_adapter_crypto : BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]",
                "    [_adapter_hkdf : BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive.Operations]",
                f"    (previous : {dictionary}) (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) :",
                f"    ({KDF_SOURCE}.{selector} previous).{field} request =",
                f"      beaconcrypt_ratchet_kdf.ratchet.{native} request := by",
                f"  adapter_certificate {KDF_SOURCE}.source_{operation}_kdf",
                "",
            ]
    if additional_modules is not None:
        names.extend(REQUIRED_SOURCE_THEOREMS)
    lines += [
        "-- Inspect transitive dependencies of every exported contract, including imported libraries.",
        "run_cmd do",
        "  let allowed := [``propext, ``Classical.choice, ``Quot.sound]",
        "  let mut certificates := #[",
    ]
    lines += [
        f"      ``{name}{',' if index + 1 < len(names) else ''}"
        for index, name in enumerate(names)
    ]
    lines += [
        "    ]",
        "  for (declaration, information) in (← Lean.getEnv).constants.toList do",
        '    if declaration.toString.startsWith "BeaconcryptCore.PanicFreedom.Adapter" && information.isTheorem && !certificates.contains declaration then',
        "      certificates := certificates.push declaration",
        "  for declaration in certificates do",
        "    for dependency in ← Lean.collectAxioms declaration do",
        "      unless allowed.contains dependency do",
        '        throwError "adapter safety certificate {declaration} has unapproved dependency {dependency}"',
        "",
        "end BeaconcryptCore.PanicFreedom.AdapterCoverage",
        "",
    ]
    return "\n".join(lines)


def check_provenance(root: Path) -> None:
    """Retain every cohort's existing exact source and specialization gate."""
    for script in COHORTS.values():
        subprocess.run(
            [
                sys.executable,
                str(root / "scripts" / (script + ".py")),
                "--check-source",
            ],
            cwd=root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )


def lean_control_command(
    label: str,
    command: list[str],
    coordinator: Path = Path("/tmp/bc-coord/coord.sh"),
    environment: dict[str, str] | None = None,
) -> list[str]:
    """Coordinate when available without nesting an inherited lease or slot.

    The coordinator's inherited environment is trusted orchestration metadata,
    not an independently validated live lease. Dedicated runners without this
    optional local helper execute the identical controls directly.
    """
    inherited = os.environ if environment is None else environment
    if any(
        inherited.get(marker)
        for marker in ("COORD_LEASE_TICKET", "COORD_LEAN_SLOT", "COORD_LEAN_SLOT_LOCK")
    ):
        return command
    if not coordinator.exists() and not coordinator.is_symlink():
        return command
    if not coordinator.is_file() or not os.access(coordinator, os.X_OK):
        raise ValueError(f"Lean control coordinator is not executable: {coordinator}")
    return [str(coordinator), "lean", "codex", label, "--", *command]


def check_lean_controls(root: Path) -> None:
    """Compile positive, wrong-type, and transitive-dependency controls freshly.

    Run after the actual safety modules are built, under the pinned Lean environment.
    Each invocation uses local coordination when available, or its inherited lease/slot.
    Runners without the optional coordinator still compile every control.
    Deliberately invalid fixture sources live only in a temporary directory.
    """
    proof = root / "beaconcrypt-core/proofs/lean"
    namespace, instances, definitions = declarations(
        "namespace AdapterPanicFixture\n"
        "variable [beaconcrypt.auth.Operations]\n"
        "def work (value : Unit) : RustM Unit := ok value\n"
        "end AdapterPanicFixture\n"
    )
    parsed = {"AdapterAuthenticationExtraction": (namespace, instances, definitions)}
    certificate = {
        "AdapterPanicFixture.work": {
            "module": "AdapterPanicFixture",
            "theorem": "AdapterPanicFixture.certificate",
            "form": "exists",
        }
    }
    lean_path = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=proof, text=True
    ).strip()
    header = (
        "import BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication\n"
        "open CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM\n"
        "namespace AdapterPanicFixture\n"
        "def work (value : Unit) : RustM Unit := ok value\n"
    )
    variants = {
        "positive": "theorem certificate (value : Unit) : ∃ result, work value = ok result := ⟨value, rfl⟩\n",
        "wrong-type": "theorem certificate : True := True.intro\n",
        "transitive-axiom": (
            "axiom hidden : False\n"
            "theorem intermediate : False := hidden\n"
            "theorem certificate (value : Unit) : ∃ result, work value = ok result := False.elim intermediate\n"
        ),
        "extra-exported-axiom": (
            "theorem certificate (value : Unit) : ∃ result, work value = ok result := ⟨value, rfl⟩\n"
            "end AdapterPanicFixture\n"
            "namespace BeaconcryptCore.PanicFreedom.AdapterExtraControl\n"
            "axiom hidden : False\n"
            "theorem unrelated : True := False.elim hidden\n"
            "end BeaconcryptCore.PanicFreedom.AdapterExtraControl\n"
            "namespace AdapterPanicFixture\n"
        ),
    }
    for label, body in variants.items():
        with tempfile.TemporaryDirectory(
            prefix="beaconcrypt-adapter-safety-control-"
        ) as directory:
            temporary = Path(directory)
            fixture = temporary / "AdapterPanicFixture.lean"
            fixture.write_text(header + body + "end AdapterPanicFixture\n")
            generated = temporary / "AdapterPanicControl.lean"
            generated.write_text(render(parsed, certificate))
            prefix = lean_control_command(
                "adapter-safety-" + label,
                [
                    "lake",
                    "env",
                    "env",
                    "LEAN_PATH=" + str(temporary) + ":" + lean_path,
                    "lean",
                    "--root=" + str(temporary),
                ],
            )
            built = subprocess.run(
                prefix + ["-o", str(fixture.with_suffix(".olean")), str(fixture)],
                cwd=proof,
                text=True,
                capture_output=True,
            )
            if built.returncode:
                raise ValueError(
                    f"{label} fixture failed before its control:\n{built.stdout}{built.stderr}"
                )
            checked = subprocess.run(
                prefix + [str(generated)], cwd=proof, text=True, capture_output=True
            )
            output = checked.stdout + checked.stderr
            if label == "positive":
                if checked.returncode:
                    raise ValueError("positive safety control failed:\n" + output)
            elif label == "wrong-type":
                if not checked.returncode or not any(
                    message in output
                    for message in ("failed", "unify", "type mismatch")
                ):
                    raise ValueError(
                        "wrong certificate type was not rejected as expected:\n"
                        + output
                    )
            elif label == "extra-exported-axiom":
                if (
                    not checked.returncode
                    or "unapproved dependency BeaconcryptCore.PanicFreedom.AdapterExtraControl.hidden"
                    not in output
                ):
                    raise ValueError(
                        "extra exported safety certificate escaped dependency audit:\n"
                        + output
                    )
            elif (
                not checked.returncode
                or "unapproved dependency AdapterPanicFixture.hidden" not in output
            ):
                raise ValueError(
                    "transitive certificate dependency was not rejected:\n" + output
                )
            print(f"Compiled adapter safety control: {label} PASS")
    _, all_parsed = inventory(root)
    cohort = "AdapterPublicOrdinaryExtraction"
    namespace, instances, definitions = all_parsed[cohort]
    name = "beaconcrypt_public_ordinary.ratchet.encrypt_message_with_ratchet"
    total = "BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary.encrypt_message_with_ratchet_total"
    weaker = {
        name: {
            "module": "BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary",
            "theorem": total,
            "form": "exists",
            "preservation": {
                "module": "BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary",
                "theorem": total,
            },
        }
    }
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-adapter-preservation-control-"
    ) as directory:
        temporary = Path(directory)
        generated = temporary / "WeakenedPreservation.lean"
        generated.write_text(
            render({cohort: (namespace, instances, {name: definitions[name]})}, weaker)
        )
        checked = subprocess.run(
            lean_control_command(
                "adapter-weakened-preservation",
                ["lake", "env", "lean", "--root=" + str(temporary), str(generated)],
            ),
            cwd=proof,
            text=True,
            capture_output=True,
        )
        output = checked.stdout + checked.stderr
        if not checked.returncode or not any(
            message in output for message in ("failed", "unify", "type mismatch")
        ):
            raise ValueError(
                "plain totality was accepted as state preservation:\n" + output
            )
        print("Compiled adapter safety control: weakened-state-preservation PASS")

    # A component certificate that assumes opaque child normality must not stand
    # in for the source-selected public theorem with only reduced leaf laws.
    cohort = "AdapterPublicWrapperExtraction"
    namespace, instances, definitions = all_parsed[cohort]
    name = next(iter(SOURCE_COMPOSITION))
    certificates = json.loads((proof / "adapter-panic-freedom.json").read_text())
    component = certificates[name]
    component["source_composition"]["module"] = component["module"]
    component["source_composition"]["theorem"] = component["theorem"]
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-adapter-source-child-control-"
    ) as directory:
        temporary = Path(directory)
        generated = temporary / "OpaqueChildren.lean"
        generated.write_text(
            render(
                {cohort: (namespace, instances, {name: definitions[name]})},
                {name: component},
            )
        )
        checked = subprocess.run(
            lean_control_command(
                "adapter-opaque-child-contract",
                ["lake", "env", "lean", "--root=" + str(temporary), str(generated)],
            ),
            cwd=proof,
            text=True,
            capture_output=True,
        )
        output = checked.stdout + checked.stderr
        if not checked.returncode or not any(
            message in output for message in ("failed", "unify", "type mismatch")
        ):
            raise ValueError(
                "opaque-child component certificate was accepted as source composition:\n"
                + output
            )
        print("Compiled adapter safety control: opaque-child-discharge PASS")

    name = "beaconcrypt_public_wrapper.server.Server.authenticate_registration_lookup"
    component = json.loads((proof / "adapter-panic-freedom.json").read_text())[name]
    component["decoder_composition"] = {
        "module": component["module"],
        "theorem": component["theorem"],
    }
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-adapter-decoder-control-"
    ) as directory:
        temporary = Path(directory)
        generated = temporary / "OpaqueDecoder.lean"
        generated.write_text(
            render(
                {cohort: (namespace, instances, {name: definitions[name]})},
                {name: component},
            )
        )
        checked = subprocess.run(
            lean_control_command(
                "adapter-opaque-decoder-contract",
                ["lake", "env", "lean", "--root=" + str(temporary), str(generated)],
            ),
            cwd=proof,
            text=True,
            capture_output=True,
        )
        output = checked.stdout + checked.stderr
        if not checked.returncode or not any(
            message in output for message in ("failed", "unify", "type mismatch")
        ):
            raise ValueError(
                "opaque decoder certificate was accepted as source composition:\n"
                + output
            )
        print("Compiled adapter safety control: opaque-decoder-discharge PASS")

    cohort = "AdapterRegistrationWriterExtraction"
    namespace, instances, definitions = all_parsed[cohort]
    name = "beaconcrypt_registration_writer.wire.encode_init"
    component = json.loads((proof / "adapter-panic-freedom.json").read_text())[name]
    component["writer_composition"] = {
        "module": component["module"],
        "theorem": component["theorem"],
    }
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-adapter-writer-control-"
    ) as directory:
        temporary = Path(directory)
        generated = temporary / "OpaqueWriter.lean"
        generated.write_text(
            render(
                {cohort: (namespace, instances, {name: definitions[name]})},
                {name: component},
            )
        )
        checked = subprocess.run(
            lean_control_command(
                "adapter-opaque-writer-contract",
                ["lake", "env", "lean", "--root=" + str(temporary), str(generated)],
            ),
            cwd=proof,
            text=True,
            capture_output=True,
        )
        output = checked.stdout + checked.stderr
        if not checked.returncode or not any(
            message in output for message in ("failed", "unify", "type mismatch")
        ):
            raise ValueError(
                "opaque writer certificate was accepted as source composition:\n"
                + output
            )
        print("Compiled adapter safety control: opaque-writer-discharge PASS")

    cohort = "AdapterRecordExtraction"
    namespace, instances, definitions = all_parsed[cohort]
    name = "beaconcrypt.ratchet.execute_record_receive"
    component = json.loads((proof / "adapter-panic-freedom.json").read_text())[name]
    component["kdf_composition"] = {
        "module": component["module"],
        "theorem": component["theorem"],
    }
    with tempfile.TemporaryDirectory(
        prefix="beaconcrypt-adapter-kdf-control-"
    ) as directory:
        temporary = Path(directory)
        generated = temporary / "OpaqueKdf.lean"
        generated.write_text(
            render(
                {cohort: (namespace, instances, {name: definitions[name]})},
                {name: component},
            )
        )
        checked = subprocess.run(
            lean_control_command(
                "adapter-opaque-kdf-contract",
                ["lake", "env", "lean", "--root=" + str(temporary), str(generated)],
            ),
            cwd=proof,
            text=True,
            capture_output=True,
        )
        output = checked.stdout + checked.stderr
        if not checked.returncode or not any(
            message in output for message in ("failed", "unify", "type mismatch")
        ):
            raise ValueError(
                "opaque KDF certificate was accepted as source composition:\n" + output
            )
        print("Compiled adapter safety control: opaque-kdf-discharge PASS")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[1]
    )
    parser.add_argument("--write", action="store_true")
    parser.add_argument(
        "--inventory-only",
        action="store_true",
        help="audit the boundary without claiming certificate coverage",
    )
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--check-source", action="store_true")
    parser.add_argument("--check-lean-controls", action="store_true")
    args = parser.parse_args()
    if args.check_lean_controls:
        check_lean_controls(args.root)
        return 0
    if args.check_source:
        check_provenance(args.root)
    reviewed, parsed = inventory(args.root)
    if args.list:
        for cohort, (_, _, definitions) in parsed.items():
            for definition in definitions.values():
                print(f"{cohort}\t{definition.role}\t{definition.name}")
        return 0
    target = (
        args.root / "beaconcrypt-core/proofs/lean/adapter-panic-freedom-inventory.json"
    )
    expected = json.dumps(reviewed, indent=2, sort_keys=True) + "\n"
    if args.write:
        target.write_text(expected)
    elif not target.exists() or target.read_text() != expected:
        raise ValueError("adapter inventory drift; review and regenerate with --write")
    count = sum(len(definitions) for _, _, definitions in parsed.values())
    monadic = sum(d.monadic for _, _, ds in parsed.values() for d in ds.values())
    if not args.inventory_only:
        certificates = json.loads(
            (target.parent / "adapter-panic-freedom.json").read_text()
        )
        generated = render(parsed, certificates, safety_modules(args.root))
        target = target.parent / "BeaconcryptCore/PanicFreedom/AdapterCoverage.lean"
        if args.write:
            target.write_text(generated)
        elif not target.exists() or target.read_text() != generated:
            raise ValueError(
                "adapter signature-derived contracts differ; review and regenerate with --write"
            )
    label = (
        "boundary only"
        if args.inventory_only
        else "signature-derived certificates; Lean compilation required"
    )
    print(
        f"Checked {count} adapter definitions ({monadic} monadic) across {len(parsed)} feature-profiled cohorts ({label})."
    )
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        if isinstance(error, subprocess.CalledProcessError):
            print(error.stdout, file=sys.stderr)
        sys.exit(f"Adapter panic-freedom check failed: {error}")
