#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reproduce the selected public Rust wrappers and their agreement driver.

Production source is immutable. The isolated source preparation and LLBC branch
continuation distribution have checked control certificates; foreign primitive,
codec and platform implementations remain explicit maintained interfaces.
"""

from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tomllib
import extract_adapter_record as common
import prepare_adapter_public_wrappers as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterPublicWrapperExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
GENERATED = common.GENERATED
MODELS = (
    "TypesExternal.lean",
    "PlatformOperations.lean",
    "LocalOperations.lean",
    "FunsExternal.lean",
)
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
LINTERS = (
    "dupNamespace",
    "hashCommand",
    "unusedVariables",
    "style.whitespace",
    "style.setOption",
    "style.longLine",
)
POLICY = "set_option autoImplicit false\nset_option warningAsError true\n"
BASE_BINDERS = """variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
"""
FUN_BINDERS = """variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Codecs]
variable [beaconcrypt.ratchet.Operations]
variable [beaconcrypt.auth.Operations]
variable [BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]
variable [BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]
"""
CHARON_FLAGS = [
    "--include=beaconcrypt::beacon::_proof_beacon_init_ready",
    "--include=beaconcrypt::beacon::_::identity_pk",
    "--include=beaconcrypt::beacon::_::identity_sk",
    "--include=beaconcrypt::server::_::identity_pk",
    "--include=beaconcrypt::server::_::identity_sk",
    "--include=beaconcrypt::server::_::identity_key_kid",
    "--include=beaconcrypt::server::_::mldsa_public_key",
    "--include=beaconcrypt::server::_::authentication_pin",
    "--include=beaconcrypt::auth::server_pin",
    "--include=beaconcrypt::beacon::_::finish_registration::closure::_::call_once",
    "--include=beaconcrypt::server::_::build_registration_response::closure::_::call_once",
    "--include=beaconcrypt::ratchet::RatchetManager",
    "--include=beaconcrypt::ratchet::_::from_kernel",
    "--include=beaconcrypt::shared::EstablishedRemote",
    "--include=beaconcrypt::shared::_::from_peer",
    "--include=beaconcrypt::server::registration_response_len",
    "--include=beaconcrypt_core::transport::RegistrationApplication",
    "--include=beaconcrypt_core::pqxdh::ServerBinding",
    "--include=beaconcrypt_crypto::crypto_sign::KeyPair",
    "--include=beaconcrypt::server::Server",
    "--include=beaconcrypt::beacon::Beacon",
    "--include=beaconcrypt::server::ServerIdentity",
    "--include=core::option::Option",
    "--include=beaconcrypt_parse::transport::initkex",
    "--include=core::ops::control_flow::ControlFlow",
    "--include=beaconcrypt::server::RegistrationOutput",
    "--include=beaconcrypt_core::agreement::AgreementEffect",
    "--include=core::result::Result",
    "--include=beaconcrypt::pqxdh::RegistrationKeys",
    "--include=beaconcrypt::server::RegResponse",
    "--include=beaconcrypt_core::registration::SignedResponseView",
    "--include=beaconcrypt_parse::transport::kexresponse",
    "--include=hashbrown::map::Entry",
    "--include=beaconcrypt::beacon::BeaconState",
    "--include=beaconcrypt::beacon::RegistrationAuthentication",
    "--include=beaconcrypt_crypto::crypto_kx::KeyPair",
    "--include=beaconcrypt_crypto::crypto_kem::mlkem768::KeyPair",
    "--include=beaconcrypt_core::pqxdh::BeaconStartInputs",
    "--include=beaconcrypt_core::pqxdh::BeaconCoins",
    "--include=beaconcrypt_core::registration::InitView",
    "--include=beaconcrypt_core::authentication::InitFields",
    "--include=beaconcrypt_core::registration::BeaconInitialOpen",
    "--include=beaconcrypt::pqxdh::execute_agreement::closure",
    "--include=beaconcrypt_core::agreement::DhRequest",
    "--include=beaconcrypt_core::agreement::DhSecretRole",
    "--include=beaconcrypt_core::registration::Ed25519SigningRequest",
    "--include=beaconcrypt::pqxdh::NoEntropy",
    "--include=beaconcrypt_core::agreement::RootKdfRequest",
    "--include=beaconcrypt::shared::_::from_peer::closure::_::call_once",
    "--include=beaconcrypt::ratchet::RatchetKernelSlot",
    "--include=beaconcrypt::ratchet::_::new",
    "--include=beaconcrypt::shared::map_peer_ratchet",
    "--include={impl core::ops::function::FnOnce for {impl beaconcrypt::beacon::ProviderBeacon for "
    "beaconcrypt::beacon::Beacon}::finish_registration::closure}",
    "--include={impl core::ops::function::FnOnce for {impl beaconcrypt::server::ProviderServer for "
    "beaconcrypt::server::Server}::build_registration_response::closure}",
    "--include=beaconcrypt::pqxdh::execute_agreement",
    "--include=beaconcrypt::pqxdh::execute_beacon_agreement",
    "--include=beaconcrypt::pqxdh::execute_agreement::closure::_::call_once",
    "--start-from=beaconcrypt::server::_::authenticate_registration_lookup",
    "--start-from=beaconcrypt::server::_::get_shared_secret_from_lookup_with_rng",
    "--start-from={impl beaconcrypt::server::ProviderServer for "
    "beaconcrypt::server::Server}::build_registration_response",
    "--start-from=beaconcrypt::beacon::_::get_registration_bundle_with_rng",
    "--start-from={impl beaconcrypt::beacon::ProviderBeacon for "
    "beaconcrypt::beacon::Beacon}::finish_registration",
    "--include=beaconcrypt_crypto::crypto_kx::KeyPair",
    "--include=beaconcrypt_crypto::crypto_kem::mlkem768::KeyPair",
    "--include=beaconcrypt_core::pqxdh::BeaconStartInputs",
    "--include=beaconcrypt_core::pqxdh::BeaconCoins",
    "--include=beaconcrypt_core::registration::Ed25519SigningRequest",
    "--include=beaconcrypt_core::registration::InitView",
    "--include=beaconcrypt_core::authentication::InitFields",
    "--include=beaconcrypt::server::ServerIdentity",
    "--include={impl beaconcrypt::server::ProviderServer for "
    "beaconcrypt::server::Server}::build_registration_response::closure",
    "--include=beaconcrypt_core::registration::SignedResponseView",
    "--include=hashbrown::map::Entry",
    "--include={impl beaconcrypt::beacon::ProviderBeacon for "
    "beaconcrypt::beacon::Beacon}::finish_registration::closure",
    "--include=beaconcrypt_core::registration::BeaconInitialOpen",
    "--opaque=beaconcrypt",
    "--opaque=core",
    "--opaque=alloc",
    "--opaque=std",
    "--include=core::ops::control_flow::ControlFlow",
    "--include=core::option::Option",
    "--include=core::result::Result",
    "--include=core::convert::Infallible",
    "--include=beaconcrypt::server::Server",
    "--include=beaconcrypt::server::_::authenticate_registration_lookup",
    "--include=beaconcrypt::server::_::get_shared_secret_from_lookup_with_rng",
    "--include={impl beaconcrypt::server::ProviderServer for "
    "beaconcrypt::server::Server}::build_registration_response",
    "--include=beaconcrypt::beacon::_::get_registration_bundle_with_rng",
    "--include={impl beaconcrypt::beacon::ProviderBeacon for "
    "beaconcrypt::beacon::Beacon}::finish_registration",
    "--include=beaconcrypt::pqxdh::RegistrationKeys",
    "--include=beaconcrypt::beacon::RegistrationAuthentication",
    "--include=beaconcrypt_core::registration::BeaconInitEffect",
    "--include=beaconcrypt::beacon::Beacon",
    "--include=beaconcrypt::beacon::BeaconState",
    "--include=beaconcrypt::server::RegistrationOutput",
    "--include=beaconcrypt::server::RegResponse",
    "--include=beaconcrypt_core::agreement::AgreementEffect",
    "--include=beaconcrypt_core::registration::BeaconRegistrationEffect",
    "--opaque=beaconcrypt_core",
    "--opaque=beaconcrypt_parse",
    "--opaque=beaconcrypt_crypto",
    "--opaque=hashbrown",
    "--opaque=ml_dsa",
    "--opaque=serde",
    "--opaque=zeroize",
    "--opaque=siphasher",
    "--opaque=beaconcrypt::auth::authenticate_init",
    "--opaque=beaconcrypt::server::decode_init",
    "--include=beaconcrypt_parse::transport::initkex",
    "--include=beaconcrypt_parse::transport::kexresponse",
]
RAW_SHA256 = {
    "Types.lean": "e45665ee6898871ae5506e757eb9e88d95058010bb4a624662a9fb03560d5814",
    "Funs.lean": "eb29b84827855cb39823d42e5b7fb079b3f9b5c4f83b0a4b56a57de44c61bf34",
    "TypesExternal_Template.lean": "9d20f7f0ad6038ace8d9a8e9606fa518c7acf12ca665c2306824ecd6ade04098",
    "FunsExternal_Template.lean": "82ebd1df189df86f25f0631617a603c52f78f7c1d408e585d0dc53dd25f504b3",
}
ALPHA = {
    "Types.lean": [
        ["pqxdh.execute_agreement.closure_8", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_8",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_7", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_7",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_6", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_6",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_5", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_5",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_4", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_4",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_3", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_3",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        [
            "pqxdh.execute_agreement.closure_2",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure_1", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure_1",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
        ["pqxdh.execute_agreement.closure", "R", "_R"],
        [
            "pqxdh.execute_agreement.closure",
            "Clause0_Clause0_Error",
            "_Clause0_Clause0_Error",
        ],
    ],
    "Funs.lean": [
        [
            "pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once",
            "c",
            "_c",
        ],
        [
            "pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once",
            "c",
            "_c",
        ],
        [
            "pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        [
            "pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once",
            "rand_coreTryCryptoRngInst",
            "_rand_coreTryCryptoRngInst",
        ],
        ["shared.EstablishedRemote.from_peer", "SignaturePkInst", "_SignaturePkInst"],
    ],
}
INTERFACES = (
    (
        "core.option.Option.take core.option.Option.None",
        "core.option.Option.take (core.option.Option.None : core.option.Option beaconcrypt_crypto.crypto_kx.KeyPair)",
    ),
    (
        "beaconcrypt_core.session.SessionBinding.assigned_key_id binding",
        "BeaconcryptCore.Refinement.PublicWrapperPlatform.assignedKeyId binding",
    ),
    (
        "beaconcrypt_core.session.SessionBinding.beacon_identity_public_key\n                                    sb",
        "BeaconcryptCore.Refinement.PublicWrapperPlatform.beaconIdentity\n                                  sb",
    ),
    (
        "beaconcrypt_core.peer.Peer.binding peer",
        "BeaconcryptCore.Refinement.PublicWrapperPlatform.peerBinding peer",
    ),
)
SUPPORT = (
    "Cargo.toml",
    "Cargo.lock",
    "hax.toml",
    "scripts/extract_adapter_public_wrappers.py",
    "scripts/prepare_adapter_public_wrappers.py",
    "scripts/registration_codec_normalization.py",
    "scripts/extract_adapter_record.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterPublicControlNormalization.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/RegistrationPrimitiveExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterInitAuthenticationExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterInitAuthenticationExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterInitAuthenticationExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterInitAuthenticationExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterAuthenticationExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterAuthenticationExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterAuthenticationExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterAuthenticationExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRegistrationWriterExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRegistrationWriterExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRegistrationWriterExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRegistrationWriterExtraction/FunsExternal.lean",
)


# Refreshed after the security-review fixes added adapter types: the certificate equals its
# predecessor up to a monotone bijective renumbering of 350 interned type ids.
CONTROL_SHA256 = "3df9e741f9041ee3c141a5fffa474c352bdac3c1575818e9e2a44dcf6a23b564"


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def fragment_range(text: str, name: str) -> tuple[int, int]:
    declarations = list(re.finditer(r"^def\s+([A-Za-z0-9_.]+)", text, re.M))
    selected = [
        (index, match) for index, match in enumerate(declarations) if match[1] == name
    ]
    if len(selected) != 1:
        raise ValueError("generated declaration changed: " + name)
    index, match = selected[0]
    return match.start(), (
        declarations[index + 1].start() if index + 1 < len(declarations) else len(text)
    )


def alpha_rewrite(text: str, name: str, *, reverse: bool = False) -> str:
    for declaration, before, after in ALPHA[name]:
        if reverse:
            before, after = after, before
        start, end = fragment_range(text, declaration)
        fragment = text[start:end]
        code = common.lean_code_without_comments_or_strings(fragment.encode())
        if len(re.findall(r"\b" + re.escape(before) + r"\b", code)) != 1:
            raise ValueError(
                "unused-binder alpha roster changed: " + declaration + ":" + before
            )
        if not re.search(r"[({]" + re.escape(before) + r"\s*:", code):
            raise ValueError("alpha change is not an unused binder")
        changed = re.sub(r"\b" + re.escape(before) + r"\b", after, fragment)
        text = text[:start] + changed + text[end:]
    return text


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed generated public-wrapper body: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("generated namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    binders = BASE_BINDERS + (FUN_BINDERS if name == "Funs.lean" else "")
    text = text.replace(
        "namespace beaconcrypt\n", "namespace beaconcrypt_public_wrapper\n" + binders, 1
    )
    if text.count("end beaconcrypt\n") != 1:
        raise ValueError("generated namespace end changed")
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_public_wrapper\n", 1)
    text = alpha_rewrite(text, name)
    if name == "Funs.lean":
        for before, after in INTERFACES:
            if text.count(before) != 1 or after in text:
                raise ValueError("pure accessor/type interface changed")
            text = text.replace(before, after, 1)
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def denormalize(contents: bytes, name: str) -> bytes:
    common.require_handwritten_warning_policy(contents, name)
    text = contents.decode()
    if name == "Funs.lean":
        for before, after in reversed(INTERFACES):
            if text.count(after) != 1:
                raise ValueError("installed pure accessor/type interface changed")
            text = text.replace(after, before, 1)
    text = alpha_rewrite(text, name, reverse=True)
    binders = BASE_BINDERS + (FUN_BINDERS if name == "Funs.lean" else "")
    if text.count("namespace beaconcrypt_public_wrapper\n" + binders) != 1:
        raise ValueError("installed public-wrapper binder changed")
    text = text.replace(
        "namespace beaconcrypt_public_wrapper\n" + binders, "namespace beaconcrypt\n", 1
    )
    text = text.replace("end beaconcrypt_public_wrapper\n", "end beaconcrypt\n", 1)
    if text.count("open Std.Do\n" + POLICY) != 1:
        raise ValueError("installed strict warning policy changed")
    text = text.replace(
        "open Std.Do\n" + POLICY,
        "open Std.Do\n"
        + "".join("set_option linter." + item + " false\n" for item in LINTERS),
        1,
    )
    raw = text.encode()
    if normalize(raw, name) != contents:
        raise ValueError("public-wrapper normalization does not round trip")
    return raw


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    names = set(SUPPORT)
    if (root / "rust-toolchain.toml").exists():
        names.add("rust-toolchain.toml")
    for member in preparation.MEMBERS:
        for name in ("Cargo.toml", "build.rs"):
            if (root / member / name).exists():
                names.add(member + "/" + name)
        names.update(
            path.relative_to(root).as_posix()
            for path in (root / member / "src").rglob("*")
            if path.is_file()
        )
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in sorted(names)
        },
        "model_sha256": {
            name: digest((destination / name).read_bytes()) for name in MODELS
        },
    }


def metadata() -> dict:
    return {
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "charon_flags": CHARON_FLAGS,
        "charon_sysroot": "default",
        "rustflags": common.RUSTFLAGS,
        "control_sha256": CONTROL_SHA256,
        "normalization": {
            "strict_warning_header": list(LINTERS),
            "namespace": ["beaconcrypt", "beaconcrypt_public_wrapper"],
            "type_binders": BASE_BINDERS,
            "function_binders": FUN_BINDERS,
            "unused_binder_alpha": ALPHA,
            "interfaces": [list(rule) for rule in INTERFACES],
            "source_changes": list(preparation.RUST_CHANGED),
            "control_laws": [
                "branch_tail",
                "terminal_tail",
                "loop_congr",
                "init_loop_factor",
                "dh_selectionM",
            ],
        },
    }


def templates(generated: Path) -> dict:
    result = {}
    for name in ("TypesExternal_Template.lean", "FunsExternal_Template.lean"):
        raw = (generated / name).read_bytes()
        if digest(raw) != RAW_SHA256[name]:
            raise ValueError("unreviewed public external signature: " + name)
        result[name] = {"sha256": digest(raw), "source": raw.decode()}
    return result


def control_summary(certificate: dict) -> dict:
    return {
        "laws": certificate["laws"],
        "functions": certificate["functions"],
        "refreshed_labels": certificate["refreshed_labels"],
        "distributions": [
            {
                "function": row["function"],
                "switch": row["switch"],
                "branches": row["branches"],
                "tail_sha256": digest(json.dumps(row["tail"], sort_keys=True).encode()),
            }
            for row in certificate["distributions"]
        ],
        "terminal_tails": [
            {
                "function": row["function"],
                "exit": row["exit"],
                "discarded_sha256": digest(
                    json.dumps(row["discarded"], sort_keys=True).encode()
                ),
            }
            for row in certificate["terminal_tails"]
        ],
    }


def run(command: list[str], environment: dict[str, str], log: Path, cwd: Path) -> None:
    with log.open("w") as output:
        process = subprocess.Popen(
            command,
            cwd=cwd,
            env=environment,
            stdout=output,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            status = process.wait(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise RuntimeError("public-wrapper extraction timeout: " + str(log))
    if status:
        raise RuntimeError("public-wrapper extraction failed: " + str(log))


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    provenance = json.loads((destination / "provenance.json").read_bytes())
    expected = (
        set(metadata())
        | set(snapshot(root, destination))
        | {"tool_sha256", "raw_generated_sha256", "installed_sha256"}
    )
    if set(provenance) != expected:
        raise ValueError("public-wrapper provenance roster changed")
    for name, value in {**metadata(), **snapshot(root, destination)}.items():
        if provenance[name] != value:
            raise ValueError("public-wrapper source/model/metadata drift: " + name)
    common.require_hash_roster(
        provenance["tool_sha256"], set(PINNED_TOOLS), "tool_sha256"
    )
    if provenance["raw_generated_sha256"] != RAW_SHA256:
        raise ValueError("public-wrapper raw generated roster changed")
    installed = common.require_hash_roster(
        provenance["installed_sha256"], set(INSTALLED), "installed_sha256"
    )
    for name in INSTALLED:
        contents = (destination / name).read_bytes()
        if digest(contents) != installed[name]:
            raise ValueError("public-wrapper installed module drift: " + name)
        if name.endswith(".lean"):
            denormalize(contents, name)
    for name in MODELS:
        common.require_model((destination / name).read_bytes(), name)
        common.require_handwritten_warning_policy(
            (destination / name).read_bytes(), name
        )
    evidence = json.loads((destination / "external-signatures.json").read_bytes())
    if set(evidence) != {"templates", "source_preparation", "control_preparation"}:
        raise ValueError("public-wrapper external/control evidence roster changed")
    if set(evidence["templates"]) != {
        "TypesExternal_Template.lean",
        "FunsExternal_Template.lean",
    }:
        raise ValueError("public-wrapper external template roster changed")
    if (
        digest(json.dumps(evidence["control_preparation"], sort_keys=True).encode())
        != CONTROL_SHA256
    ):
        raise ValueError("public-wrapper control normalization certificate drift")
    for name, row in evidence["templates"].items():
        if (
            set(row) != {"sha256", "source"}
            or row["sha256"] != RAW_SHA256[name]
            or digest(row["source"].encode()) != RAW_SHA256[name]
        ):
            raise ValueError("public-wrapper external signature evidence drift")
    if set(evidence["source_preparation"]) != {"source_changes", "unchanged_sha256"}:
        raise ValueError("public-wrapper source preparation evidence roster changed")
    source = evidence["source_preparation"]["source_changes"]
    if set(source) != set(preparation.RUST_CHANGED):
        raise ValueError("public-wrapper source change roster changed")
    for name, prepare in zip(
        preparation.RUST_CHANGED,
        (preparation.factor_beacon, preparation.distribute_dh),
        strict=True,
    ):
        original = (root / name).read_text()
        prepared, certificate = prepare(original)
        expected = {
            **certificate,
            "source_sha256": digest(original.encode()),
            "prepared_sha256": digest(prepared.encode()),
        }
        if source.get(name) != expected:
            raise ValueError("public-wrapper source control certificate drift")
    immutable = {
        name
        for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml")
        if (root / name).exists()
    }
    for member in preparation.MEMBERS:
        immutable.update(
            member + "/" + name
            for name in ("Cargo.toml", "build.rs")
            if (root / member / name).exists()
        )
        immutable.update(
            path.relative_to(root).as_posix()
            for path in (root / member / "src").rglob("*")
            if path.is_file()
        )
    immutable.difference_update(preparation.RUST_CHANGED)
    if set(evidence["source_preparation"]["unchanged_sha256"]) != immutable:
        raise ValueError("public-wrapper immutable fixture evidence roster changed")
    for name, sha in evidence["source_preparation"]["unchanged_sha256"].items():
        if digest((root / name).read_bytes()) != sha:
            raise ValueError("public-wrapper immutable fixture input drift")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-source", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--review-external-signatures", action="store_true")
    parser.add_argument(
        "--tools-root",
        type=Path,
        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
        / "hax/tools",
    )
    args = parser.parse_args()
    if args.review_external_signatures and not args.write:
        parser.error("--review-external-signatures requires --write")
    if args.check_source:
        check_source()
        print(
            "Source public wrappers, control certificates and explicit interfaces match"
        )
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required for fresh extraction")
    work = common.isolated_work_directory(args.work_dir)
    common.validate_work_paths(work)
    common.validate_configuration(tomllib.loads((ROOT / "hax.toml").read_text()))
    before = snapshot()
    tools = {
        name: args.tools_root / name / version / name
        for name, version in PINNED_TOOLS.items()
    }
    tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
    work.mkdir(parents=True, exist_ok=True)
    fixture = work / "source"
    if fixture.exists():
        raise ValueError(
            "fresh wrapper work directory must have no prior source fixture"
        )
    source_certificate = preparation.prepare_source(ROOT, fixture)
    environment = common.extraction_environment(work)
    command = [
        str(tools["charon"]),
        "cargo",
        "--preset=aeneas",
        "--sysroot=default",
        *CHARON_FLAGS,
        "--dest-file",
        str(work / "original.llbc"),
        "--",
        "-p",
        "beaconcrypt",
        "--lib",
        "--locked",
        "--no-default-features",
        "--features=beacon,server,pqxdh",
    ]
    run(command, environment, work / "charon.log", fixture)
    original = json.loads((work / "original.llbc").read_bytes())
    if original["has_errors"]:
        raise ValueError("Charon reported an incomplete public source extraction")
    prepared, certificate = preparation.prepare_llbc(original)
    preparation.check_llbc(original, prepared, certificate)
    (work / "beaconcrypt.llbc").write_text(json.dumps(prepared))
    (work / "control-certificate.json").write_text(json.dumps(certificate, indent=2))
    command = [
        str(tools["aeneas"]),
        "-backend",
        "lean",
        "-core-models-lib",
        "-split-files",
        "-specs",
        "hax",
        "-no-progress-bar",
        "-sequential",
        "-abort-on-error",
        str(work / "beaconcrypt.llbc"),
        "-dest",
        str(work / "generated"),
        "-subdir",
        SUBDIRECTORY,
    ]
    run(command, environment, work / "aeneas.log", fixture)
    generated = work / "generated" / SUBDIRECTORY
    if (
        digest(json.dumps(control_summary(certificate), sort_keys=True).encode())
        != CONTROL_SHA256
    ):
        raise ValueError("fresh public-wrapper control certificate changed")
    evidence = {
        "templates": templates(generated),
        "source_preparation": source_certificate,
        "control_preparation": control_summary(certificate),
    }
    contents = {
        name: normalize((generated / name).read_bytes(), name)
        for name in ("Types.lean", "Funs.lean")
    }
    contents["external-signatures.json"] = (
        json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    ).encode()
    baseline = DESTINATION / "external-signatures.json"
    common.require_reviewed_signatures(
        contents["external-signatures.json"],
        baseline.read_bytes() if baseline.exists() else None,
        write=args.write,
        review=args.review_external_signatures,
    )
    if before != snapshot() or tool_hashes != {
        name: digest(path.read_bytes()) for name, path in tools.items()
    }:
        raise ValueError("public-wrapper extraction inputs changed during extraction")
    provenance = {
        **metadata(),
        **before,
        "tool_sha256": tool_hashes,
        "raw_generated_sha256": {
            name: digest((generated / name).read_bytes()) for name in GENERATED
        },
        "installed_sha256": {name: digest(value) for name, value in contents.items()},
    }
    contents["provenance.json"] = (
        json.dumps(provenance, indent=2, sort_keys=True) + "\n"
    ).encode()
    if args.write:
        for name, value in contents.items():
            (DESTINATION / name).write_bytes(value)
    else:
        changed = [
            name
            for name, value in contents.items()
            if (DESTINATION / name).read_bytes() != value
        ]
        if changed:
            raise ValueError(
                "public-wrapper fresh extraction drift: " + ", ".join(changed)
            )
    print(
        "Wrote reviewed public source cohort and evidence"
        if args.write
        else "Public source fresh extraction and evidence match"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
