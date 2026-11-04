#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract actual ordinary SDK ownership, admission and four public route bodies."""

from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import extract_adapter_record as common
import extract_adapter_public_server_entry as entry
import extract_adapter_public_wrappers as wrappers
import prepare_adapter_public_ordinary as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterPublicOrdinaryExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
RAW_SHA256 = {
    "Funs.lean": "7f1c2bd8963d6edae7dedeef11d072669e045168b9e0df0db42cab09dbff98e6",
    "FunsExternal_Template.lean": "8f37d17c4edb9bf4494f15f1036088ca54e9f9f82a09c81a923d454701fdb76b",
    "Types.lean": "b049d04c578ad32319e4d119bf54aa27111185e26c11f2ba7dbbb83ef829e440",
    "TypesExternal_Template.lean": "ecee449db44f5ccb0373c2da8d051c62d8e9fdaa5ac15a4fcc81fe668e99c83b",
}
SELECTION = {
    "opaque": [
        "beaconcrypt",
        "beaconcrypt_core",
        "beaconcrypt_crypto",
        "beaconcrypt_parse",
        "core",
        "alloc",
        "std",
        "rand_core",
        "hashbrown",
        "siphasher",
    ],
    "includes": [
        "core::option::Option",
        "core::result::Result",
        "core::ops::control_flow::ControlFlow",
        "core::convert::Infallible",
        "beaconcrypt::ratchet::RatchetKernelSlot",
        "beaconcrypt::ratchet::RatchetManager",
        "beaconcrypt::ratchet::RatchetStatus",
        "beaconcrypt::ratchet::CryptoFrame",
        "beaconcrypt::beacon::Beacon",
        "beaconcrypt::beacon::BeaconState",
        "beaconcrypt::beacon::RegistrationAuthentication",
        "beaconcrypt::server::Server",
        "beaconcrypt::server::ServerIdentity",
        "beaconcrypt::shared::EstablishedRemote",
        "beaconcrypt::shared::Encrypted",
        "beaconcrypt::shared::Decrypted",
        "beaconcrypt::server::ReceiveTransition",
        "beaconcrypt_crypto::crypto_sign::KeyPair",
        "beaconcrypt_crypto::crypto_kx::KeyPair",
        "beaconcrypt_crypto::crypto_kem::mlkem768::KeyPair",
        "beaconcrypt_core::record_effects::RecordEncoding",
        "beaconcrypt_parse::frame::Frame",
        "beaconcrypt_core::transport::FrameView",
        "beaconcrypt::ratchet::{impl core::ops::deref::Deref for _}::deref",
        "beaconcrypt::ratchet::{impl core::ops::deref::DerefMut for _}::deref_mut",
    ],
    "roots": [
        "beaconcrypt::ratchet::_::take",
        "beaconcrypt::ratchet::_::put",
        "beaconcrypt::ratchet::_::status",
        "beaconcrypt::ratchet::_::send_sequence",
        "beaconcrypt::ratchet::encrypt_with_ratchet",
        "beaconcrypt::ratchet::encrypt_message_with_ratchet",
        "beaconcrypt::ratchet::decrypt_payload_with_ratchet",
        "beaconcrypt::ratchet::decrypt_message_with_ratchet",
        "beaconcrypt::ratchet::decode_crypto_frame",
        "beaconcrypt::ratchet::encrypted_frame_sender",
        "beaconcrypt::wire::frame_len",
        "beaconcrypt::beacon::_::encrypt_message",
        "beaconcrypt::beacon::_::decrypt_message",
        "beaconcrypt::server::_::encrypt_message",
        "beaconcrypt::server::_::decrypt_message",
        "beaconcrypt::server::_::decrypt_message_transition",
        "beaconcrypt::server::_::associated_data",
        "beaconcrypt::server::_::ratchet_manager_mut",
        "beaconcrypt::shared::_::ratchet_mut",
        "beaconcrypt::shared::_::binding",
        "beaconcrypt::server::_::identity_key_kid",
        "beaconcrypt::server::_::into_option",
    ],
}
FLAGS = (
    ["--opaque=" + name for name in SELECTION["opaque"]]
    + ["--include=" + name for name in SELECTION["includes"] + SELECTION["roots"]]
    + ["--start-from=" + name for name in SELECTION["roots"]]
)
MODEL_SHA256 = {
    "TypesExternal.lean": "c321c9f323f93e9b9caa148b4b33d74018eec323477cf14aa068f8f2fde460fa",
    "FunsExternal.lean": "bfa79db313b9f954ed6acfca483583029f2e4b5b3e36736aaf2c7953bce129ee",
}
DEPENDENCIES = (
    "scripts/extract_adapter_public_ordinary.py",
    "scripts/prepare_adapter_public_ordinary.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterPublicOrdinaryString.lean",
    "scripts/lift_adapter_public_ordinary_requests.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterPublicOrdinaryBorrow.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordSendExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/FrameCodecExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Funs.lean",
)
BINDERS = wrappers.BASE_BINDERS
FUN_BINDERS = """variable [beaconcrypt_record_send.ratchet.Operations]
variable [beaconcrypt.ratchet.Operations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Allocator]
variable [BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.LookupOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.LocalOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.ContainerOperations]
"""
SHARED = {
    "beacon.RegistrationAuthentication": "AdapterPublicWrapperExtraction/Types.lean",
    "ratchet.RatchetKernelSlot": "AdapterPublicWrapperExtraction/Types.lean",
    "ratchet.RatchetManager": "AdapterPublicWrapperExtraction/Types.lean",
    "beacon.BeaconState": "AdapterPublicWrapperExtraction/Types.lean",
    "beacon.Beacon": "AdapterPublicWrapperExtraction/Types.lean",
    "shared.SignaturePk": "AdapterPublicWrapperExtraction/Types.lean",
    "server.ServerIdentity": "AdapterPublicWrapperExtraction/Types.lean",
    "shared.EstablishedRemote": "AdapterPublicWrapperExtraction/Types.lean",
    "server.Server": "AdapterPublicWrapperExtraction/Types.lean",
    "shared.Encrypted": "AdapterRecordSendExtraction/Types.lean",
    "shared.Decrypted": "AdapterRecordExtraction/Types.lean",
}


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def block(text: str, declaration: str) -> str:
    matches = []
    for part in re.findall(
        r"/--[\s\S]*?(?=/--|end beaconcrypt(?:_record_send|_public_wrapper)?\n|\Z)",
        text,
    ):
        if re.search(
            r"^(?:structure|inductive) " + re.escape(declaration) + r"(?=\s|$)",
            part,
            re.M,
        ):
            matches.append(part)
    if len(matches) != 1:
        raise ValueError("ordinary shared declaration boundary changed: " + declaration)
    return matches[0]


def shared_blocks(raw: bytes) -> tuple[str, dict]:
    text = raw.decode()
    receipts = {}
    for declaration, filename in SHARED.items():
        original = block(text, declaration)
        shared = block(
            (
                ROOT / "beaconcrypt-core/proofs/lean/BeaconcryptCore" / filename
            ).read_text(),
            declaration,
        )
        if original != shared:
            raise ValueError("ordinary concrete shared layout differs: " + declaration)
        receipts[declaration] = {"file": filename, "sha256": digest(original.encode())}
        text = text.replace(original, "", 1)
    return text, receipts


def normalize(raw: bytes, name: str) -> bytes:
    if digest(raw) != RAW_SHA256[name] or name not in ("Types.lean", "Funs.lean"):
        raise ValueError("unreviewed ordinary extracted source body")
    text = shared_blocks(raw)[0] if name == "Types.lean" else raw.decode()
    if (
        tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M))
        != wrappers.LINTERS
    ):
        raise ValueError("ordinary generated warning policy changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    text = text.replace("open Std.Do\n", "open Std.Do\n" + wrappers.POLICY, 1)
    binders = BINDERS + (FUN_BINDERS if name == "Funs.lean" else "")
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_public_ordinary\nopen beaconcrypt_public_wrapper\n"
        + binders,
        1,
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_public_ordinary\n", 1)
    if name == "Types.lean":
        text = text.replace(
            "end beaconcrypt_public_ordinary",
            "abbrev shared.Encrypted := beaconcrypt_record_send.shared.Encrypted\nabbrev shared.Decrypted := beaconcrypt.shared.Decrypted\nend beaconcrypt_public_ordinary",
            1,
        )
    else:
        if text.count("(SignaturePkInst :") != 2 or text.count("fun o1 =>") != 2:
            raise ValueError("ordinary unused binder roster changed")
        text = text.replace("(SignaturePkInst :", "(_SignaturePkInst :")
        text = text.replace("fun o1 =>", "fun _o1 =>", 1)
    if name == "Funs.lean":
        text = text.replace(
            "import Aeneas\n",
            "import Aeneas\nimport BeaconcryptCore.Refinement.AdapterPublicOrdinaryString\n",
            1,
        )
        literal = (
            '"a ratchet kernel is absent only while its synchronous effect is running")'
        )
        if text.count(literal) != 2:
            raise ValueError("ordinary unchanged panic literal boundary changed")
        text = text.replace(
            literal,
            literal[:-1]
            + " BeaconcryptCore.Refinement.AdapterPublicOrdinaryString.slot_bound)",
        )
        for before, after, count in (
            (
                "beaconcrypt_core.session.SessionBinding.associated_data",
                "BeaconcryptCore.Refinement.AdapterPublicOrdinaryPlatform.associatedData",
                3,
            ),
            (
                "beaconcrypt_core.peer.Peer.binding self.peer",
                "BeaconcryptCore.Refinement.PublicWrapperPlatform.peerBinding self.peer",
                1,
            ),
        ):
            if text.count(before) != count:
                raise ValueError("ordinary pure accessor interface changed: " + before)
            text = text.replace(before, after)
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def require_roots(raw: bytes) -> None:
    text = raw.decode()
    for declaration in (
        "ratchet.RatchetKernelSlot.take",
        "ratchet.RatchetKernelSlot.put",
        "ratchet.encrypt_with_ratchet",
        "ratchet.decrypt_payload_with_ratchet",
        "ratchet.decrypt_message_with_ratchet",
        "beacon.Beacon.encrypt_message",
        "beacon.Beacon.decrypt_message",
        "server.Server.encrypt_message",
        "server.Server.decrypt_message",
        "server.Server.ratchet_manager_mut",
    ):
        if (
            len(
                re.findall(
                    r"^def\s+" + re.escape(declaration) + r"(?=\s|$)", text, re.M
                )
            )
            != 1
        ):
            raise ValueError("ordinary selected body missing: " + declaration)
    common.require_model(raw, "ordinary selected bodies")


def contents(raw: dict[str, bytes]) -> dict[str, bytes]:
    if {name: digest(value) for name, value in raw.items()} != RAW_SHA256:
        raise ValueError("ordinary raw extraction roster/hash changed")
    require_roots(raw["Funs.lean"])
    for name, expected in MODEL_SHA256.items():
        model = (DESTINATION / name).read_bytes()
        if digest(model) != expected:
            raise ValueError("unreviewed ordinary external model: " + name)
        common.require_model(model, name)
    evidence = {
        "raw": {name: value.decode() for name, value in raw.items()},
        "source_preparation": preparation.certificate(ROOT),
        "shared_types": shared_blocks(raw["Types.lean"])[1],
        "tool_sha256": entry.TOOL_SHA256,
        "selection": SELECTION,
        "model_sha256": MODEL_SHA256,
        "dependency_sha256": {
            name: digest((ROOT / name).read_bytes()) for name in DEPENDENCIES
        },
    }
    result = {name: normalize(raw[name], name) for name in ("Types.lean", "Funs.lean")}
    result["source-evidence.json"] = (
        json.dumps(evidence, indent=2, sort_keys=True) + "\n"
    ).encode()
    return result


def check_source() -> None:
    evidence = json.loads((DESTINATION / "source-evidence.json").read_text())
    expected = contents(
        {name: value.encode() for name, value in evidence["raw"].items()}
    )
    for name, value in expected.items():
        if (DESTINATION / name).read_bytes() != value:
            raise ValueError("ordinary installed source differs: " + name)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-source", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--review-external-signatures", action="store_true")
    parser.add_argument(
        "--tools-root", type=Path, default=Path.home() / ".cache/hax/tools"
    )
    args = parser.parse_args()
    if args.check_source:
        check_source()
        print("ordinary SDK source bodies, layouts and exact preparation match")
        return 0
    if args.work_dir is None or (args.write and not args.review_external_signatures):
        parser.error(
            "fresh extraction needs --work-dir; writing also requires --review-external-signatures"
        )
    work = common.isolated_work_directory(args.work_dir)
    work.mkdir(parents=True, exist_ok=True)
    proof = preparation.prepare(ROOT, work / "source")
    tools = {
        name: args.tools_root / name / version / name
        for name, version in common.PINNED_TOOLS.items()
    }
    if {
        name: digest(path.read_bytes()) for name, path in tools.items()
    } != entry.TOOL_SHA256:
        raise ValueError("ordinary extraction tools differ from reviewed pins")
    commands = (
        [
            str(tools["charon"]),
            "cargo",
            "--preset=aeneas",
            "--sysroot=default",
            *FLAGS,
            "--dest-file",
            str(work / "beaconcrypt.llbc"),
            "--",
            "-p",
            "beaconcrypt",
            "--lib",
            "--locked",
            "--no-default-features",
            "--features=beacon,server,pqxdh",
        ],
        [
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
        ],
    )
    (work / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    environment = common.extraction_environment(work)
    for name, command in zip(("charon", "aeneas"), commands, strict=True):
        wrappers.run(command, environment, work / (name + ".log"), work / "source")
        if (
            name == "charon"
            and json.loads((work / "beaconcrypt.llbc").read_bytes())["has_errors"]
        ):
            raise ValueError("ordinary Charon extraction incomplete")
    preparation.verify(ROOT, work / "source", proof)
    raw = {
        name: (work / "generated" / SUBDIRECTORY / name).read_bytes()
        for name in RAW_SHA256
    }
    expected = contents(raw)
    if args.write:
        DESTINATION.mkdir(parents=True, exist_ok=True)
        for name, value in expected.items():
            (DESTINATION / name).write_bytes(value)
    else:
        check_source()
        for name, value in expected.items():
            if (DESTINATION / name).read_bytes() != value:
                raise ValueError("ordinary fresh extraction differs: " + name)
    print("pinned ordinary SDK ownership, admission and four-route extraction matches")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
