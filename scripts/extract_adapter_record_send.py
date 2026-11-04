#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the actual outer record send driver with certified borrow localization.

Only an isolated fixture distributes pure optional borrowed-view consumption;
all primitive leaves, short circuits and mutable commitment effects are retained.
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
import prepare_adapter_record_send as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterRecordSendExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = ["beaconcrypt::ratchet::execute_record_send"]
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = common.GENERATED
MODELS = common.MODELS
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "hax.toml",
    "scripts/extract_adapter_record_send.py",
    "scripts/prepare_adapter_record_send.py",
    "scripts/extract_adapter_record.py",
    "scripts/extract_adapter_seal.py",
    "scripts/registration_codec_normalization.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterRecordSendBorrow.lean",
)

MEMBERS = (
    "beaconcrypt",
    "beaconcrypt-core",
    "beaconcrypt-crypto",
    "beaconcrypt-parse",
    "beaconcrypt-ffi",
    "beaconcrypt-wasm",
)
BINDER = "variable [beaconcrypt_record_send.ratchet.Operations]\n"

LINTERS = (
    "dupNamespace",
    "hashCommand",
    "unusedVariables",
    "style.whitespace",
    "style.setOption",
    "style.longLine",
)
POLICY = "set_option autoImplicit false\nset_option warningAsError true\n"
RAW_SHA256 = {
    "Types.lean": "27166238164a830b4c8e534bb1a05e2b4ec6f561306374c0a41234e4e63b5db4",
    "Funs.lean": "04d258a293b273ab2c185728f5f5296cc1a8c783dfbb190ac1210ffb75ab5ec1",
    "TypesExternal_Template.lean": "8523567a9ec3d2416673fd29f4aa75fe72104a375dba090d9d0746e2e9ca447e",
    "FunsExternal_Template.lean": "5c303ca131e2e914ea714d2b3d3526f28e537fab199a0e4679f1b7add10a9c54",
}

INTERFACES = []

TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "namespace": ["beaconcrypt", "beaconcrypt_record_send"],
    "binders": BINDER,
    "mutable_serializers": [list(rule) for rule in INTERFACES],
    "body_rewrites": [
        [
            "(c : ratchet.execute_record_send.closure)",
            "(_c : ratchet.execute_record_send.closure)",
        ]
    ],
}
PLATFORM_SIGNATURES = {
    "kdf": "actual SymmetricRatchetKdfRequest -> RustM RatchetKdfResponse",
    "sealing": "actual AeadSealRequest -> RustM Option(Vec U8 * Array U8 16)",
    "hash": "actual CommitmentTranscript -> RustM (Option(Array U8 64) * CommitmentTranscript)",
    "writer": "actual RecordWriteRequest -> RustM Option(Vec U8)",
}
REVIEWED_MODEL_SHA256 = {
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordSendExtraction/TypesExternal.lean": "dc0e1b55fd1beeb1c394ba8d24159be34bd0eb6decb4bd41380c308c454c0a57",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterRecordSendExtraction/FunsExternal.lean": "705af4f17473a1844db1dfcdebd651c75fd1d9156af01d9b8c7315797b9dc410",
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed original outer send driver: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("outer send driver namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_record_send\n" + (BINDER if name == "Funs.lean" else ""),
        1,
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_record_send\n", 1)
    if name == "Funs.lean":
        text = text.replace(
            "(c : ratchet.execute_record_send.closure)",
            "(_c : ratchet.execute_record_send.closure)",
            1,
        )
        for before, after in INTERFACES:
            if text.count(before) != 1 or after in text:
                raise ValueError("mutable schema serializer interface changed")
            text = text.replace(before, after, 1)
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def denormalize(contents: bytes, name: str) -> bytes:
    common.require_handwritten_warning_policy(contents, name)
    text = contents.decode()
    if name == "Funs.lean":
        text = text.replace(
            "(_c : ratchet.execute_record_send.closure)",
            "(c : ratchet.execute_record_send.closure)",
            1,
        )
        for before, after in reversed(INTERFACES):
            if text.count(after) != 1:
                raise ValueError("installed mutable serializer interface changed")
            text = text.replace(after, before, 1)
    namespace = "namespace beaconcrypt_record_send\n" + (
        BINDER if name == "Funs.lean" else ""
    )
    if text.count(namespace) != 1 or text.count("end beaconcrypt_record_send\n") != 1:
        raise ValueError("installed source namespace/binders changed")
    text = text.replace(namespace, "namespace beaconcrypt\n", 1)
    text = text.replace("end beaconcrypt_record_send\n", "end beaconcrypt\n", 1)
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
        raise ValueError("source outer send driver does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("outer send driver external template roster changed")
    for name, contents in templates.items():
        if digest(contents) != RAW_SHA256[name]:
            raise ValueError("outer send driver external signature changed")


def source_files(root: Path) -> dict[str, bytes]:
    files = {}
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        path = root / name
        if path.is_symlink():
            raise ValueError("source fixture symlink")
        if path.is_file():
            files[name] = path.read_bytes()
    for member in MEMBERS:
        if (root / member).is_symlink() or (root / member / "src").is_symlink():
            raise ValueError("source member symlink")
        for name in ("Cargo.toml", "build.rs"):
            path = root / member / name
            if path.is_symlink():
                raise ValueError("source fixture symlink")
            if path.is_file():
                files[path.relative_to(root).as_posix()] = path.read_bytes()
        for path in sorted((root / member / "src").rglob("*")):
            if path.is_symlink():
                raise ValueError("source fixture symlink")
            if path.is_file():
                files[path.relative_to(root).as_posix()] = path.read_bytes()
    return files


def prepare_source(root: Path, fixture: Path) -> None:
    preparation.prepare(root, fixture)


def check_fixture(fixture: Path, expected: dict) -> None:
    preparation.check_fixture(fixture, expected)


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in SOURCE_FILES
        },
        "fixture_source_sha256": preparation.certificate(root),
        "model_sha256": {
            name: digest((destination / name).read_bytes()) for name in MODELS
        },
    }


def assemble(generated: Path) -> dict[str, bytes]:
    raw = {name: (generated / name).read_bytes() for name in GENERATED}
    templates = {
        name: raw[name] for name in GENERATED if name.endswith("_Template.lean")
    }
    validate_templates(templates)
    evidence = {
        "templates": {
            name: {"sha256": digest(value), "source": value.decode()}
            for name, value in templates.items()
        },
        "platform_signatures": PLATFORM_SIGNATURES,
    }
    return {
        **{name: normalize(raw[name], name) for name in ["Types.lean", "Funs.lean"]},
        "external-signatures.json": (
            json.dumps(evidence, indent=2, sort_keys=True) + "\n"
        ).encode(),
    }


def commands(tools: dict[str, Path], work: Path) -> tuple[list[str], list[str]]:
    replacements = {
        "CHARON": str(tools["charon"]),
        "AENEAS": str(tools["aeneas"]),
        "LLBC": str(work / "beaconcrypt.llbc"),
        "GENERATED": str(work / "generated"),
    }
    return tuple(
        [replacements.get(item, item) for item in command]
        for command in (
            [
                "CHARON",
                "cargo",
                "--preset=aeneas",
                "--sysroot=default",
                "--start-from=beaconcrypt::ratchet::execute_record_send",
                "--opaque=beaconcrypt_core",
                "--opaque=beaconcrypt::ratchet::ratchet_hkdf",
                "--opaque=beaconcrypt::ratchet::execute_commitment_hash",
                "--include=beaconcrypt_core::record_effects::RecordSendStart",
                "--include=beaconcrypt_core::record_effects::SealAfterAead",
                "--include=beaconcrypt_core::record_effects::SealAfterCommitment",
                "--opaque=beaconcrypt::ratchet::execute_seal_request",
                "--opaque=beaconcrypt::ratchet::execute_write_request",
                "--include=beaconcrypt_core::record_effects::SealedRecord",
                "--dest-file",
                "LLBC",
                "--",
                "-p",
                "beaconcrypt",
                "--lib",
                "--locked",
                "--no-default-features",
                "--features=beacon,pqxdh",
            ],
            [
                "AENEAS",
                "-no-progress-bar",
                "-sequential",
                "-abort-on-error",
                "-backend",
                "lean",
                "-core-models-lib",
                "-split-files",
                "-specs",
                "hax",
                "LLBC",
                "-dest",
                "GENERATED",
                "-subdir",
                "BeaconcryptCore/AdapterRecordSendExtraction",
            ],
        )
    )


def metadata() -> dict:
    return {
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "rust_start_from": START_FROM,
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "generated_transformation": TRANSFORMATION,
        "reviewed_model_sha256": REVIEWED_MODEL_SHA256,
    }


def validate_models(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    for name, expected in REVIEWED_MODEL_SHA256.items():
        path = (
            destination / Path(name).name
            if "/AdapterRecordSendExtraction/" in name
            else root / name
        )
        if digest(path.read_bytes()) != expected:
            raise ValueError("reviewed outer send model changed: " + name)


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    validate_models(root, destination)
    provenance = json.loads((destination / "provenance.json").read_text())
    expected_roster = (
        set(metadata())
        | set(snapshot(root, destination))
        | {"tool_sha256", "raw_generated_sha256", "installed_sha256"}
    )
    if set(provenance) != expected_roster:
        raise ValueError("outer send provenance metadata roster changed")
    for name, value in metadata().items():
        if provenance[name] != value:
            raise ValueError("outer send provenance metadata changed: " + name)
    for name, value in snapshot(root, destination).items():
        if provenance[name] != value:
            raise ValueError("outer send source/model hash drift: " + name)
    common.require_hash_roster(
        provenance["tool_sha256"], set(PINNED_TOOLS), "tool_sha256"
    )
    raw = common.require_hash_roster(
        provenance["raw_generated_sha256"], set(GENERATED), "raw_generated_sha256"
    )
    installed = common.require_hash_roster(
        provenance["installed_sha256"], set(INSTALLED), "installed_sha256"
    )
    for name in INSTALLED:
        contents = (destination / name).read_bytes()
        if digest(contents) != installed[name]:
            raise ValueError("outer send installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("outer send raw generated body drift: " + name)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_text())
    if (
        set(evidence) != {"templates", "platform_signatures"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("outer send builtin signature roster changed")
    templates = evidence["templates"]
    validate_templates(
        {name: value["source"].encode() for name, value in templates.items()}
    )
    for name, value in templates.items():
        if (
            set(value) != {"sha256", "source"}
            or digest(value["source"].encode()) != value["sha256"]
            or value["sha256"] != raw[name]
        ):
            raise ValueError("outer send external signature evidence drift")


def run(
    command: list[str], environment: dict[str, str], log: Path, fixture: Path
) -> None:
    with log.open("w") as output:
        process = subprocess.Popen(
            command,
            cwd=fixture,
            env=environment,
            stdout=output,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            code = process.wait(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise RuntimeError("outer send extraction timeout: " + str(log))
    if code:
        raise RuntimeError("outer send extraction failed: " + str(log))


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
            "Source outer send driver, builtin interfaces and generated evidence match"
        )
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required for fresh extraction")
    if args.work_dir.is_symlink():
        raise ValueError("scratch directory must not be a symlink")
    work = common.isolated_work_directory(args.work_dir)
    if work.exists() and any(work.iterdir()):
        raise ValueError("outer send extraction scratch directory must be fresh")
    common.validate_work_paths(work)
    common.validate_configuration(tomllib.loads((ROOT / "hax.toml").read_text()))
    validate_models()
    before = snapshot()
    tools = {
        name: args.tools_root / name / version / name
        for name, version in PINNED_TOOLS.items()
    }
    tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
    work.mkdir(parents=True, exist_ok=True)
    fixture = work / "source"
    prepare_source(ROOT, fixture)
    environment = common.extraction_environment(work)
    for index, command in enumerate(commands(tools, work)):
        run(
            command,
            environment,
            work / ("charon.log" if index == 0 else "aeneas.log"),
            fixture,
        )
    check_fixture(fixture, before["fixture_source_sha256"])
    generated = work / "generated" / SUBDIRECTORY
    contents = assemble(generated)
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
        raise ValueError("outer send inputs changed during extraction")
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
            DESTINATION.mkdir(parents=True, exist_ok=True)
            (DESTINATION / name).write_bytes(value)
    else:
        changed = [
            name
            for name, value in contents.items()
            if (DESTINATION / name).read_bytes() != value
        ]
        if changed:
            raise ValueError("outer send extraction drift: " + ", ".join(changed))
    print(
        "Source outer send driver fresh extraction and provenance match"
        if not args.write
        else "Wrote reviewed source outer send driver extraction and evidence"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
