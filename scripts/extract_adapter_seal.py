#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the unchanged original seal dispatcher with explicit primitive leaves.

The Single branch keeps its direct borrowed plaintext. Prefixed joining and its
allocation failure precede detached AEAD. Generic joining and cryptography remain
explicit interfaces; no primitive, zeroization, codec or security law is assumed.
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

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterSealExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = ["beaconcrypt::ratchet::execute_seal_request"]
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = common.GENERATED
MODELS = common.MODELS
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "hax.toml",
    "scripts/extract_adapter_seal.py",
    "scripts/extract_adapter_record.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterSealPrimitive.lean",
)
MEMBERS = (
    "beaconcrypt",
    "beaconcrypt-core",
    "beaconcrypt-crypto",
    "beaconcrypt-parse",
    "beaconcrypt-ffi",
    "beaconcrypt-wasm",
)
BINDER = (
    "variable [BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]\n"
    "variable [BeaconcryptCore.Refinement.AdapterSealJoinCallbacks.Operations]\n"
)
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
    "Types.lean": "89c58951f50b1467b5b4e6980c969d8e05b9e1b1aeaf58120e7c7e1e27d9ef96",
    "Funs.lean": "c6eb0ddd5ebe874b99fc1c255a3dbfc142f7ccf0ed2c81085c2aa437a257215c",
    "TypesExternal_Template.lean": "8523567a9ec3d2416673fd29f4aa75fe72104a375dba090d9d0746e2e9ca447e",
    "FunsExternal_Template.lean": "f60b18aab2f54ec391b0df1aa47dd4af88451aa11a7a3d81e42e7dd4ca8d94cf",
}
INTERFACES = []

TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "namespace": ["beaconcrypt", "beaconcrypt_seal"],
    "binders": BINDER,
    "mutable_serializers": [list(rule) for rule in INTERFACES],
    "body_rewrites": [],
}
PLATFORM_SIGNATURES = {
    "ratchet::join_record_parts": "forall N, Array (Slice U8) N -> RustM (Option (Vec U8))",
    "AdapterSealPrimitive.fromKey": "Array U8 32 -> RustM Key",
    "AdapterSealPrimitive.fromNonce": "Array U8 12 -> RustM Nonce",
    "AdapterSealPrimitive.aead": "Slice U8 -> Option (Slice U8) -> Nonce -> Key -> RustM (Result (Vec U8 * Vec U8) Error)",
    "Zeroizing": "selected value wrapper; constructor/deref retain value; no drop or memory-erasure law",
}
REVIEWED_MODEL_SHA256 = {
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterSealPrimitive.lean": "4bd38308facf82a559d73ab8ccb95265c5aef4e4e9b7aa828b3e230b7421b9e0",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterSealExtraction/TypesExternal.lean": "dcd8468321fc74250710d4be2107cf8b367fe4810ec38fb03bf4d09a70c3e4bc",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterSealExtraction/FunsExternal.lean": "6ecd51855d35810d1b0a9c491969d508c7c1ad1a9ff5e75036d181e0415c31a0",
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed original seal dispatcher: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("seal dispatcher namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_seal\n" + (BINDER if name == "Funs.lean" else ""),
        1,
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_seal\n", 1)
    if name == "Funs.lean":
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
        for before, after in reversed(INTERFACES):
            if text.count(after) != 1:
                raise ValueError("installed mutable serializer interface changed")
            text = text.replace(after, before, 1)
    namespace = "namespace beaconcrypt_seal\n" + (BINDER if name == "Funs.lean" else "")
    if text.count(namespace) != 1 or text.count("end beaconcrypt_seal\n") != 1:
        raise ValueError("installed source namespace/binders changed")
    text = text.replace(namespace, "namespace beaconcrypt\n", 1)
    text = text.replace("end beaconcrypt_seal\n", "end beaconcrypt\n", 1)
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
        raise ValueError("source seal dispatcher does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("seal dispatcher external template roster changed")
    for name, contents in templates.items():
        if digest(contents) != RAW_SHA256[name]:
            raise ValueError("seal dispatcher external signature changed")


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
    if fixture.exists() or fixture.is_symlink():
        raise ValueError("source fixture must be fresh")
    fixture.mkdir(parents=True)
    for name, contents in source_files(root).items():
        path = fixture / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)


def check_fixture(fixture: Path, expected: dict[str, str]) -> None:
    actual = {}
    for path in fixture.rglob("*"):
        if path.is_symlink():
            raise ValueError("changed source fixture symlink")
        if path.is_file():
            actual[path.relative_to(fixture).as_posix()] = digest(path.read_bytes())
    if actual != expected:
        raise ValueError("original source fixture changed during extraction")


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in SOURCE_FILES
        },
        "fixture_source_sha256": {
            name: digest(contents) for name, contents in source_files(root).items()
        },
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
    return (
        [
            str(tools["charon"]),
            "cargo",
            "--preset=aeneas",
            "--sysroot=default",
            *["--start-from=" + name for name in START_FROM],
            *[
                "--opaque=" + name
                for name in (
                    "beaconcrypt",
                    "beaconcrypt_core",
                    "beaconcrypt_crypto",
                    "zeroize",
                    "core",
                    "alloc",
                    "std",
                    "beaconcrypt_parse",
                )
            ],
            *["--include=" + name for name in START_FROM],
            "--include=beaconcrypt_core::record_effects::AeadSealRequest",
            "--include=beaconcrypt_core::record_effects::SealPlaintextRequest",
            "--include=core::option::Option",
            "--include=core::result::Result",
            "--include=core::ops::control_flow::ControlFlow",
            "--include=core::convert::Infallible",
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
            if "/AdapterSealExtraction/" in name
            else root / name
        )
        if digest(path.read_bytes()) != expected:
            raise ValueError("reviewed seal model changed: " + name)


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
        raise ValueError("seal provenance metadata roster changed")
    for name, value in metadata().items():
        if provenance[name] != value:
            raise ValueError("seal provenance metadata changed: " + name)
    for name, value in snapshot(root, destination).items():
        if provenance[name] != value:
            raise ValueError("seal source/model hash drift: " + name)
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
            raise ValueError("seal installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("seal raw generated body drift: " + name)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_text())
    if (
        set(evidence) != {"templates", "platform_signatures"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("seal builtin signature roster changed")
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
            raise ValueError("seal external signature evidence drift")


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
            raise RuntimeError("seal extraction timeout: " + str(log))
    if code:
        raise RuntimeError("seal extraction failed: " + str(log))


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
        print("Source seal dispatcher, builtin interfaces and generated evidence match")
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required for fresh extraction")
    if args.work_dir.is_symlink():
        raise ValueError("scratch directory must not be a symlink")
    work = common.isolated_work_directory(args.work_dir)
    if work.exists() and any(work.iterdir()):
        raise ValueError("seal extraction scratch directory must be fresh")
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
        raise ValueError("seal inputs changed during extraction")
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
            raise ValueError("seal extraction drift: " + ", ".join(changed))
    print(
        "Source seal dispatcher fresh extraction and provenance match"
        if not args.write
        else "Wrote reviewed source seal dispatcher extraction and evidence"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
