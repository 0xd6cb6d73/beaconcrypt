#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the exact fixed-two prefixed plaintext join with pinned tools.

The checked isolated preparation appends only the two-part specialization of
original checked length and ordered extension loops. Production and generated
Rust remain unchanged. Lean header/namespace/binder normalization is reversible;
reservation failures, returned vectors and every original branch are retained.
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
import prepare_adapter_seal_join as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterSealJoinExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = ["beaconcrypt::ratchet::_proof_join_seal_two"]
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = common.GENERATED
MODELS = common.MODELS
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "hax.toml",
    "scripts/extract_adapter_seal_join.py",
    "scripts/prepare_adapter_seal_join.py",
    "scripts/test_extract_adapter_seal_join.py",
    "scripts/test_prepare_adapter_seal_join.py",
    "scripts/prepare_adapter_record_helpers.py",
    "scripts/prepare_adapter_public_wrappers.py",
    "scripts/registration_codec_normalization.py",
    "scripts/extract_adapter_record.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterSealFixedParts.lean",
)
BINDER = "variable [BeaconcryptCore.Refinement.AdapterWirePrimitive.Operations]\n"
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
    "Funs.lean": "2954bb6111e4aa0ac97d609f162792ba82e07ec8e33fb3603c281848723c16e1",
    "FunsExternal_Template.lean": "6066715465c4a2b342348b6fce9270138db6274b885b14221b55a56d8ca0faa3",
    "Types.lean": "5d3e9968e5e1a92b823fa4abda1147e1330ae23006cf275f0cd48d89d54e3a66",
    "TypesExternal_Template.lean": "8523567a9ec3d2416673fd29f4aa75fe72104a375dba090d9d0746e2e9ca447e",
}
MODEL_SHA256 = {
    "TypesExternal.lean": "ab5de7ba0d1e9aaed6a4e31f4b0689b776949cebaf35fbbdfb4bba1b43ff2f3c",
    "FunsExternal.lean": "ab5de7ba0d1e9aaed6a4e31f4b0689b776949cebaf35fbbdfb4bba1b43ff2f3c",
}
INTERFACES = []
TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "namespace": ["beaconcrypt", "beaconcrypt_seal_join"],
    "binders": BINDER,
    "mutable_serializers": [],
    "body_rewrites": [],
}
PLATFORM_SIGNATURES = {
    "alloc::vec::Vec::try_reserve_exact": "Vec U8 -> Usize -> RustM (Result Unit operations.ReserveError * Vec U8); explicit AdapterWirePrimitive.Operations retains the returned vector in either Result branch",
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed original fixed-two seal join: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("fixed-two seal join namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_seal_join\n" + (BINDER if name == "Funs.lean" else ""),
        1,
    )
    text = text.replace("end beaconcrypt\n", "end beaconcrypt_seal_join\n", 1)
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
    namespace = "namespace beaconcrypt_seal_join\n" + (
        BINDER if name == "Funs.lean" else ""
    )
    if text.count(namespace) != 1 or text.count("end beaconcrypt_seal_join\n") != 1:
        raise ValueError("installed source namespace/binders changed")
    text = text.replace(namespace, "namespace beaconcrypt\n", 1)
    text = text.replace("end beaconcrypt_seal_join\n", "end beaconcrypt\n", 1)
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
        raise ValueError("source fixed-two seal join does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("fixed-two seal join external template roster changed")
    for name, contents in templates.items():
        if digest(contents) != RAW_SHA256[name]:
            raise ValueError("fixed-two seal join external signature changed")


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    models = {name: digest((destination / name).read_bytes()) for name in MODELS}
    if models != MODEL_SHA256:
        raise ValueError("unreviewed seal-join external model")
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes())
            for name in sorted(set(SOURCE_FILES) | set(preparation.source_files(root)))
        },
        "source_preparation": preparation.certificate(root),
        "model_sha256": models,
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
            "--opaque=beaconcrypt",
            "--opaque=core",
            "--opaque=alloc",
            "--opaque=std",
            *["--include=" + name for name in START_FROM],
            "--opaque=beaconcrypt_core",
            "--opaque=beaconcrypt_parse",
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
    }


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    provenance = json.loads((destination / "provenance.json").read_text())
    expected_roster = (
        set(metadata())
        | set(snapshot(root, destination))
        | {"tool_sha256", "raw_generated_sha256", "installed_sha256"}
    )
    if set(provenance) != expected_roster:
        raise ValueError("seal-join provenance metadata roster changed")
    for name, value in metadata().items():
        if provenance[name] != value:
            raise ValueError("seal-join provenance metadata changed: " + name)
    for name, value in snapshot(root, destination).items():
        if provenance[name] != value:
            raise ValueError("seal-join source/model hash drift: " + name)
    common.require_hash_roster(
        provenance["tool_sha256"], set(PINNED_TOOLS), "tool_sha256"
    )
    raw = common.require_hash_roster(
        provenance["raw_generated_sha256"], set(GENERATED), "raw_generated_sha256"
    )
    if raw != RAW_SHA256:
        raise ValueError("seal-join reviewed raw output changed")
    installed = common.require_hash_roster(
        provenance["installed_sha256"], set(INSTALLED), "installed_sha256"
    )
    for name in INSTALLED:
        contents = (destination / name).read_bytes()
        if digest(contents) != installed[name]:
            raise ValueError("seal-join installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("seal-join raw generated body drift: " + name)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_text())
    if (
        set(evidence) != {"templates", "platform_signatures"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("seal-join builtin signature roster changed")
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
            raise ValueError("seal-join external signature evidence drift")


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
            raise RuntimeError("seal-join extraction timeout: " + str(log))
    if code:
        raise RuntimeError("seal-join extraction failed: " + str(log))


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
            "Fixed-two seal-join source preparation, interfaces and generated evidence match"
        )
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required for fresh extraction")
    if args.work_dir.is_symlink():
        raise ValueError("seal-join scratch directory must not be a symlink")
    work = common.isolated_work_directory(args.work_dir)
    if (work / "source").exists() or (work / "source").is_symlink():
        raise ValueError("seal-join source fixture must be fresh")
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
    preparation.prepare(ROOT, fixture)
    environment = common.extraction_environment(work)
    for index, command in enumerate(commands(tools, work)):
        run(
            command,
            environment,
            work / ("charon.log" if index == 0 else "aeneas.log"),
            fixture,
        )
    preparation.check_fixture(ROOT, fixture, before["source_preparation"])
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
        raise ValueError("seal-join inputs changed during extraction")
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
            raise ValueError("seal-join extraction drift: " + ", ".join(changed))
    print(
        "Source seal-join fresh extraction and provenance match"
        if not args.write
        else "Wrote reviewed source seal-join extraction and evidence"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
