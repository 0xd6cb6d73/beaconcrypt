#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the actual finite ordinary-frame dispatcher with source certificates.

The original many-part tail is outlined unchanged and remains abstract outside
the selected API shape. Length/index normalization preserves the original four
slice-pattern branches. The selected three-part case reuses the exact existing
source frame encoder without a codec-correctness hypothesis.
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
import prepare_frame_dispatch_source as preparation

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/FrameDispatchExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = ["beaconcrypt_parse::frame::encode_parts"]
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")
MODELS = common.MODELS
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "Cargo.toml",
    "Cargo.lock",
    "hax.toml",
    "beaconcrypt/Cargo.toml",
    "beaconcrypt/src/lib.rs",
    "beaconcrypt/src/wire.rs",
    "beaconcrypt/src/ratchet.rs",
    "beaconcrypt-parse/src/frame.rs",
    "scripts/prepare_frame_dispatch_source.py",
    "scripts/registration_codec_normalization.py",
    "scripts/prepare_adapter_public_wrappers.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/FrameCodecExtraction/Funs.lean",
    "beaconcrypt-core/Cargo.toml",
    "beaconcrypt-crypto/Cargo.toml",
    "beaconcrypt-parse/Cargo.toml",
    "scripts/extract_frame_dispatch.py",
    "scripts/test_extract_frame_dispatch.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/RegistrationPrimitiveExtraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/FunsExternal.lean",
    "scripts/extract_adapter_record.py",
)
BINDER = "variable [BeaconcryptCore.Refinement.FrameDispatchFallback.Operations]\n"
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
    "Funs.lean": "01fb3c5026131bc169d96809c076342dae0225a40bd7cf22a586ce30f0634d8a",
    "FunsExternal_Template.lean": "560829256fbe1b2e70c6139b9af48e82640c5526d7a73f55ced9b8376e162b29",
    "Types.lean": "573896083f3e384a06038004dff1e26ad5d74510f341f6c1fd3b5b1011e1552b",
}
INTERFACES = []

TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "namespace": ["beaconcrypt_parse", "beaconcrypt_parse_dispatch"],
    "binders": BINDER,
    "mutable_serializers": [list(rule) for rule in INTERFACES],
    "body_rewrites": [],
}
PLATFORM_SIGNATURES = {
    "frame::encode_three": "existing actual FrameCodecExtraction source encoder",
    "frame::_proof_encode_many": "entire original outlined fallback; outside selected three-part path",
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed original registration writer: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if (
        text.count("open Std.Do\n") != 1
        or text.count("namespace beaconcrypt_parse\n") != 1
    ):
        raise ValueError("registration writer namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt_parse\n",
        "namespace beaconcrypt_parse_dispatch\n"
        + (BINDER if name == "Funs.lean" else ""),
        1,
    )
    text = text.replace(
        "end beaconcrypt_parse\n", "end beaconcrypt_parse_dispatch\n", 1
    )
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
    namespace = "namespace beaconcrypt_parse_dispatch\n" + (
        BINDER if name == "Funs.lean" else ""
    )
    if (
        text.count(namespace) != 1
        or text.count("end beaconcrypt_parse_dispatch\n") != 1
    ):
        raise ValueError("installed source namespace/binders changed")
    text = text.replace(namespace, "namespace beaconcrypt_parse\n", 1)
    text = text.replace(
        "end beaconcrypt_parse_dispatch\n", "end beaconcrypt_parse\n", 1
    )
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
        raise ValueError("source registration writer does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    if set(templates) != {"FunsExternal_Template.lean"}:
        raise ValueError("registration writer external template roster changed")
    for name, contents in templates.items():
        if digest(contents) != RAW_SHA256[name]:
            raise ValueError("registration writer external signature changed")


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in SOURCE_FILES
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
            "--opaque=beaconcrypt_parse",
            *["--include=" + name for name in START_FROM],
            "--opaque=beaconcrypt_core",
            "--opaque=beaconcrypt_parse",
            "--dest-file",
            str(work / "beaconcrypt.llbc"),
            "--",
            "-p",
            "beaconcrypt-parse",
            "--lib",
            "--locked",
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
        raise ValueError("writer provenance metadata roster changed")
    for name, value in metadata().items():
        if provenance[name] != value:
            raise ValueError("writer provenance metadata changed: " + name)
    for name, value in snapshot(root, destination).items():
        if provenance[name] != value:
            raise ValueError("writer source/model hash drift: " + name)
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
            raise ValueError("writer installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("writer raw generated body drift: " + name)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_text())
    if (
        set(evidence) != {"templates", "platform_signatures", "source_preparation"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("writer builtin signature roster changed")
    original = (root / preparation.SOURCE).read_text()
    prepared, certificate = preparation.transform(original)
    source_evidence = evidence["source_preparation"]
    if (
        set(source_evidence)
        != {
            "source_sha256",
            "prepared_sha256",
            "control_certificate",
            "unchanged_sha256",
        }
        or source_evidence["source_sha256"] != digest(original.encode())
        or source_evidence["prepared_sha256"] != digest(prepared.encode())
        or source_evidence["control_certificate"] != certificate
    ):
        raise ValueError("frame dispatch source control certificate changed")
    expected_unchanged = {
        name: digest(contents)
        for name, contents in preparation.source_files(root).items()
        if name != preparation.SOURCE
    }
    if source_evidence["unchanged_sha256"] != expected_unchanged:
        raise ValueError("frame dispatch immutable fixture source roster changed")
    for name, expected in source_evidence["unchanged_sha256"].items():
        if digest((root / name).read_bytes()) != expected:
            raise ValueError("frame dispatch immutable fixture source drift")
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
            raise ValueError("writer external signature evidence drift")


def run(
    command: list[str], environment: dict[str, str], log: Path, cwd: Path = ROOT
) -> None:
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
            code = process.wait(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            raise RuntimeError("writer extraction timeout: " + str(log))
    if code:
        raise RuntimeError("writer extraction failed: " + str(log))


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
        print("Source writer, builtin interfaces and generated evidence match")
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
    environment = common.extraction_environment(work)
    fixture = work / "source"
    source_certificate = preparation.prepare(ROOT, fixture)
    for index, command in enumerate(commands(tools, work)):
        run(
            command,
            environment,
            work / ("charon.log" if index == 0 else "aeneas.log"),
            cwd=fixture,
        )
    generated = work / "generated" / SUBDIRECTORY
    contents = assemble(generated)
    signatures = json.loads(contents["external-signatures.json"])
    signatures["source_preparation"] = source_certificate
    contents["external-signatures.json"] = (
        json.dumps(signatures, indent=2, sort_keys=True) + "\n"
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
        raise ValueError("writer inputs changed during extraction")
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
            raise ValueError("writer extraction drift: " + ", ".join(changed))
    print(
        "Source writer fresh extraction and provenance match"
        if not args.write
        else "Wrote reviewed source writer extraction and evidence"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
