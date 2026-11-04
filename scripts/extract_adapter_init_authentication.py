#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract the original selected Rust Init authentication loop with pinned Charon/Aeneas.

No Rust source preparation is performed. Generated Lean receives only the exact
reviewed strict warning header and the two explicit primitive instance binders.
These changes are reversible and every generated body byte is retained.
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
SUBDIRECTORY = "BeaconcryptCore/AdapterInitAuthenticationExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = "beaconcrypt::auth::authenticate_init"
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = common.GENERATED
MODELS = common.MODELS
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "Cargo.toml",
    "Cargo.lock",
    "hax.toml",
    "beaconcrypt/Cargo.toml",
    "beaconcrypt/src/lib.rs",
    "beaconcrypt/src/auth.rs",
    "beaconcrypt-core/Cargo.toml",
    "beaconcrypt-crypto/Cargo.toml",
    "beaconcrypt-parse/Cargo.toml",
    "scripts/extract_adapter_init_authentication.py",
    "scripts/extract_adapter_record.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterAuthenticationExtraction/FunsExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterOptionDeref.lean",
)
BINDER = "variable [beaconcrypt.auth.Operations] [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]\n"
LINTERS = (
    "dupNamespace",
    "hashCommand",
    "unusedVariables",
    "style.whitespace",
    "style.setOption",
    "style.longLine",
)
POLICY = "set_option autoImplicit false\nset_option warningAsError true\n"
REVIEWED_BODIES = {
    "Types.lean": "3fe36d9750c486ec56d95d7205e16786eeff2d169becaf3527a270225807c718",
    "Funs.lean": "75039df3eeb51278359e6c37739740c87cb2dad6ca67a8078c22d09ecb70c4b9",
}
TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "insert_after": "namespace beaconcrypt\n",
    "text": BINDER,
    "body_rewrites": [],
}
PLATFORM_SIGNATURES = {
    "beaconcrypt_crypto::crypto_sign::PublicKey::from_bytes": "Slice U8 -> RustM (Result PublicKey Error)",
    "beaconcrypt_crypto::crypto_sign::verify": "Slice U8 -> PublicKey -> RustM (Option (Vec U8))",
    "core::option::Option<Vec<u8>>::as_deref": "Option Vec U8 -> RustM (Option Slice U8); actual Deref once on Some",
}
EXTERNAL_SIGNATURES = {
    "auth.execute_hash": "beaconcrypt_core.registration.HashRequest → RustM (core.option.Option (Array Std.U8 64#usize))",
    "auth.verify_requested": "beaconcrypt_core.registration.MldsaVerificationRequest → RustM Bool",
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    text = contents.decode()
    common.require_model(contents, name)
    if name not in REVIEWED_BODIES or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("Init authentication generated module roster changed")
    if (
        digest(text.split("namespace beaconcrypt\n", 1)[1].encode())
        != REVIEWED_BODIES[name]
    ):
        raise ValueError("reviewed Init authentication generated body changed")
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("unreviewed generated warning header")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or POLICY in text:
        raise ValueError("warning header insertion changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    if name == "Funs.lean":
        text = text.replace(
            "namespace beaconcrypt\n", "namespace beaconcrypt\n" + BINDER, 1
        )
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def denormalize(contents: bytes, name: str) -> bytes:
    text = contents.decode()
    common.require_handwritten_warning_policy(contents, name)
    if name == "Funs.lean":
        if text.count("namespace beaconcrypt\n" + BINDER) != 1:
            raise ValueError("Init authentication binder changed")
        text = text.replace(
            "namespace beaconcrypt\n" + BINDER, "namespace beaconcrypt\n", 1
        )
    if text.count("open Std.Do\n" + POLICY) != 1:
        raise ValueError("generated warning policy changed")
    text = text.replace(
        "open Std.Do\n" + POLICY,
        "open Std.Do\n"
        + "".join("set_option linter." + name + " false\n" for name in LINTERS),
        1,
    )
    raw = text.encode()
    if normalize(raw, name) != contents:
        raise ValueError("Init authentication normalization does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    expected = {name for name in GENERATED if name.endswith("_Template.lean")}
    if set(templates) != expected:
        raise ValueError("external template roster changed")
    if common.TEMPLATE_DECLARATION.search(
        common.lean_code_without_comments_or_strings(
            templates["TypesExternal_Template.lean"]
        )
    ):
        raise ValueError("unexpected external type obligation")
    source = common.lean_code_without_comments_or_strings(
        templates["FunsExternal_Template.lean"]
    )
    declarations = list(common.TEMPLATE_DECLARATION.finditer(source))
    signatures = {}
    for index, declaration in enumerate(declarations):
        end = (
            declarations[index + 1].start()
            if index + 1 < len(declarations)
            else len(source)
        )
        signature = re.fullmatch(
            r"\s+([A-Za-z0-9_.]+)\s*:\s*(.+?)\s*", source[declaration.end() : end], re.S
        )
        if declaration.group(1) != "axiom" or signature is None:
            raise ValueError("unreviewed external function obligation")
        name, value = signature.groups()
        if name in signatures:
            raise ValueError("duplicate external function")
        signatures[name] = " ".join(value.split())
    if signatures != EXTERNAL_SIGNATURES:
        raise ValueError("Init authentication external signature roster changed")


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
            "--start-from=" + START_FROM,
            "--opaque=beaconcrypt",
            "--include=" + START_FROM,
            "--opaque=beaconcrypt_core",
            "--opaque=beaconcrypt_crypto",
            "--opaque=core",
            "--opaque=alloc",
            "--opaque=std",
            "--include=core::option::Option",
            "--include=core::result::Result",
            "--include=core::ops::control_flow::ControlFlow",
            "--include=core::convert::Infallible",
            "--include=beaconcrypt_core::registration::InitAuthentication",
            "--include=beaconcrypt_core::registration::Ed25519VerificationRequest",
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
        raise ValueError("Init authentication provenance metadata roster changed")
    for name, value in metadata().items():
        if provenance[name] != value:
            raise ValueError("Init authentication provenance metadata changed: " + name)
    for name, value in snapshot(root, destination).items():
        if provenance[name] != value:
            raise ValueError("Init authentication source/model hash drift: " + name)
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
            raise ValueError("Init authentication installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("Init authentication raw generated body drift: " + name)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_text())
    if (
        set(evidence) != {"templates", "platform_signatures"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("Init authentication builtin signature roster changed")
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
            raise ValueError("Init authentication external signature evidence drift")


def run(command: list[str], environment: dict[str, str], log: Path) -> None:
    with log.open("w") as output:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
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
            raise RuntimeError("Init authentication extraction timeout: " + str(log))
    if code:
        raise RuntimeError("Init authentication extraction failed: " + str(log))


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
            "Source Init authentication, builtin interfaces and generated evidence match"
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
    environment = common.extraction_environment(work)
    for index, command in enumerate(commands(tools, work)):
        run(command, environment, work / ("charon.log" if index == 0 else "aeneas.log"))
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
        raise ValueError("Init authentication inputs changed during extraction")
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
                "Init authentication extraction drift: " + ", ".join(changed)
            )
    print(
        "Source Init authentication fresh extraction and provenance match"
        if not args.write
        else "Wrote reviewed source Init authentication extraction and evidence"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
