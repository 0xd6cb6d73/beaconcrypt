#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Extract exactly the three original ratchet HKDF wrappers without Rust edits.

The canonical and both role-only profiles must produce identical source bodies
and external signatures. The two source Core getter method names are rebound
to their existing extracted `.impl` methods, avoiding the pure field projections
with the same Rust names. No control-flow or primitive implementation is changed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import tomllib

import extract_adapter_record as common
import extract_adapter_seal as source_fixture

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterRatchetKdfExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = [
    "beaconcrypt::ratchet::symmetric_ratchet_hkdf",
    "beaconcrypt::ratchet::ratchet_hkdf",
    "beaconcrypt::ratchet::initial_ratchet_hkdf",
]
PINNED_TOOLS = common.PINNED_TOOLS
PINNED_VERSIONS = common.PINNED_VERSIONS
RUSTFLAGS = common.RUSTFLAGS
GENERATED = common.GENERATED
MODELS = common.MODELS
INSTALLED = common.INSTALLED
LINTERS = source_fixture.LINTERS
POLICY = source_fixture.POLICY
PROFILES = {
    "canonical": "beacon,server,pqxdh",
    "beacon": "beacon,pqxdh",
    "server": "server,pqxdh",
}
BINDER = """variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.CryptoOperations]
variable [BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive.Operations]
"""
INTERFACES = [
    (
        "beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest.input",
        "beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest.impl.input",
    ),
    (
        "beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest.info",
        "beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest.impl.info",
    ),
]
PROOF_ARGUMENTS = [
    (
        '(toStr "HKDF-SHA-512 extract accepts every fixed-width ratchet chain")',
        '(toStr "HKDF-SHA-512 extract accepts every fixed-width ratchet chain" (by simp only [U32.max, U32.numBits]; decide_cbv))',
    ),
    (
        '(toStr\n    "the fixed ratchet output sizes are below the HKDF-SHA-512 limit")',
        '(toStr\n    "the fixed ratchet output sizes are below the HKDF-SHA-512 limit" (by simp only [U32.max, U32.numBits]; decide_cbv))',
    ),
]
RAW_SHA256 = {
    "Types.lean": "2d4994bc3fec987fd7eeb689793a7316c64e3e11240672572a346aa3e3000a50",
    "Funs.lean": "06bcad89719dc400b69bf81fcbc50e00348db575b99f118130c7590e9a5bd36b",
    "TypesExternal_Template.lean": "8523567a9ec3d2416673fd29f4aa75fe72104a375dba090d9d0746e2e9ca447e",
    "FunsExternal_Template.lean": "b73667671f9b9f286555ca76596811457bd785d3fcfcde5cf43f8b34a5b38a2a",
}
SOURCE_FILES = (
    "hax.toml",
    "scripts/extract_adapter_ratchet_kdf.py",
    "scripts/extract_adapter_seal.py",
    "scripts/extract_adapter_record.py",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/TypesExternal.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/PlatformOperations.lean",
)
PLATFORM_SIGNATURES = {
    "CryptoOperations.extract": "Option (Slice U8) -> Slice U8 -> RustM (Result Prk Error); the existing public-adapter operation is reused unchanged",
    "AdapterRatchetKdfPrimitive.expandInto": "Slice U8 -> Option (Slice U8) -> Prk -> RustM (Result Unit Error * Slice U8); failure, divergence and Result.Err remain representable",
    "AdapterRatchetKdfPrimitive.errorDebug": "core.fmt.Debug Error; no formatter execution-totality assumption",
    "SymmetricRatchetKdfRequest.input": "original Core method rebound to existing impl.input: Request -> RustM (Array U8 32)",
    "SymmetricRatchetKdfRequest.info": "original Core method rebound to existing impl.info: Request -> RustM (Array U8 41)",
    "RatchetKdfResponse.from_bytes": "existing extracted Core constructor: Array U8 76 -> RustM Response",
    "Zeroizing": "existing payload wrapper; new/deref retain the payload; no drop or physical-erasure claim",
    "Zeroizing.deref_mut": "Zeroizing T -> RustM (T * (T -> Zeroizing T)); pure write-back wraps the actual replacement",
    "Array.index_mut_RangeFull": "existing CoreModels full-array mutable slice and pure write-back; source-correspondent mutable output length is a separate structural law",
    "Result.expect": "existing CoreModels Result.expect; Err returns represented panic, success ignores the formatter",
    "output_bound": "literal extracted checked multiplication 255 * 64 and massert OUTPUT_SIZE <= bound, retained unchanged",
}
REVIEWED_MODEL_SHA256 = {
    "TypesExternal.lean": "40b0f4c16e7782fc9629055c4a8f5d62945100f21f37d8ea298fcaf08b8ea1fd",
    "FunsExternal.lean": "f567764bb20912fbdb789dd474d5ebf6ebeec230432517e48a2db875b7c58e23",
}
TRANSFORMATION = {
    "warning_header": list(LINTERS),
    "namespace": ["beaconcrypt", "beaconcrypt_ratchet_kdf"],
    "binders": BINDER,
    "source_core_method_interfaces": [list(rule) for rule in INTERFACES],
    "proof_arguments": [list(rule) for rule in PROOF_ARGUMENTS],
    "control_flow_rewrites": [],
    "fixture_rust_rewrites": [],
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def normalize(contents: bytes, name: str) -> bytes:
    if name not in {"Types.lean", "Funs.lean"} or digest(contents) != RAW_SHA256[name]:
        raise ValueError("unreviewed original ratchet KDF wrapper: " + name)
    common.require_model(contents, name)
    text = contents.decode()
    if tuple(re.findall(r"^set_option linter\.(\S+) false$", text, re.M)) != LINTERS:
        raise ValueError("generated warning header changed")
    text = re.sub(r"^set_option linter\.\S+ false\n", "", text, flags=re.M)
    if text.count("open Std.Do\n") != 1 or text.count("namespace beaconcrypt\n") != 1:
        raise ValueError("ratchet KDF namespace/header changed")
    text = text.replace("open Std.Do\n", "open Std.Do\n" + POLICY, 1)
    text = text.replace(
        "namespace beaconcrypt\n",
        "namespace beaconcrypt_ratchet_kdf\n" + (BINDER if name == "Funs.lean" else ""),
        1,
    ).replace("end beaconcrypt\n", "end beaconcrypt_ratchet_kdf\n", 1)
    if name == "Funs.lean":
        for before, after in INTERFACES:
            if text.count(before) != 1 or after in text:
                raise ValueError("source Core getter interface changed")
            text = text.replace(before, after, 1)
        for before, after in PROOF_ARGUMENTS:
            if text.count(before) != 1 or after in text:
                raise ValueError("source string-bound proof argument changed")
            text = text.replace(before, after, 1)
    common.require_handwritten_warning_policy(text.encode(), name)
    return text.encode()


def denormalize(contents: bytes, name: str) -> bytes:
    common.require_handwritten_warning_policy(contents, name)
    text = contents.decode()
    if name == "Funs.lean":
        for before, after in reversed(PROOF_ARGUMENTS):
            if text.count(after) != 1:
                raise ValueError("installed string-bound proof argument changed")
            text = text.replace(after, before, 1)
        for before, after in reversed(INTERFACES):
            if text.count(after) != 1:
                raise ValueError("installed Core getter interface changed")
            text = text.replace(after, before, 1)
    namespace = "namespace beaconcrypt_ratchet_kdf\n" + (
        BINDER if name == "Funs.lean" else ""
    )
    if text.count(namespace) != 1 or text.count("end beaconcrypt_ratchet_kdf\n") != 1:
        raise ValueError("installed ratchet KDF namespace/binders changed")
    text = text.replace(namespace, "namespace beaconcrypt\n", 1).replace(
        "end beaconcrypt_ratchet_kdf\n", "end beaconcrypt\n", 1
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
        raise ValueError("source ratchet KDF wrapper does not round trip")
    return raw


def validate_templates(templates: dict[str, bytes]) -> None:
    expected = {name for name in GENERATED if name.endswith("_Template.lean")}
    if set(templates) != expected:
        raise ValueError("ratchet KDF external template roster changed")
    for name, contents in templates.items():
        if digest(contents) != RAW_SHA256[name]:
            raise ValueError("ratchet KDF external signature changed: " + name)


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in SOURCE_FILES
        },
        "fixture_source_sha256": {
            name: digest(contents)
            for name, contents in source_fixture.source_files(root).items()
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
        **{name: normalize(raw[name], name) for name in ("Types.lean", "Funs.lean")},
        "external-signatures.json": (
            json.dumps(evidence, indent=2, sort_keys=True) + "\n"
        ).encode(),
    }


def commands(
    tools: dict[str, Path], work: Path, profile: str = "canonical"
) -> tuple[list[str], list[str]]:
    if profile not in PROFILES:
        raise ValueError("unreviewed ratchet KDF feature profile: " + profile)
    charon = [
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
        *[
            "--include=" + name
            for name in (
                "core::option::Option",
                "core::result::Result",
                "core::convert::Infallible",
                "core::ops::range::RangeFull",
            )
        ],
        "--dest-file",
        str(work / "beaconcrypt.llbc"),
        "--",
        "-p",
        "beaconcrypt",
        "--lib",
        "--locked",
        "--no-default-features",
        "--features=beacon,server,pqxdh",
    ]
    if profile != "canonical":
        charon[-1] = "--features=" + PROFILES[profile]
    return charon, [
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


def metadata() -> dict:
    return {
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "rust_start_from": START_FROM,
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "feature_profiles": {
            name: {"features": features.split(","), "default_features": False}
            for name, features in PROFILES.items()
        },
        "generated_transformation": TRANSFORMATION,
        "reviewed_model_sha256": REVIEWED_MODEL_SHA256,
    }


def validate_models(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    if set(REVIEWED_MODEL_SHA256) != set(MODELS):
        raise ValueError("unreviewed ratchet KDF model roster")
    for name, expected in REVIEWED_MODEL_SHA256.items():
        if digest((destination / name).read_bytes()) != expected:
            raise ValueError("reviewed ratchet KDF model changed: " + name)


def validate_profile_comparisons(provenance: dict) -> None:
    comparisons = provenance.get("profile_comparisons")
    if not isinstance(comparisons, dict) or set(comparisons) != set(PROFILES):
        raise ValueError("ratchet KDF feature comparison roster changed")
    canonical = comparisons["canonical"]
    for name, value in comparisons.items():
        if set(value) != {"raw_generated_sha256", "normalized_generated_sha256"}:
            raise ValueError("ratchet KDF profile evidence fields changed: " + name)
        common.require_hash_roster(value["raw_generated_sha256"], set(GENERATED), name)
        common.require_hash_roster(
            value["normalized_generated_sha256"], {"Types.lean", "Funs.lean"}, name
        )
        if value != canonical:
            raise ValueError("ratchet KDF feature profile output drift: " + name)
    if canonical["raw_generated_sha256"] != provenance["raw_generated_sha256"]:
        raise ValueError("ratchet KDF canonical raw profile evidence changed")
    if canonical["normalized_generated_sha256"] != {
        name: provenance["installed_sha256"][name]
        for name in ("Types.lean", "Funs.lean")
    }:
        raise ValueError("ratchet KDF canonical installed profile evidence changed")


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    common.validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    validate_models(root, destination)
    provenance = json.loads((destination / "provenance.json").read_bytes())
    expected = (
        set(metadata())
        | set(snapshot(root, destination))
        | {
            "tool_sha256",
            "raw_generated_sha256",
            "installed_sha256",
            "profile_comparisons",
        }
    )
    if set(provenance) != expected:
        raise ValueError("ratchet KDF provenance metadata roster changed")
    for name, value in {**metadata(), **snapshot(root, destination)}.items():
        if provenance[name] != value:
            raise ValueError("ratchet KDF source/model/metadata drift: " + name)
    common.require_hash_roster(provenance["tool_sha256"], set(PINNED_TOOLS), "tools")
    raw = common.require_hash_roster(
        provenance["raw_generated_sha256"], set(GENERATED), "raw"
    )
    installed = common.require_hash_roster(
        provenance["installed_sha256"], set(INSTALLED), "installed"
    )
    for name in INSTALLED:
        contents = (destination / name).read_bytes()
        if digest(contents) != installed[name]:
            raise ValueError("ratchet KDF installed module drift: " + name)
        if name.endswith(".lean") and digest(denormalize(contents, name)) != raw[name]:
            raise ValueError("ratchet KDF raw generated body drift: " + name)
    validate_profile_comparisons(provenance)
    for name in MODELS:
        contents = (destination / name).read_bytes()
        common.require_model(contents, name)
        common.require_handwritten_warning_policy(contents, name)
    evidence = json.loads((destination / "external-signatures.json").read_bytes())
    if (
        set(evidence) != {"templates", "platform_signatures"}
        or evidence["platform_signatures"] != PLATFORM_SIGNATURES
    ):
        raise ValueError("ratchet KDF builtin signature roster changed")
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
            raise ValueError("ratchet KDF external signature evidence drift")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ("write", "check", "check-source"):
        mode.add_argument("--" + name, action="store_true")
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
        print("Original ratchet KDF source, interfaces and all three profiles match")
        return 0
    if args.work_dir is None:
        parser.error("--work-dir is required for fresh extraction")
    if args.work_dir.is_symlink():
        raise ValueError("scratch directory must not be a symlink")
    work = common.isolated_work_directory(args.work_dir)
    if work.exists() and any(work.iterdir()):
        raise ValueError("ratchet KDF extraction scratch directory must be fresh")
    common.validate_work_paths(work)
    common.validate_configuration(tomllib.loads((ROOT / "hax.toml").read_text()))
    validate_models()
    before = snapshot()
    tools = {
        name: args.tools_root / name / version / name
        for name, version in PINNED_TOOLS.items()
    }
    for path in tools.values():
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError("missing pinned executable: " + str(path))
    tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
    work.mkdir(parents=True, exist_ok=True)
    fixture = work / "source"
    source_fixture.prepare_source(ROOT, fixture)
    environment = common.extraction_environment(work)
    environment.update({name.upper(): str(path) for name, path in tools.items()})
    comparisons = {}
    contents = None
    for profile in PROFILES:
        profile_work = work / profile
        profile_work.mkdir()
        for index, command in enumerate(commands(tools, profile_work, profile)):
            source_fixture.run(
                command,
                environment,
                profile_work / ("charon.log" if index == 0 else "aeneas.log"),
                fixture,
            )
        source_fixture.check_fixture(fixture, before["fixture_source_sha256"])
        generated = profile_work / "generated" / SUBDIRECTORY
        selected = assemble(generated)
        if contents is None:
            contents = selected
        elif selected != contents:
            raise ValueError("ratchet KDF normalized feature-profile drift: " + profile)
        comparisons[profile] = {
            "raw_generated_sha256": {
                name: digest((generated / name).read_bytes()) for name in GENERATED
            },
            "normalized_generated_sha256": {
                name: digest(selected[name]) for name in ("Types.lean", "Funs.lean")
            },
        }
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
        raise ValueError("ratchet KDF inputs changed during extraction")
    provenance = {
        **metadata(),
        **before,
        "tool_sha256": tool_hashes,
        "raw_generated_sha256": comparisons["canonical"]["raw_generated_sha256"],
        "installed_sha256": {name: digest(value) for name, value in contents.items()},
        "profile_comparisons": comparisons,
    }
    validate_profile_comparisons(provenance)
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
            raise ValueError("ratchet KDF extraction drift: " + ", ".join(changed))
    print("Original ratchet KDF wrappers freshly agree across all three profiles")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
