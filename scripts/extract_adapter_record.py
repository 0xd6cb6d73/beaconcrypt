#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Regenerate the selected production adapter driver with pinned Charon/Aeneas.

All compiler outputs stay in --work-dir, outside the checkout. The sole change
to generated Lean is an explicit Operations instance binder; primitive models
and core aliases remain maintained files, never generated placeholder proofs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
SUBDIRECTORY = "BeaconcryptCore/AdapterRecordExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = "beaconcrypt::ratchet::execute_record_receive"
PINNED_TOOLS = {
    "aeneas": "nightly-2026.09.03-6852e64",
    "charon": "nightly-2026.09.02",
}
PINNED_VERSIONS = {
    "lean": "leanprover/lean4:v4.35.0",
    "hax-lean-lib": "174840bf2f633ae3bae955e08f781b3737ffc0b8",
}
GENERATED = (
    "Types.lean",
    "Funs.lean",
    "TypesExternal_Template.lean",
    "FunsExternal_Template.lean",
)
MODELS = ("TypesExternal.lean", "FunsExternal.lean")
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
SOURCE_FILES = (
    "Cargo.toml",
    "Cargo.lock",
    "hax.toml",
    "beaconcrypt/Cargo.toml",
    "beaconcrypt/src/ratchet.rs",
    "beaconcrypt/src/shared.rs",
    "beaconcrypt-crypto/src/lib.rs",
    "beaconcrypt-crypto/src/crypto_generichash.rs",
    "beaconcrypt-crypto/src/crypto_aead.rs",
    "beaconcrypt-crypto/src/crypto_kdf.rs",
    "beaconcrypt/src/lib.rs",
    "beaconcrypt-core/Cargo.toml",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "scripts/extract_adapter_record.py",
)
BINDER = "variable [beaconcrypt.ratchet.Operations]\n"
RUSTFLAGS = "--cfg hax_compilation --cfg hax_backend_lean"
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|sorryAx|opaque)\b|#check")
EXTERNAL_SIGNATURES = {
    "ratchet.ratchet_hkdf": "beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → RustM "
    "beaconcrypt_core.ratchet.RatchetKdfResponse",
    "ratchet.execute_commitment_hash": "beaconcrypt_core.commitment.CommitmentTranscript → RustM "
    "((core.option.Option (Array Std.U8 64#usize)) × beaconcrypt_core.commitment.CommitmentTranscript)",
    "ratchet.execute_open_request": "core.option.Option beaconcrypt_core.record.AeadRequest → RustM "
    "(core.option.Option (alloc.vec.Vec Std.U8))",
}
TEMPLATE_DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|unsafe|noncomputable)\s+)*"
    r"(axiom|opaque|constant|def|abbrev|theorem|structure|inductive|class|instance)\b",
    re.MULTILINE,
)


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def validate_configuration(configuration: dict) -> None:
    if configuration.get("tools") != PINNED_TOOLS:
        raise ValueError("hax.toml tool pins differ from the reviewed extraction")
    if configuration.get("versions") != PINNED_VERSIONS:
        raise ValueError("hax.toml library pins differ from the reviewed extraction")


def require_model(contents: bytes, name: str) -> None:
    if FORBIDDEN.search(contents.decode("utf-8")):
        raise ValueError(f"{name} contains an unchecked external obligation")


def lean_code_without_comments_or_strings(contents: bytes) -> str:
    """Keep command text while ignoring quoted text and nested Lean comments."""
    source = contents.decode("utf-8")
    output = []
    position = 0
    block_depth = 0
    line_comment = False
    quoted = False
    while position < len(source):
        char = source[position]
        pair = source[position : position + 2]
        if line_comment:
            output.append("\n" if char == "\n" else " ")
            line_comment = char != "\n"
        elif block_depth:
            if pair in ("/-", "-/"):
                block_depth += 1 if pair == "/-" else -1
                output.append("  ")
                position += 1
            else:
                output.append("\n" if char == "\n" else " ")
        elif quoted:
            if char == "\\" and position + 1 < len(source):
                output.append("  ")
                position += 1
            else:
                output.append("\n" if char == "\n" else " ")
                if char == '"':
                    quoted = False
        elif pair in ("--", "/-"):
            line_comment = pair == "--"
            block_depth = int(pair == "/-")
            output.append("  ")
            position += 1
        elif char == '"':
            quoted = True
            output.append(" ")
        else:
            output.append(char)
        position += 1
    return "".join(output)


def require_handwritten_warning_policy(contents: bytes, name: str) -> None:
    code = lean_code_without_comments_or_strings(contents)
    settings = re.findall(r"\bset_option\s+warningAsError\s+(\w+)\b", code)
    global_setting = re.findall(
        r"^[ \t]*set_option[ \t]+warningAsError[ \t]+true[ \t]*$",
        code,
        flags=re.MULTILINE,
    )
    if settings != ["true"] or len(global_setting) != 1:
        raise ValueError(f"{name} must set warningAsError true exactly once")
    if re.search(r"\bset_option\s+linter(?:\.[A-Za-z0-9_]+)*\s+false\b", code):
        raise ValueError(f"{name} disables handwritten Lean warnings")


def check_handwritten_warning_policy(destination: Path) -> None:
    handwritten = {name: destination / name for name in MODELS} | {
        "Refinement/AdapterRecordReceive.lean": destination.parent
        / "Refinement/AdapterRecordReceive.lean"
    }
    for name, path in handwritten.items():
        require_handwritten_warning_policy(path.read_bytes(), name)


def validate_external_templates(templates: dict[str, bytes]) -> None:
    """The maintained models implement only the three local foreign signatures."""
    expected_names = {name for name in GENERATED if name.endswith("_Template.lean")}
    if set(templates) != expected_names:
        raise ValueError("unexpected external-template roster")
    sources = {}
    for name, contents in templates.items():
        source = re.sub(r"/-.*?-/", "", contents.decode(), flags=re.DOTALL)
        sources[name] = re.sub(r"--[^\n]*", "", source)
    if TEMPLATE_DECLARATION.search(sources["TypesExternal_Template.lean"]):
        raise ValueError("unexpected external type declaration")
    source = sources["FunsExternal_Template.lean"]
    declarations = list(TEMPLATE_DECLARATION.finditer(source))
    if len(declarations) != len(EXTERNAL_SIGNATURES):
        raise ValueError("unexpected external function declaration roster")
    signatures = {}
    for index, declaration in enumerate(declarations):
        stop = (
            declarations[index + 1].start()
            if index + 1 < len(declarations)
            else len(source)
        )
        body = source[declaration.end() : stop]
        signature = re.fullmatch(r"\s+([A-Za-z0-9_.]+)\s*:\s*(.+?)\s*", body, re.DOTALL)
        if declaration.group(1) != "axiom" or signature is None:
            raise ValueError("malformed external function declaration")
        name, value = signature.groups()
        if name in signatures:
            raise ValueError("duplicate external function declaration")
        signatures[name] = " ".join(value.split())
    if signatures != EXTERNAL_SIGNATURES:
        raise ValueError(
            "external signatures do not match the maintained primitive models"
        )


def bind_operations(contents: bytes) -> bytes:
    text = contents.decode("utf-8")
    namespace = "namespace beaconcrypt\n"
    if text.count(namespace) != 1 or BINDER in text:
        raise ValueError("expected one unmodified beaconcrypt namespace")
    if (
        len(re.findall(r"^def ratchet\.execute_record_receive\b", text, re.MULTILINE))
        != 1
    ):
        raise ValueError("expected exactly one extracted receive driver")
    require_model(contents, "generated Funs.lean")
    return text.replace(namespace, namespace + "\n" + BINDER, 1).encode("utf-8")


def unbind_operations(contents: bytes) -> bytes:
    insertion = ("namespace beaconcrypt\n\n" + BINDER).encode()
    if contents.count(insertion) != 1 or contents.count(BINDER.encode()) != 1:
        raise ValueError("expected exactly one Operations binder at the namespace")
    raw = contents.replace(insertion, b"namespace beaconcrypt\n", 1)
    if bind_operations(raw) != contents:
        raise ValueError("installed driver is not the binder-only transformation")
    return raw


def commands(charon: Path, aeneas: Path, work: Path) -> tuple[list[str], list[str]]:
    charon_command = [
        str(charon),
        "cargo",
        "--preset=aeneas",
        "--sysroot=default",
        "--start-from=" + START_FROM,
        "--opaque=beaconcrypt_core",
        "--include=beaconcrypt_core::record_effects::RecordReceiveEffect",
        "--include=beaconcrypt_core::record::OpenedRecord",
        "--opaque=beaconcrypt::ratchet::ratchet_hkdf",
        "--opaque=beaconcrypt::ratchet::execute_commitment_hash",
        "--opaque=beaconcrypt::ratchet::execute_open_request",
        "--opaque=beaconcrypt_crypto::utils::memcmp",
        "--dest-file",
        str(work / "beaconcrypt.llbc"),
        "--",
        "-p",
        "beaconcrypt",
        "--lib",
        "--locked",
        "--no-default-features",
        "--features=beacon,pqxdh",
    ]
    aeneas_command = [
        str(aeneas),
        "-backend",
        "lean",
        "-core-models-lib",
        "-split-files",
        "-specs",
        "hax",
        str(work / "beaconcrypt.llbc"),
        "-dest",
        str(work / "generated"),
        "-subdir",
        SUBDIRECTORY,
    ]
    return charon_command, aeneas_command


def isolated_work_directory(path: Path, root: Path = ROOT) -> Path:
    work = path.resolve()
    root = root.resolve()
    if work == root or root in work.parents or work in root.parents:
        raise ValueError("--work-dir must be outside the source checkout")
    return work


def validate_work_paths(work: Path) -> None:
    """Do not follow a reused scratch directory's links into another tree."""
    work = isolated_work_directory(work)
    generated = work / "generated"
    target = work / "target"
    paths = [
        generated,
        target,
        work / "beaconcrypt.llbc",
        work / "charon.log",
        work / "aeneas.log",
        generated / SUBDIRECTORY,
        *(generated / SUBDIRECTORY / name for name in GENERATED),
    ]
    for directory in (generated, target):
        if directory.is_symlink():
            raise ValueError(
                f"scratch output directory is a symbolic link: {directory}"
            )
        if directory.is_dir() and not directory.is_symlink():
            for parent, directories, files in os.walk(directory, followlinks=False):
                for name in directories:
                    if (Path(parent) / name).is_symlink():
                        raise ValueError(
                            f"scratch output directory is a symbolic link: {Path(parent) / name}"
                        )
                paths.extend(
                    candidate
                    for name in directories + files
                    if (candidate := Path(parent) / name).is_symlink()
                )
    for path in paths:
        resolved = path.resolve()
        if resolved != work and work not in resolved.parents:
            raise ValueError(f"scratch output escapes the work directory: {path}")


def extraction_environment(
    work: Path, inherited: dict[str, str] | None = None
) -> dict[str, str]:
    environment = dict(os.environ if inherited is None else inherited)
    # Cargo gives this encoded variable precedence over RUSTFLAGS.
    environment.pop("CARGO_ENCODED_RUSTFLAGS", None)
    environment.update(
        CARGO_TARGET_DIR=str(work / "target"),
        CARGO_BUILD_JOBS="2",
        RUSTFLAGS=RUSTFLAGS,
    )
    return environment


def source_paths(root: Path = ROOT) -> list[str]:
    return sorted(
        [*SOURCE_FILES]
        + [
            path.relative_to(root).as_posix()
            for path in (root / "beaconcrypt-core/src").rglob("*.rs")
        ]
    )


def snapshot_inputs(
    root: Path = ROOT,
    destination: Path = DESTINATION,
    tools: dict[str, Path] | None = None,
) -> dict[str, dict[str, str]]:
    snapshot = {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in source_paths(root)
        },
        "model_sha256": {
            name: digest((destination / name).read_bytes()) for name in MODELS
        },
    }
    if tools is not None:
        snapshot["tool_sha256"] = {
            name: digest(path.read_bytes()) for name, path in tools.items()
        }
    return snapshot


def require_unchanged_inputs(before: dict, after: dict) -> None:
    if before != after:
        changed = [
            name
            for name in before.keys() | after.keys()
            if before.get(name) != after.get(name)
        ]
        raise ValueError(
            "extraction inputs changed during the run: " + ", ".join(sorted(changed))
        )


def run_logged(command: list[str], environment: dict[str, str], log: Path) -> None:
    with log.open("w") as output:
        output.write("Command: " + repr(command) + "\n")
        output.flush()
        result = subprocess.run(
            command, cwd=ROOT, env=environment, stdout=output, stderr=output
        )
    if result.returncode:
        raise RuntimeError(f"extraction exited {result.returncode}; inspect {log}")


def run_pipeline(
    charon: Path, aeneas: Path, work: Path, environment: dict[str, str]
) -> Path:
    validate_work_paths(work)
    generated = work / "generated" / SUBDIRECTORY
    generated.mkdir(parents=True, exist_ok=True)
    for name in GENERATED:
        (generated / name).unlink(missing_ok=True)
    llbc = work / "beaconcrypt.llbc"
    llbc.unlink(missing_ok=True)
    charon_command, aeneas_command = commands(charon, aeneas, work)
    run_logged(charon_command, environment, work / "charon.log")
    if not llbc.is_file() or llbc.is_symlink() or llbc.stat().st_size == 0:
        raise RuntimeError("Charon returned without a fresh nonempty LLBC artifact")
    validate_work_paths(work)
    run_logged(aeneas_command, environment, work / "aeneas.log")
    validate_work_paths(work)
    return generated


def require_reviewed_signatures(
    generated: bytes, baseline: bytes | None, *, write: bool, review: bool
) -> None:
    if review and not write:
        raise ValueError("--review-external-signatures is allowed only with --write")
    if generated != baseline and not review:
        state = "changed" if baseline is not None else "have no reviewed baseline"
        raise ValueError(
            f"external signatures {state}; inspect the generated templates, then "
            "use --write --review-external-signatures to record a reviewed change"
        )


def assemble(generated: Path, models: dict[str, bytes]) -> dict[str, bytes]:
    for name in MODELS:
        require_model(models[name], name)
    raw = {name: (generated / name).read_bytes() for name in GENERATED}
    require_model(raw["Types.lean"], "generated Types.lean")
    validate_external_templates(
        {name: raw[name] for name in GENERATED if name.endswith("_Template.lean")}
    )
    # Raw external templates are evidence, not Lean import targets. Preserve them
    # as JSON strings so placeholder declarations can never enter a Lean build.
    templates = {
        name: {"sha256": digest(raw[name]), "source": raw[name].decode("utf-8")}
        for name in GENERATED
        if name.endswith("_Template.lean")
    }
    return {
        "Types.lean": raw["Types.lean"],
        "Funs.lean": bind_operations(raw["Funs.lean"]),
        "external-signatures.json": (
            json.dumps(templates, indent=2, sort_keys=True) + "\n"
        ).encode(),
    }


def build_provenance(
    generated: Path, snapshot: dict, contents: dict[str, bytes]
) -> dict:
    return {
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "tool_sha256": snapshot["tool_sha256"],
        "rust_start_from": START_FROM,
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "lean_namespace": "beaconcrypt",
        "generated_transformation": {
            "insert_after": "namespace beaconcrypt\n",
            "text": "\n" + BINDER,
        },
        "raw_generated_sha256": {
            name: digest((generated / name).read_bytes()) for name in GENERATED
        },
        "model_sha256": snapshot["model_sha256"],
        "source_sha256": snapshot["source_sha256"],
        "installed_sha256": {name: digest(value) for name, value in contents.items()},
    }


def require_hash_roster(
    value: object, expected: set[str], label: str
) -> dict[str, str]:
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError(f"unexpected {label} roster")
    if any(
        not isinstance(item, str) or not re.fullmatch(r"[0-9a-f]{64}", item)
        for item in value.values()
    ):
        raise ValueError(f"invalid {label} digest")
    return value


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    """Validate committed evidence without loading tools or running extraction."""
    validate_configuration(tomllib.loads((root / "hax.toml").read_text()))
    check_handwritten_warning_policy(destination)
    provenance = json.loads((destination / "provenance.json").read_bytes())
    if not isinstance(provenance, dict):
        raise ValueError("provenance must be an object")
    expected_metadata = {
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "rust_start_from": START_FROM,
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "lean_namespace": "beaconcrypt",
        "generated_transformation": {
            "insert_after": "namespace beaconcrypt\n",
            "text": "\n" + BINDER,
        },
    }
    for name, value in expected_metadata.items():
        if provenance.get(name) != value:
            raise ValueError(f"unexpected provenance {name}")
    current = snapshot_inputs(root, destination)
    for name, hashes in current.items():
        recorded = require_hash_roster(provenance.get(name), set(hashes), name)
        if recorded != hashes:
            raise ValueError(f"adapter record {name} drift")
    require_hash_roster(provenance.get("tool_sha256"), set(PINNED_TOOLS), "tool_sha256")
    raw_hashes = require_hash_roster(
        provenance.get("raw_generated_sha256"), set(GENERATED), "raw_generated_sha256"
    )
    installed_hashes = require_hash_roster(
        provenance.get("installed_sha256"), set(INSTALLED), "installed_sha256"
    )
    installed = {name: (destination / name).read_bytes() for name in INSTALLED}
    if installed_hashes != {
        name: digest(contents) for name, contents in installed.items()
    }:
        raise ValueError("adapter record installed_sha256 drift")
    for name in MODELS:
        require_model((destination / name).read_bytes(), name)
    require_model(installed["Types.lean"], "installed Types.lean")
    raw_driver = unbind_operations(installed["Funs.lean"])
    if digest(raw_driver) != raw_hashes["Funs.lean"]:
        raise ValueError("raw driver body differs from the recorded generator output")
    if digest(installed["Types.lean"]) != raw_hashes["Types.lean"]:
        raise ValueError("raw types differ from the recorded generator output")
    signatures = json.loads(installed["external-signatures.json"])
    template_names = {name for name in GENERATED if name.endswith("_Template.lean")}
    if not isinstance(signatures, dict) or set(signatures) != template_names:
        raise ValueError("unexpected external-signature evidence roster")
    for name, evidence in signatures.items():
        if not isinstance(evidence, dict) or set(evidence) != {"sha256", "source"}:
            raise ValueError(f"malformed external-signature evidence: {name}")
        if not isinstance(evidence["source"], str):
            raise ValueError(f"invalid external-signature source: {name}")
        if (
            digest(evidence["source"].encode()) != evidence["sha256"]
            or evidence["sha256"] != raw_hashes[name]
        ):
            raise ValueError(f"external-signature evidence drift: {name}")
    validate_external_templates(
        {name: evidence["source"].encode() for name, evidence in signatures.items()}
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-source", action="store_true")
    parser.add_argument("--review-external-signatures", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument(
        "--tools-root",
        type=Path,
        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
        / "hax/tools",
    )
    args = parser.parse_args()
    if args.review_external_signatures and not args.write:
        parser.error("--review-external-signatures is allowed only with --write")
    if not args.check_source and args.work_dir is None:
        parser.error("--work-dir is required for extraction")
    try:
        if args.check_source:
            check_source()
            print("Adapter record source, models, and generated evidence match")
            return 0
        validate_configuration(tomllib.loads((ROOT / "hax.toml").read_text()))
        work = isolated_work_directory(args.work_dir)
        tools = {
            name: args.tools_root / name / version / name
            for name, version in PINNED_TOOLS.items()
        }
        for tool in tools.values():
            if not tool.is_file() or not os.access(tool, os.X_OK):
                raise ValueError(f"missing pinned executable: {tool}")
        before = snapshot_inputs(tools=tools)
        models = {name: (DESTINATION / name).read_bytes() for name in MODELS}
        for name, contents in models.items():
            require_model(contents, name)
        work.mkdir(parents=True, exist_ok=True)
        environment = extraction_environment(work)
        generated = run_pipeline(tools["charon"], tools["aeneas"], work, environment)
        contents = assemble(generated, models)
        baseline_path = DESTINATION / "external-signatures.json"
        require_reviewed_signatures(
            contents["external-signatures.json"],
            baseline_path.read_bytes() if baseline_path.is_file() else None,
            write=args.write,
            review=args.review_external_signatures,
        )
        provenance = build_provenance(generated, before, contents)
        contents["provenance.json"] = (
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        ).encode()
        require_unchanged_inputs(before, snapshot_inputs(tools=tools))
        if args.write:
            for name, value in contents.items():
                (DESTINATION / name).write_bytes(value)
            print(
                f"Wrote {len(contents)} adapter extraction/evidence files; "
                "maintained models preserved"
            )
            return 0
        changed = [
            name
            for name, value in contents.items()
            if not (DESTINATION / name).is_file()
            or (DESTINATION / name).read_bytes() != value
        ]
        if changed:
            print(
                "Adapter record extraction drift: " + ", ".join(changed),
                file=sys.stderr,
            )
            return 1
        print("Adapter record extraction and provenance match the pinned generator")
        return 0
    except (OSError, ValueError, RuntimeError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
