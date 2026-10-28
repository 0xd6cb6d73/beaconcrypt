#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Extract the production canonical ordinary-frame codec with pinned tools.

The imported functions are unmodified Charon/Aeneas output. The sole maintained
external file imports the existing core extraction; no opaque codec operation or
parser-correctness hypothesis is introduced. Registration's generated codecs are
outside this extraction.
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
SUBDIRECTORY = "BeaconcryptCore/FrameCodecExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
START_FROM = (
    "beaconcrypt_parse::frame::decode",
    "beaconcrypt_parse::frame::encode_argument",
    "beaconcrypt_parse::frame::encode_three",
)
TOOLS = {"charon": "nightly-2026.09.02", "aeneas": "nightly-2026.09.03-6852e64"}
VERSIONS = {
    "lean": "leanprover/lean4:v4.35.0",
    "hax-lean-lib": "174840bf2f633ae3bae955e08f781b3737ffc0b8",
}
GENERATED = ("Types.lean", "Funs.lean", "FunsExternal_Template.lean")
INSTALLED = ("Types.lean", "Funs.lean", "external-signatures.json")
MODELS = ("FunsExternal.lean",)
RUSTFLAGS = "--cfg hax_compilation --cfg hax_backend_lean"
MODEL_CODE = """import BeaconcryptCore.Extraction.Funs

set_option warningAsError true

noncomputable def beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE :
    Aeneas.Std.RustM Aeneas.Std.Usize :=
  Aeneas.Std.RustM.ok _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE"""
SOURCES = (
    "Cargo.toml",
    "Cargo.lock",
    "hax.toml",
    "beaconcrypt-parse/Cargo.toml",
    "beaconcrypt-parse/src/lib.rs",
    "beaconcrypt-parse/src/frame.rs",
    "beaconcrypt-core/Cargo.toml",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Types.lean",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
    "scripts/extract_frame_codec.py",
)


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def code(contents: bytes) -> str:
    """Remove nested Lean comments and strings without hiding command text."""
    source = contents.decode()
    output = []
    position = 0
    depth = 0
    quoted = False
    line = False
    while position < len(source):
        char, pair = source[position], source[position : position + 2]
        if line:
            output.append("\n" if char == "\n" else " ")
            line = char != "\n"
        elif depth:
            if pair in ("/-", "-/"):
                depth += 1 if pair == "/-" else -1
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
                quoted = char != '"'
        elif pair in ("--", "/-"):
            line, depth = pair == "--", int(pair == "/-")
            output.append("  ")
            position += 1
        elif char == '"':
            quoted = True
            output.append(" ")
        else:
            output.append(char)
        position += 1
    if depth or quoted:
        raise ValueError("unterminated Lean comment or string")
    return "".join(output)


def checked_lean(contents: bytes, name: str) -> None:
    source = code(contents)
    if re.search(r"\b(?:sorry|admit|axiom|sorryAx|opaque|unsafe)\b|#check", source):
        raise ValueError(f"unchecked declaration in {name}")


def checked_template(contents: bytes) -> None:
    """The production decoder and argument encoder have no opaque operations."""
    source = code(contents)
    if re.search(
        r"\b(?:axiom|opaque|constant|def|abbrev|theorem|structure|inductive|class|instance)\b",
        source,
    ):
        raise ValueError("frame codec extraction has an unexpected external obligation")
    checked_lean(contents, "external template")


def sources(root: Path) -> list[str]:
    return sorted(
        [*SOURCES]
        + [
            p.relative_to(root).as_posix()
            for p in (root / "beaconcrypt-core/src").rglob("*.rs")
        ]
        + [
            p.relative_to(root).as_posix()
            for p in (root / "beaconcrypt-parse/src/generated").rglob("*.rs")
        ]
    )


def snapshot(root: Path = ROOT, destination: Path = DESTINATION) -> dict:
    return {
        "source_sha256": {
            name: digest((root / name).read_bytes()) for name in sources(root)
        },
        "model_sha256": {
            name: digest((destination / name).read_bytes()) for name in MODELS
        },
    }


def isolated_work(path: Path, root: Path = ROOT) -> Path:
    work, root = path.resolve(), root.resolve()
    if work == root or root in work.parents or work in root.parents:
        raise ValueError("--work-dir must be outside the source checkout")
    # A reused scratch tree must not send generated outputs into another tree.
    if work.exists():
        for parent, directories, files in os.walk(work, followlinks=False):
            for name in directories + files:
                candidate = Path(parent) / name
                if candidate.is_symlink():
                    raise ValueError(
                        f"symbolic link in extraction work directory: {candidate}"
                    )
    return work


def configuration(root: Path = ROOT) -> None:
    value = tomllib.loads((root / "hax.toml").read_text())
    if value.get("tools") != TOOLS or value.get("versions") != VERSIONS:
        raise ValueError("frame codec tool pins differ from the reviewed extraction")


def assembled(generated: Path) -> dict[str, bytes]:
    raw = {name: (generated / name).read_bytes() for name in GENERATED}
    for name in ("Types.lean", "Funs.lean"):
        checked_lean(raw[name], name)
    checked_template(raw["FunsExternal_Template.lean"])
    for name in (
        "frame.decode",
        "frame.decode_argument",
        "frame.encode_argument",
        "frame.write_argument",
        "frame.write_header",
        "frame.encode_three",
    ):
        if (
            len(
                re.findall(
                    r"^def " + re.escape(name) + r"\b",
                    raw["Funs.lean"].decode(),
                    re.MULTILINE,
                )
            )
            != 1
        ):
            raise ValueError(f"missing or duplicate generated codec function: {name}")
    return {
        "Types.lean": raw["Types.lean"],
        "Funs.lean": raw["Funs.lean"],
        "external-signatures.json": (
            json.dumps(
                {
                    "FunsExternal_Template.lean": {
                        "sha256": digest(raw["FunsExternal_Template.lean"]),
                        "source": raw["FunsExternal_Template.lean"].decode(),
                    }
                },
                indent=2,
                sort_keys=True,
            )
            + "\n"
        ).encode(),
    }


def hash_roster(value: object, expected: set[str], label: str) -> dict:
    if not isinstance(value, dict) or set(value) != expected:
        raise ValueError(f"unexpected {label} roster")
    if any(
        not isinstance(x, str) or not re.fullmatch(r"[0-9a-f]{64}", x)
        for x in value.values()
    ):
        raise ValueError(f"malformed {label} digest")
    return value


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    configuration(root)
    provenance = json.loads((destination / "provenance.json").read_bytes())
    metadata = {
        "tools": TOOLS,
        "versions": VERSIONS,
        "rust_start_from": list(START_FROM),
        "charon_sysroot": "default",
        "rustflags": RUSTFLAGS,
        "lean_namespace": "beaconcrypt_parse",
        "generated_transformation": None,
    }
    for name, value in metadata.items():
        if provenance.get(name) != value:
            raise ValueError(f"unexpected frame codec provenance {name}")
    current = snapshot(root, destination)
    for name, hashes in current.items():
        if hash_roster(provenance.get(name), set(hashes), name) != hashes:
            raise ValueError(f"frame codec {name} drift")
    hash_roster(provenance.get("tool_sha256"), set(TOOLS), "tool_sha256")
    raw = hash_roster(
        provenance.get("raw_generated_sha256"), set(GENERATED), "raw_generated_sha256"
    )
    installed = hash_roster(
        provenance.get("installed_sha256"), set(INSTALLED), "installed_sha256"
    )
    for name in INSTALLED:
        if digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError(f"frame codec installed file drift: {name}")
    for name in ("Types.lean", "Funs.lean"):
        value = (destination / name).read_bytes()
        checked_lean(value, name)
        if digest(value) != raw[name]:
            raise ValueError(f"frame codec generator body drift: {name}")
    for name in MODELS:
        value = (destination / name).read_bytes()
        checked_lean(value, name)
        if " ".join(code(value).split()) != " ".join(MODEL_CODE.split()):
            raise ValueError(
                "frame codec external model must only import the existing extraction"
            )
    evidence = json.loads((destination / "external-signatures.json").read_bytes())
    if not isinstance(evidence, dict) or set(evidence) != {
        "FunsExternal_Template.lean"
    }:
        raise ValueError("unexpected frame codec external template roster")
    item = evidence["FunsExternal_Template.lean"]
    if (
        not isinstance(item, dict)
        or set(item) != {"sha256", "source"}
        or not isinstance(item["source"], str)
    ):
        raise ValueError("malformed frame codec external template evidence")
    if (
        digest(item["source"].encode()) != item["sha256"]
        or item["sha256"] != raw["FunsExternal_Template.lean"]
    ):
        raise ValueError("frame codec external template evidence drift")
    checked_template(item["source"].encode())


def pipeline(tools: dict[str, Path], work: Path) -> Path:
    work = isolated_work(work)
    generated = work / "generated"
    destination = generated / SUBDIRECTORY
    destination.mkdir(parents=True, exist_ok=True)
    for name in GENERATED:
        (destination / name).unlink(missing_ok=True)
    llbc = work / "beaconcrypt_parse.llbc"
    llbc.unlink(missing_ok=True)
    environment = dict(os.environ)
    environment.pop("CARGO_ENCODED_RUSTFLAGS", None)
    environment.update(
        CARGO_TARGET_DIR=str(work / "target"), CARGO_BUILD_JOBS="2", RUSTFLAGS=RUSTFLAGS
    )
    commands = (
        [
            str(tools["charon"]),
            "cargo",
            "--preset=aeneas",
            "--sysroot=default",
            *("--start-from=" + name for name in START_FROM),
            "--opaque=beaconcrypt_core",
            "--dest-file",
            str(llbc),
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
            str(llbc),
            "-dest",
            str(generated),
            "-subdir",
            SUBDIRECTORY,
        ],
    )
    for name, command in zip(("charon", "aeneas"), commands):
        with (work / (name + ".log")).open("w") as output:
            output.write("Command: " + repr(command) + "\n")
            output.flush()
            result = subprocess.run(
                command, cwd=ROOT, env=environment, stdout=output, stderr=output
            )
        if result.returncode:
            raise RuntimeError(f"{name} failed; inspect {work / (name + '.log')}")
        isolated_work(work)
        if not llbc.is_file() or not llbc.stat().st_size:
            raise ValueError("Charon returned without fresh nonempty LLBC")
    return destination


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-source", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument(
        "--tools-root",
        type=Path,
        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
        / "hax/tools",
    )
    args = parser.parse_args()
    if not args.check_source and args.work_dir is None:
        parser.error("--work-dir is required for extraction")
    try:
        if args.check_source:
            check_source()
            print("Frame codec source, models, and generated evidence match")
            return 0
        configuration()
        tools = {
            name: args.tools_root / name / version / name
            for name, version in TOOLS.items()
        }
        for tool in tools.values():
            if not tool.is_file() or not os.access(tool, os.X_OK):
                raise ValueError(f"missing pinned executable: {tool}")
        before = snapshot()
        tool_hashes = {name: digest(path.read_bytes()) for name, path in tools.items()}
        generated = pipeline(tools, args.work_dir)
        contents = assembled(generated)
        provenance = {
            "tools": TOOLS,
            "versions": VERSIONS,
            "tool_sha256": tool_hashes,
            "rust_start_from": list(START_FROM),
            "charon_sysroot": "default",
            "rustflags": RUSTFLAGS,
            "lean_namespace": "beaconcrypt_parse",
            "generated_transformation": None,
            "raw_generated_sha256": {
                name: digest((generated / name).read_bytes()) for name in GENERATED
            },
            "installed_sha256": {
                name: digest(value) for name, value in contents.items()
            },
            **before,
        }
        if before != snapshot() or tool_hashes != {
            name: digest(path.read_bytes()) for name, path in tools.items()
        }:
            raise ValueError("frame codec extraction inputs changed during the run")
        contents["provenance.json"] = (
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        ).encode()
        if args.write:
            for name, value in contents.items():
                (DESTINATION / name).write_bytes(value)
            print(
                "Wrote frame codec extraction and provenance; generated functions are unchanged"
            )
        else:
            changed = [
                name
                for name, value in contents.items()
                if not (DESTINATION / name).is_file()
                or (DESTINATION / name).read_bytes() != value
            ]
            if changed:
                raise ValueError("frame codec extraction drift: " + ", ".join(changed))
            print("Frame codec extraction and provenance match the pinned generator")
        return 0
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
