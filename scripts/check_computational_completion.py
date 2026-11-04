#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the explicit computational-completion proof and source-control roster.

The reviewed inventory binds every file's contents. This additional roster pins
the imported modules, declarations, complete dependency guards and source gates.
The Lean kernel checks the named endpoint proofs; this control only verifies their reviewed source and dependency roster.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("beaconcrypt-core/proofs/lean/computational-completion.json")
LEAN_ROOT = Path("beaconcrypt-core/proofs/lean/BeaconcryptCore.lean")
DECLARATION = re.compile(
    r"^(?:@\[[^\n]+\][ \t]*)?(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma)\s+[^\s(:]+",
    re.MULTILINE,
)
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|sorryAx)\b|^\s*axiom\b|"
    r"set_option\s+(?:warningAsError\s+false|linter\.)|"
    r"#guard_msgs\s*\([^)]*drop\s+(?:error|warning)",
    re.MULTILINE,
)


SOURCE_VALUE_GUARD_PATH = (
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/"
    "RegistrationNativeSourceExecutionDependencyGuards.lean"
)
NEGATIVE_SOURCE_VALUE_GUARD = (
    "/-- error: source endpoint "
    "BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build "
    "does not reach source proof "
    "BeaconcryptCore.Refinement.AdapterSealNative.source_native "
    "through declaration values -/\n"
    "#guard_msgs in\n"
    "#guard_source_value_dependencies RegistrationNativePlatformSourceSeal.build "
    "includes [BeaconcryptCore.Refinement.AdapterSealNative.source_native]"
)


def negative_source_guard(root: str, proof: str, proof_name: str) -> str:
    """Construct the exact reviewed diagnostic and its one failing command."""
    return (
        "/-- error: source endpoint BeaconcryptCore.Computational."
        + root
        + " does not reach source proof "
        + proof
        + " through declaration values -/\n#guard_msgs in\n"
        + "#guard_source_value_dependencies "
        + root
        + " includes ["
        + proof_name
        + "]"
    )


BRANCH_GUARD_DIRECTORY = "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/"
REVIEWED_NEGATIVE_SOURCE_GUARDS = {
    SOURCE_VALUE_GUARD_PATH: NEGATIVE_SOURCE_VALUE_GUARD,
    BRANCH_GUARD_DIRECTORY
    + "RegistrationNativePlatformPublicAdapterFinishObservedSourceGuards.lean": negative_source_guard(
        "RegistrationNativePlatformPublicAdapterFinishSourceLogProgram.program_erase",
        "BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.source",
        "BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.source",
    ),
    BRANCH_GUARD_DIRECTORY
    + "RegistrationNativePlatformPublicAdapterBundleObservedSourceGuards.lean": negative_source_guard(
        "RegistrationNativePlatformPublicAdapterBundleLoggedSource.call_erase",
        "BeaconcryptCore.Computational."
        "RegistrationNativePlatformPublicAdapterBundleObservedBody.source",
        "RegistrationNativePlatformPublicAdapterBundleObservedBody.source",
    ),
    BRANCH_GUARD_DIRECTORY
    + "RegistrationNativePlatformPublicAdapterBuildObservedSourceGuards.lean": negative_source_guard(
        "RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_normalized_source",
        "BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.source",
        "BeaconcryptCore.Refinement.AdapterPublicServerBuildObservedBody.source",
    ),
}


def fail(message: str) -> None:
    raise ValueError(message)


def read_manifest(root: Path = ROOT) -> dict:
    value = json.loads((root / MANIFEST).read_text())
    if set(value) != {"version", "artifacts", "sourceChecks", "tests"}:
        fail("unexpected computational-completion manifest fields")
    if value["version"] != 1:
        fail("unsupported computational-completion manifest version")
    return value


def checked_path(root: Path, name: str) -> Path:
    relative = Path(name)
    if relative.is_absolute() or ".." in relative.parts:
        fail(f"nonlocal roster path: {name}")
    path = root / relative
    if path.is_symlink() or not path.is_file():
        fail(f"missing or symbolic-link roster artifact: {name}")
    return path


def guard_blocks(text: str) -> list[str]:
    # Start at the final documentation comment immediately before each guard.
    # Restricting the match to a single comment prevents one guard from hiding
    # unguarded print commands or another theorem's expected dependency output.
    return re.findall(
        r"/-- info: (?:(?!-/).)* -/\s*#guard_msgs in\s*#print axioms [^\n]+",
        text,
        re.DOTALL,
    )


def check_roster(root: Path = ROOT, manifest: dict | None = None) -> None:
    manifest = read_manifest(root) if manifest is None else manifest
    entries = manifest["artifacts"]
    paths = [entry["path"] for entry in entries]
    if paths != sorted(set(paths)):
        fail("artifact roster must be sorted and unique")
    imports = (root / LEAN_ROOT).read_text().splitlines()
    for entry in entries:
        if set(entry) != {"path", "category", "declarations", "guards"}:
            fail(f"unexpected artifact fields: {entry.get('path')}")
        name = entry["path"]
        text = checked_path(root, name).read_text()
        if entry["category"] not in {
            "generated-lean",
            "handwritten-lean",
            "lean-control",
            "validation",
        }:
            fail(f"invalid artifact category: {name}")
        if not name.endswith(".lean"):
            if entry["declarations"] or entry["guards"]:
                fail(f"non-Lean artifact contains a theorem roster: {name}")
            continue
        module = name.removeprefix("beaconcrypt-core/proofs/lean/")
        module = module.removesuffix(".lean").replace("/", ".")
        if imports.count(f"import {module}") != 1:
            fail(f"missing or duplicate verification-root import: {module}")
        if text.splitlines().count("set_option warningAsError true") != 1:
            fail(f"strict warnings missing or duplicated: {name}")
        if FORBIDDEN.search(text):
            fail(f"placeholder or warning/error suppression: {name}")
        if DECLARATION.findall(text) != entry["declarations"]:
            fail(f"theorem declaration roster changed: {name}")
        blocks = guard_blocks(text)
        if blocks != entry["guards"]:
            fail(f"exact guarded dependency roster changed: {name}")
        if len(blocks) != len(re.findall(r"^#print axioms ", text, re.MULTILINE)):
            fail(f"unguarded dependency output: {name}")
        reviewed_negative = REVIEWED_NEGATIVE_SOURCE_GUARDS.get(name)
        negative_guards = text.count(reviewed_negative) if reviewed_negative else 0
        if negative_guards > 1:
            fail(f"duplicate source dependency negative control: {name}")
        if len(blocks) + negative_guards != len(
            re.findall(r"^#guard_msgs in$", text, re.MULTILINE)
        ):
            fail(f"unreviewed message guard: {name}")
        public_declarations = [
            declaration
            for declaration in entry["declarations"]
            if not re.search(r"\bprivate\b", declaration)
        ]
        if entry["category"] == "handwritten-lean" and len(public_declarations) > len(
            blocks
        ):
            fail(f"public theorem lacks a reviewed dependency guard: {name}")
        for block in blocks:
            if "depends on axioms:" in block:
                names = re.search(r"depends on axioms: \[([^]]*)\]", block)
                if names is None or not set(names[1].replace("\n", "").split(",")):
                    fail(f"invalid dependency output: {name}")
                if any(
                    word.strip() not in {"propext", "Classical.choice", "Quot.sound"}
                    for word in names[1].split(",")
                ):
                    fail(f"nonstandard proof dependency: {name}")
            elif "does not depend on any axioms" not in block:
                fail(f"unexpected dependency output: {name}")
    scripts = [entry["path"] for entry in entries if entry["category"] == "validation"]
    for commands in (manifest["sourceChecks"], manifest["tests"]):
        if len(commands) != len({tuple(command) for command in commands}):
            fail("duplicate source gate")
        for command in commands:
            if not command or command[0] not in scripts:
                fail(f"unreviewed source gate: {command}")
            checked_path(root, command[0])
    for command in manifest["sourceChecks"]:
        name = Path(command[0]).name
        if name.startswith("extract_"):
            expected = ["--check-source"]
        elif name.startswith("lift_"):
            expected = ["--check"]
        elif name == "certify_registration_shallow_dispatch.py":
            expected = []
        else:
            fail(f"unrecognized source checker: {command}")
        if command[1:] != expected:
            fail(f"source checker must run its read-only mode: {command}")
    for command in manifest["tests"]:
        if len(command) != 1 or not Path(command[0]).name.startswith("test_"):
            fail(f"invalid negative-control command: {command}")
    missing = {
        name
        for name in scripts
        if Path(name).name.startswith("test_") and [name] not in manifest["tests"]
    }
    if missing:
        fail(f"source controls omitted: {sorted(missing)}")


def run_commands(commands: list[list[str]], root: Path = ROOT) -> None:
    for command in commands:
        subprocess.run([sys.executable, *command], cwd=root, check=True)


def fresh_extraction_commands(
    manifest: dict, workspace: Path, root: Path = ROOT
) -> list[list[str]]:
    work, root = workspace.resolve(), root.resolve()
    if work == root or root in work.parents or work in root.parents:
        fail("fresh extraction workspace must be outside the checkout")
    selected = []
    for command in manifest["sourceChecks"]:
        if Path(command[0]).name.startswith("extract_"):
            if command[1:] != ["--check-source"]:
                fail(f"invalid fresh extraction control: {command}")
            selected.append(command[0])
    work.mkdir(parents=True, exist_ok=True)
    fresh = Path(tempfile.mkdtemp(prefix="computational-completion-", dir=work))
    return [
        [script, "--check", "--work-dir", str(fresh / Path(script).stem)]
        for script in selected
    ]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check-roster", action="store_true")
    mode.add_argument("--check-sources", action="store_true")
    mode.add_argument(
        "--paths",
        choices=["generated-lean", "handwritten-lean", "lean-control", "validation"],
    )
    mode.add_argument("--check-extractions", type=Path, metavar="WORK_DIR")
    args = parser.parse_args()
    manifest = read_manifest()
    check_roster(manifest=manifest)
    if args.paths:
        for entry in manifest["artifacts"]:
            if entry["category"] == args.paths:
                print(
                    Path(entry["path"]).relative_to("beaconcrypt-core")
                    if entry["path"].startswith("beaconcrypt-core/")
                    else "../" + entry["path"]
                )
    elif args.check_sources:
        run_commands(manifest["tests"])
        run_commands(manifest["sourceChecks"])
    elif args.check_extractions:
        run_commands(fresh_extraction_commands(manifest, args.check_extractions))
    else:
        print(
            f"Computational completion roster matches: {len(manifest['artifacts'])} artifacts."
        )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        raise SystemExit(f"computational completion gate: {error}") from error
