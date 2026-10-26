#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Regenerate/check the isolated production authentication extraction.

Run inside the pinned proof environment, or put cargo-hax 0.4.2 and rustup on
PATH. The work directory retains LLBC and build evidence for inspection. This
entry point never writes the historical BeaconcryptCore/Extraction cohort.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tomllib

CORE = Path(__file__).resolve().parents[1]
ROOT = CORE.parent
DESTINATION = CORE / "proofs/lean/BeaconcryptCore/AuthenticationExtraction"
NAMESPACE = "beaconcrypt_authentication_core"
SUBDIRECTORY = "BeaconcryptCore/AuthenticationExtraction"
PINNED_TOOLS = {
    "aeneas": "nightly-2026.09.03-6852e64",
    "charon": "nightly-2026.09.02",
}
PINNED_VERSIONS = {
    "lean": "leanprover/lean4:v4.35.0",
    "hax-lean-lib": "174840bf2f633ae3bae955e08f781b3737ffc0b8",
}
GENERATED = (
    "TypesExternal_Template.lean",
    "Types.lean",
    "FunsExternal_Template.lean",
    "Funs.lean",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument("--work-dir", required=True, type=Path)
    parser.add_argument("--cargo", default="cargo")
    args = parser.parse_args()
    configuration = tomllib.loads((ROOT / "hax.toml").read_text())
    if configuration.get("tools") != PINNED_TOOLS:
        parser.error("hax.toml tool pins differ from the reviewed extraction")
    if configuration.get("versions") != PINNED_VERSIONS:
        parser.error(
            "hax.toml library/toolchain pins differ from the reviewed extraction"
        )
    version = subprocess.check_output([args.cargo, "hax", "--version"], text=True)
    if "version=0.4.2" not in version.splitlines():
        parser.error("this extraction requires cargo-hax 0.4.2")

    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ)
    environment["CARGO_TARGET_DIR"] = str(work / "target")
    environment["CARGO_BUILD_JOBS"] = "2"
    command = [
        args.cargo,
        "hax",
        "-C",
        "--locked",
        ";",
        "into",
        "-v",
        "--output-dir",
        str(work / "hax-output"),
        "lean",
        "--charon-args=--start-from beaconcrypt_core::authentication --sysroot default",
        "--aeneas-args=-dest "
        + shlex.quote(str(work / "generated"))
        + " -subdir "
        + SUBDIRECTORY
        + " -namespace "
        + NAMESPACE,
    ]
    with (work / "extraction.log").open("w") as log:
        log.write("Command: " + repr(command) + "\n")
        log.flush()
        result = subprocess.run(
            command, cwd=CORE, env=environment, stdout=log, stderr=log
        )
    if result.returncode:
        print((work / "extraction.log").read_text(), file=sys.stderr)
        return result.returncode

    generated = work / "generated" / SUBDIRECTORY
    contents = {name: (generated / name).read_bytes() for name in GENERATED}
    # These templates are empty: the selected module needs no external axioms.
    # Keep the generator's bytes unchanged when installing their import targets.
    for prefix in ("Types", "Funs"):
        template = contents[f"{prefix}External_Template.lean"]
        if any(
            token in template for token in (b"sorry", b"axiom ", b"opaque ", b"#check")
        ):
            raise RuntimeError(
                "authentication extraction introduced an external obligation"
            )
        contents[f"{prefix}External.lean"] = template
    provenance = {
        "cargo_hax": "0.4.2",
        "tools": PINNED_TOOLS,
        "versions": PINNED_VERSIONS,
        "rust_start_from": "beaconcrypt_core::authentication",
        "lean_namespace": NAMESPACE,
        "charon_sysroot": "default",
        "source_sha256": {
            "beaconcrypt-core/src/authentication.rs": sha256(
                CORE / "src/authentication.rs"
            ),
            "beaconcrypt-core/src/constants.rs": sha256(CORE / "src/constants.rs"),
            "beaconcrypt-core/src/lib.rs": sha256(CORE / "src/lib.rs"),
            "beaconcrypt-core/Cargo.toml": sha256(CORE / "Cargo.toml"),
            "Cargo.lock": sha256(ROOT / "Cargo.lock"),
            "hax.toml": sha256(ROOT / "hax.toml"),
        },
        "generated_sha256": {
            name: hashlib.sha256(value).hexdigest()
            for name, value in sorted(contents.items())
        },
    }
    contents["provenance.json"] = (json.dumps(provenance, indent=2) + "\n").encode()
    if args.write:
        DESTINATION.mkdir(parents=True, exist_ok=True)
        for name, value in contents.items():
            (DESTINATION / name).write_bytes(value)
        print(f"Wrote {len(contents)} authentication extraction/provenance files")
        return 0
    changed = [
        name
        for name, value in contents.items()
        if not (DESTINATION / name).is_file()
        or (DESTINATION / name).read_bytes() != value
    ]
    if changed:
        print("Authentication extraction drift: " + ", ".join(changed), file=sys.stderr)
        return 1
    print("Authentication extraction and provenance match the pinned generator")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
