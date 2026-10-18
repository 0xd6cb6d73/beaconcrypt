#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Verify the pinned EverParse bundle and explicitly check or write Rust output."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import shlex
import subprocess
import sys
import tarfile
import tempfile

BUNDLE_SHA256 = "b96f5de71df42f5ea861bd4115a892371f10dac9b1249e08a6a92bca180b46a5"
GENERATED_FILES = ("cbordetver.rs", "cbordetveraux.rs", "transport.rs")
CRATE_DIR = Path(__file__).resolve().parents[1]


def regenerate(bundle: Path, *, write: bool) -> int:
    # Keep hashing and extraction on the same open file and reject it before any extraction.
    with (
        bundle.open("rb") as archive,
        tempfile.TemporaryDirectory(
            prefix="beaconcrypt-parse-", dir="/tmp"
        ) as temporary,
    ):
        digest = hashlib.file_digest(archive, "sha256").hexdigest()
        if digest != BUNDLE_SHA256:
            raise ValueError(
                f"bundle SHA-256 mismatch: expected {BUNDLE_SHA256}, got {digest}"
            )
        archive.seek(0)
        scratch = Path(temporary)
        with tarfile.open(fileobj=archive, mode="r:gz") as contents:
            contents.extractall(scratch, filter="data")

        output = scratch / "out"
        output.mkdir()
        command = [
            str(scratch / "everparse" / "bin" / "cddl.exe"),
            "--rust",
            "--mname",
            "Transport",
            "--odir",
            str(output),
            str(CRATE_DIR / "schema" / "transport.cddl"),
        ]
        print(f"Running: {shlex.join(command)}", flush=True)
        subprocess.run(command, cwd=scratch, check=True)

        found = {path.name for path in output.glob("*.rs")}
        if found != set(GENERATED_FILES):
            raise ValueError(f"unexpected generated Rust inventory: {sorted(found)}")
        regenerated = {name: (output / name).read_bytes() for name in GENERATED_FILES}
        destination = CRATE_DIR / "src" / "generated"
        drift = False
        for name, content in regenerated.items():
            target = destination / name
            digest = hashlib.sha256(content).hexdigest()
            if write:
                target.write_bytes(content)
                status = "wrote"
            elif not target.is_file() or target.read_bytes() != content:
                status = "DIFFERS"
                drift = True
            else:
                status = "matches"
            print(
                f"{status}: {name} ({len(content)} bytes, sha256 {digest})", flush=True
            )

        if drift:
            print(
                "Generated sources differ; review the schema and use --write explicitly.",
                file=sys.stderr,
            )
            return 1
        return 0


def main() -> int:
    if sys.version_info < (3, 12):
        print("Python 3.12 or newer is required.", file=sys.stderr)
        return 1
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "bundle", type=Path, help="local EverParse v2026.08.21 Linux x86_64 tar.gz"
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--check",
        action="store_true",
        help="report drift without changing checked-in files",
    )
    mode.add_argument(
        "--write",
        action="store_true",
        help="replace the three checked-in generated Rust files",
    )
    args = parser.parse_args()
    try:
        return regenerate(args.bundle, write=args.write)
    except (
        OSError,
        ValueError,
        tarfile.TarError,
        subprocess.CalledProcessError,
    ) as error:
        print(f"Regeneration failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
