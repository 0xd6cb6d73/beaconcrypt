#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Recreate the exact isolated Aeneas branch-duplication feasibility experiment."""

from __future__ import annotations

import argparse
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile

import evaluate_registration_codec_toolchain as candidate
from extract_frame_codec import isolated_work


def replace_exact(source: str, old: str, new: str, count: int) -> str:
    if source.count(old) != count:
        raise ValueError("candidate patch does not match the reviewed source")
    return source.replace(old, new)


def prepare(base: Path, destination: Path, mode: str = candidate.CUSTOM) -> dict:
    if mode not in (candidate.CUSTOM, candidate.RECOVER):
        raise ValueError("unknown custom candidate")
    destination = isolated_work(destination)
    if destination.exists():
        raise ValueError("candidate source destination must not already exist")
    revision = candidate.SOURCE_COMMITS["aeneas"]
    actual = subprocess.check_output(
        ["git", "-C", str(base), "rev-parse", revision + "^{commit}"], text=True
    ).strip()
    if actual != revision:
        raise ValueError("missing exact candidate Aeneas source commit")
    archive = subprocess.check_output(["git", "-C", str(base), "archive", revision])
    destination.mkdir(parents=True)
    with tarfile.open(fileobj=io.BytesIO(archive)) as contents:
        contents.extractall(destination, filter="data")
    if mode == candidate.CUSTOM:
        path = destination / candidate.CUSTOM_PATCH["file"]
        candidate.checked_hash(path, candidate.CUSTOM_PATCH["before_sha256"])
        path.write_text(
            replace_exact(path.read_text(), "if join then", "if false && join then", 3)
        )
        candidate.checked_hash(path, candidate.CUSTOM_PATCH["after_sha256"])
    else:
        path = destination / "src/interp/InterpBorrows.ml"
        source = replace_exact(
            path.read_text(),
            "let destructure_abs (span : Meta.span)",
            "let destructure_abs ?(recoverable = false) (span : Meta.span)",
            1,
        )
        start = source.index("let destructure_abs ")
        end = source.index("\nlet ", start + 1)
        source = (
            source[:start]
            + replace_exact(
                source[start:end],
                "[%cassert] span\n              (not\n                 (ty_has_borrows",
                "[%cassert_recover] recoverable span\n              (not\n                 (ty_has_borrows",
                4,
            )
            + source[end:]
        )
        path.write_text(source)
        path = destination / "src/interp/InterpBorrows.mli"
        path.write_text(
            replace_exact(
                path.read_text(),
                "val destructure_abs :\n",
                "val destructure_abs :\n  ?recoverable:bool ->\n",
                1,
            )
        )
        path = destination / "src/interp/InterpJoin.ml"
        source = replace_exact(
            path.read_text(),
            "destructure_abs span fresh_abs_kind ~can_end:true\n          ~destructure_shared_values:true ctx",
            "destructure_abs ~recoverable span fresh_abs_kind ~can_end:true\n          ~destructure_shared_values:true ctx",
            1,
        )
        path.write_text(
            replace_exact(
                source,
                '| None -> [%craise] span "Could not match the contexts"',
                '| None -> [%craise_recover] recoverable span "Could not match the contexts"',
                1,
            )
        )
        for changed in candidate.RECOVER_PATCH["patches"]:
            candidate.checked_hash(
                destination / changed["file"], changed["after_sha256"]
            )
    flake = destination / "flake.nix"
    flake.write_text(
        replace_exact(
            flake.read_text(),
            "              postInstall = ''\n                ln -s ${charon}/bin/charon $out/bin\n              '';",
            '              postInstall = "";',
            1,
        )
    )
    source_hash = candidate.source_hash(destination)
    expected = (
        candidate.CUSTOM_SOURCE_HASH
        if mode == candidate.CUSTOM
        else candidate.RECOVER_SOURCE_HASH
    )
    if source_hash != expected:
        raise ValueError("prepared source tree does not match the reviewed candidate")
    return {
        "evaluation_only": True,
        "candidate": mode,
        "source_tree_sha256": source_hash,
        "source_commit": revision,
        "exact_patch": (
            candidate.CUSTOM_PATCH
            if mode == candidate.CUSTOM
            else candidate.RECOVER_PATCH
        ),
        "source_correspondence_proved": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--candidate", choices=(candidate.CUSTOM, candidate.RECOVER), required=True
    )
    parser.add_argument("--base-source", required=True, type=Path)
    parser.add_argument("--destination", required=True, type=Path)
    args = parser.parse_args()
    try:
        result = prepare(args.base_source, args.destination, args.candidate)
        # The manifest stays outside the hashed source inputs.
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (
        OSError,
        ValueError,
        subprocess.CalledProcessError,
        tarfile.TarError,
    ) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
