#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Append the exact fixed-two plaintext join in an isolated source copy.

The original seal dispatcher and every production/generated Rust file remain
unchanged prefixes. Only the checked two-element length fold and ordered Vec
extensions are unrolled for the actual Prefixed plaintext call.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from prepare_adapter_record_helpers import source_files
from registration_codec_normalization import close, mask

SOURCE = "beaconcrypt/src/ratchet.rs"
ORIGINAL_SHA256 = "5f39724e93d3880de29c80527253258e8b37d83fe52d789b340b5aa329b2085c"
MARKER = "fn join_record_parts<const N: usize>"


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def transform(source: str) -> tuple[str, dict]:
    if source.count(MARKER) != 1:
        raise ValueError("unreviewed original seal-join declaration roster")
    start = source.index(MARKER)
    lexical = mask(source)
    end = close(lexical, lexical.index("{", start)) + 1
    original = source[start:end]
    if digest(original.encode()) != ORIGINAL_SHA256:
        raise ValueError("unreviewed original seal-join body")
    body = original[original.index("{") + 1 : -1]
    folded = "\n\tlet length = parts\n\t\t.iter()\n\t\t.try_fold(0usize, |length, part| length.checked_add(part.len()))?;"
    original_loop = "\tfor part in parts {\n\t\toutput.extend_from_slice(part);\n\t}"
    if body.count(folded) != 1 or body.count(original_loop) != 1:
        raise ValueError("seal-join checked fold or extension loop changed")
    body = body.replace(
        folded,
        "\n\tlet length0 = 0usize.checked_add(parts[0].len())?;\n"
        "\tlet length = length0.checked_add(parts[1].len())?;",
        1,
    ).replace(
        original_loop,
        "\toutput.extend_from_slice(parts[0]);\n\toutput.extend_from_slice(parts[1]);",
        1,
    )
    helper = (
        "\nfn _proof_join_seal_two(parts: [&[u8]; 2]) -> Option<Vec<u8>> {"
        + body.replace("\t", "    ")
        + "}\n"
    )
    return source + "\n" + helper, {
        "original": original,
        "original_sha256": ORIGINAL_SHA256,
        "helper": helper,
        "part_count": 2,
        "fold_order": [0, 1],
        "source_prefix_unchanged": True,
        "laws": [
            "AdapterSealFixedParts.fold_two",
            "AdapterSealFixedParts.extend_state_two",
            "AdapterSealFixedParts.indices",
        ],
    }


def certificate(root: Path) -> dict:
    files = source_files(root.resolve())
    original = files[SOURCE].decode()
    prepared, proof = transform(original)
    return {
        "source_changes": {
            SOURCE: {
                **proof,
                "source_sha256": digest(files[SOURCE]),
                "prepared_sha256": digest(prepared.encode()),
            }
        },
        "unchanged_sha256": {
            name: digest(contents) for name, contents in files.items() if name != SOURCE
        },
    }


def check_fixture(root: Path, destination: Path, expected: dict) -> None:
    root, destination = root.resolve(), destination.resolve()
    if certificate(root) != expected:
        raise ValueError("seal-join source certificate drift")
    files = source_files(root)
    installed = {}
    for path in destination.rglob("*"):
        if path.is_symlink():
            raise ValueError("unreviewed seal-join fixture symlink")
        if path.is_file():
            installed[path.relative_to(destination).as_posix()] = path.read_bytes()
    if set(installed) != set(files):
        raise ValueError("seal-join fixture file roster changed")
    for name, original in files.items():
        wanted = (
            original + b"\n" + expected["source_changes"][SOURCE]["helper"].encode()
            if name == SOURCE
            else original
        )
        if installed[name] != wanted:
            raise ValueError("unreviewed seal-join fixture edit: " + name)


def prepare(root: Path, destination: Path) -> dict:
    if destination.is_symlink():
        raise ValueError("seal-join fixture must not be a symlink")
    root, destination = root.resolve(), destination.resolve()
    if (
        destination == root
        or root in destination.parents
        or destination in root.parents
        or destination.exists()
    ):
        raise ValueError("fresh seal-join fixture must be outside the repository")
    expected = certificate(root)
    for name, contents in source_files(root).items():
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
    path = destination / SOURCE
    path.write_bytes(
        path.read_bytes()
        + b"\n"
        + expected["source_changes"][SOURCE]["helper"].encode()
    )
    check_fixture(root, destination, expected)
    return expected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--fixture", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    args = parser.parse_args()
    args.certificate.write_text(
        json.dumps(prepare(args.source_root, args.fixture), indent=2, sort_keys=True)
        + "\n"
    )


if __name__ == "__main__":
    main()
