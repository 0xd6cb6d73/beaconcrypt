#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Prepare exact fixed-three-part specializations in an isolated source copy.

The selected core request owns three slices. The original checked length fold
and ordered Vec extension loop are unrolled for that shape; the source function
prefixes and all generated parser files remain byte-for-byte present.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil

from registration_codec_normalization import close, mask
from prepare_adapter_public_wrappers import MEMBERS

SOURCES = ("beaconcrypt/src/ratchet.rs", "beaconcrypt/src/wire.rs")
HASHES = (
    "5f39724e93d3880de29c80527253258e8b37d83fe52d789b340b5aa329b2085c",
    "66f1b1230efeeb37719a8a7a8bc7780d4b65c5f925118a5e44bc764c3d7c71ca",
)
MARKERS = ("fn join_record_parts<const N: usize>", "pub(crate) fn encode_frame_parts(")


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def transform(source: str, index: int) -> tuple[str, dict]:
    start = source.index(MARKERS[index])
    lexical = mask(source)
    end = close(lexical, lexical.index("{", start)) + 1
    original = source[start:end]
    if digest(original.encode()) != HASHES[index]:
        raise ValueError("unreviewed original fixed-part helper source")
    body = original[original.index("{") + 1 : -1]
    variable = "length" if index == 0 else "ciphertext_length"
    folded = f"\n\tlet {variable} = parts\n\t\t.iter()\n\t\t.try_fold(0usize, |length, part| length.checked_add(part.len()))?;"
    if body.count(folded) != 1:
        raise ValueError("checked length fold changed")
    expanded = (
        "\n\tlet length0 = 0usize.checked_add(parts[0].len())?;\n\tlet length1 = length0.checked_add(parts[1].len())?;\n"
        + f"\tlet {variable} = length1.checked_add(parts[2].len())?;"
    )
    body = body.replace(folded, expanded, 1)
    if index == 0:
        original_loop = (
            "\tfor part in parts {\n\t\toutput.extend_from_slice(part);\n\t}"
        )
        if body.count(original_loop) != 1:
            raise ValueError("ordered Vec extension loop changed")
        body = body.replace(
            original_loop,
            "\n".join(f"\toutput.extend_from_slice(parts[{i}]);" for i in range(3)),
            1,
        )
        signature = (
            "fn _proof_join_record_three(parts: [&[u8]; 3]) -> Option<Vec<u8>> {"
        )
    else:
        before = (
            "beaconcrypt_parse::encode_frame_parts(sequence, sender, parts, output)"
        )
        if body.count(before) != 1:
            raise ValueError("frame serializer operands changed")
        body = body.replace(
            before,
            "beaconcrypt_parse::encode_frame_parts(sequence, sender, &parts, output)",
            1,
        )
        signature = "fn _proof_encode_frame_three(sequence: u64, sender: u64, parts: [&[u8]; 3]) -> Option<Vec<u8>> {"
    # Formatting is part of the reviewed extraction fixture, including closure spans.
    helper = "\n" + signature + body.replace("\t", "    ") + "}\n"
    return source + "\n" + helper, {
        "original": original,
        "original_sha256": HASHES[index],
        "helper": helper,
        "part_count": 3,
        "fold_order": [0, 1, 2],
        "source_prefix_unchanged": True,
        "laws": [
            "AdapterRecordFixedParts.fold_three",
            "AdapterRecordFixedParts.extend_three",
            "AdapterRecordFixedParts.indices",
        ],
    }


def source_files(root: Path) -> dict[str, bytes]:
    """The exact workspace subset copied into the isolated extraction fixture."""
    files = {}
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        path = root / name
        if path.is_symlink():
            raise ValueError("unreviewed source fixture symlink")
        if path.is_file():
            files[name] = path.read_bytes()
    for member in MEMBERS:
        if (root / member).is_symlink() or (root / member / "src").is_symlink():
            raise ValueError("unreviewed source fixture symlink")
        for name in ("Cargo.toml", "build.rs"):
            path = root / member / name
            if path.is_symlink():
                raise ValueError("unreviewed source fixture symlink")
            if path.is_file():
                files[path.relative_to(root).as_posix()] = path.read_bytes()
        for path in sorted((root / member / "src").rglob("*")):
            if path.is_symlink():
                raise ValueError("unreviewed source fixture symlink")
            if path.is_file():
                files[path.relative_to(root).as_posix()] = path.read_bytes()
    return files


def certificate(root: Path) -> dict:
    """Review the complete original/helper correspondence without writing files."""
    root = root.resolve()
    files = source_files(root)
    changed = {}
    for index, name in enumerate(SOURCES):
        original = files[name].decode()
        prepared, proof = transform(original, index)
        if not prepared.startswith(original):
            raise ValueError("original helper source prefix was edited")
        changed[name] = {
            **proof,
            "source_sha256": digest(files[name]),
            "prepared_sha256": digest(prepared.encode()),
        }
    return {
        "source_changes": changed,
        "unchanged_sha256": {
            name: digest(contents)
            for name, contents in files.items()
            if name not in SOURCES
        },
    }


def check_fixture(root: Path, destination: Path, expected: dict) -> None:
    root, destination = root.resolve(), destination.resolve()
    if certificate(root) != expected:
        raise ValueError("fixed-part source certificate drift")
    files = source_files(root)
    installed = {}
    for path in destination.rglob("*"):
        if path.is_symlink():
            raise ValueError("unreviewed fixture symlink")
        if path.is_file():
            installed[path.relative_to(destination).as_posix()] = path.read_bytes()
    if set(installed) != set(files):
        raise ValueError("fixed-part fixture file roster changed")
    for name, original in files.items():
        wanted = (
            original + b"\n" + expected["source_changes"][name]["helper"].encode()
            if name in SOURCES
            else original
        )
        if installed[name] != wanted:
            raise ValueError("unreviewed fixed-part fixture edit: " + name)


def prepare(root: Path, destination: Path) -> dict:
    if destination.is_symlink():
        raise ValueError("fixed-part fixture must not be a symlink")
    root, destination = root.resolve(), destination.resolve()
    if (
        destination == root
        or root in destination.parents
        or destination in root.parents
        or destination.exists()
    ):
        raise ValueError("fresh fixed-part fixture must be outside the repository")
    expected = certificate(root)
    destination.mkdir(parents=True)
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        if (root / name).exists():
            shutil.copy2(root / name, destination / name)
    for member in MEMBERS:
        (destination / member).mkdir()
        for name in ("Cargo.toml", "build.rs"):
            if (root / member / name).exists():
                shutil.copy2(root / member / name, destination / member / name)
        if (root / member / "src").exists():
            shutil.copytree(root / member / "src", destination / member / "src")
    changed = {}
    for index, name in enumerate(SOURCES):
        original = (root / name).read_text()
        prepared, proof = transform(original, index)
        if not prepared.startswith(original):
            raise ValueError("original helper source prefix was edited")
        (destination / name).write_text(prepared)
        changed[name] = {
            **proof,
            "source_sha256": digest(original.encode()),
            "prepared_sha256": digest(prepared.encode()),
        }
    unchanged = {}
    for path in destination.rglob("*"):
        if path.is_file() and path.relative_to(destination).as_posix() not in SOURCES:
            name = path.relative_to(destination).as_posix()
            if path.read_bytes() != (root / name).read_bytes():
                raise ValueError("unreviewed fixed-part fixture edit")
            unchanged[name] = digest(path.read_bytes())
    result = {"source_changes": changed, "unchanged_sha256": unchanged}
    if result != expected:
        raise ValueError("fixed-part source changed while preparing the fixture")
    check_fixture(root, destination, expected)
    return result


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
