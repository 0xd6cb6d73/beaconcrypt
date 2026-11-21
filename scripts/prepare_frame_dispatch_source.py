#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Isolate the actual finite frame dispatch from the unreachable many-part tail.

Original generated parser files remain immutable. The four original slice
patterns become equivalent length tests with guarded indices; the whole
original fallback is outlined unchanged. No codec result is assumed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from registration_codec_normalization import close, mask
from prepare_adapter_public_wrappers import MEMBERS

SOURCE = "beaconcrypt-parse/src/frame.rs"
FUNCTION_SHA256 = "7fb1ce25580f94b80cc8eb82fc6e720bc9100c2dd650e96c98c14a4d98bcae5c"
PREFIX_SHA256 = "cde52045072a122828b9cba91eef5bccbc29635646b9ccc3639442ae07a65b05"
TAIL_SHA256 = "5c6307cc9de1c059cc999ef1bcc6fcc9b9179d49db3877f6d7ff22a37cdf56bb"
PREFIX = """\tif parts.len() == 0 { return encode_three(sequence, sender, &[], &[], &[], output); }
\tif parts.len() == 1 { return encode_three(sequence, sender, parts[0], &[], &[], output); }
\tif parts.len() == 2 { return encode_three(sequence, sender, parts[0], parts[1], &[], output); }
\tif parts.len() == 3 { return encode_three(sequence, sender, parts[0], parts[1], parts[2], output); }"""


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def source_files(root: Path) -> dict[str, bytes]:
    paths = set()
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        if (root / name).exists():
            paths.add(name)
    for member in MEMBERS:
        for name in ("Cargo.toml", "build.rs"):
            if (root / member / name).exists():
                paths.add(f"{member}/{name}")
        paths.update(
            path.relative_to(root).as_posix()
            for path in (root / member / "src").rglob("*")
            if path.is_file()
        )
    if any((root / name).is_symlink() for name in paths):
        raise ValueError("symbolic link in frame source fixture")
    return {name: (root / name).read_bytes() for name in sorted(paths)}


def transform(source: str) -> tuple[str, dict]:
    start = source.index("pub(crate) fn encode_parts(")
    lexical = mask(source)
    opening = lexical.index("{", start)
    end = close(lexical, opening) + 1
    tail_start = source.index("\tlet mut payload_length = 0usize;", opening)
    original = source[start:end]
    prefix = source[opening + 1 : tail_start]
    tail = source[tail_start : end - 1]
    for contents, expected in (
        (original, FUNCTION_SHA256),
        (prefix, PREFIX_SHA256),
        (tail, TAIL_SHA256),
    ):
        if digest(contents.encode()) != expected:
            raise ValueError("unreviewed original frame dispatch source")
    helper = (
        "\nfn _proof_encode_many(sequence: u64, sender: u64, parts: &[&[u8]], output: &mut [u8]) -> usize {\n"
        + tail
        + "}\n"
    )
    prepared = (
        source[: opening + 1]
        + "\n"
        + PREFIX
        + "\n\t_proof_encode_many(sequence, sender, parts, output)\n}"
        + source[end:]
        + helper
    )
    return prepared, {
        "original_function_sha256": FUNCTION_SHA256,
        "original_prefix_sha256": PREFIX_SHA256,
        "original_tail_sha256": TAIL_SHA256,
        "original_function": original,
        "length_prefix": PREFIX,
        "outlined_tail": tail,
        "laws": [
            "FrameDispatch.classify",
            "FrameDispatch.selected_three",
            "AdapterPublicControlNormalization.loop_congr",
        ],
        "fallback_claimed_reachable": False,
    }


def prepare(root: Path, destination: Path) -> dict:
    root = root.resolve()
    unresolved = destination.absolute()
    if any(path.is_symlink() for path in (unresolved, *unresolved.parents)):
        raise ValueError("symbolic-link frame fixture destination")
    destination = unresolved.resolve()
    if (
        destination == root
        or root in destination.parents
        or destination in root.parents
        or destination.exists()
    ):
        raise ValueError("fresh frame dispatch fixture must be outside the repository")
    destination.mkdir(parents=True)
    for name, contents in source_files(root).items():
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(contents)
    original = (root / SOURCE).read_text()
    prepared, certificate = transform(original)
    (destination / SOURCE).write_text(prepared)
    unchanged = {}
    for path in destination.rglob("*"):
        if path.is_file() and path.relative_to(destination).as_posix() != SOURCE:
            name = path.relative_to(destination).as_posix()
            if path.read_bytes() != (root / name).read_bytes():
                raise ValueError("unreviewed frame fixture edit")
            unchanged[name] = digest(path.read_bytes())
    return {
        "source_sha256": digest(original.encode()),
        "prepared_sha256": digest(prepared.encode()),
        "control_certificate": certificate,
        "unchanged_sha256": unchanged,
    }


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
