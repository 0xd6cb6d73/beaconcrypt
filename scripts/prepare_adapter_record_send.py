#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Prepare one exact borrow-localization of the actual outer send driver.

The fixture retains every primitive call and continuation. Only consuming the
borrowed optional detached result is distributed over its two constructors.
Production Rust and generated parser sources are never modified.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

from extract_adapter_seal import source_files
from registration_codec_normalization import close, mask

SOURCE = "beaconcrypt/src/ratchet.rs"
MARKER = "fn execute_record_send("
ORIGINAL_SHA256 = "01a6479b741b8a162ac6efdb79f2ba8deb281d43f57b054c0bf0b625b402d362"
BORROW = "\tlet detached_view = detached.as_ref().map(|(body, tag)| (body.as_slice(), *tag));\n\tlet mut commitment = match aead.resume(detached_view) {"
LOCAL = "\tlet resumed = match detached.as_ref() {\n\t\tSome((body, tag)) => aead.resume(Some((body.as_slice(), *tag))),\n\t\tNone => aead.resume(None),\n\t};\n\tlet mut commitment = match resumed {"


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def transform(source: str) -> tuple[str, dict]:
    start = source.index(MARKER)
    lexical = mask(source)
    end = close(lexical, lexical.index("{", start)) + 1
    original = source[start:end]
    if digest(original.encode()) != ORIGINAL_SHA256:
        raise ValueError("unreviewed outer send driver source")
    if original.count(BORROW) != 1:
        raise ValueError("outer send borrowed result consumption changed")
    prepared = original.replace(BORROW, LOCAL, 1)
    return source[:start] + prepared + source[end:], {
        "original": original,
        "original_sha256": ORIGINAL_SHA256,
        "prepared": prepared,
        "prepared_sha256": digest(prepared.encode()),
        "law": "AdapterRecordSendBorrow.aead_resume",
        "monadic_law": "AdapterRecordSendBorrow.consume_optional",
        "primitive_order": [
            "begin_record_send",
            "ratchet_hkdf",
            "execute_seal_request",
            "execute_commitment_hash",
            "execute_write_request",
            "finish",
        ],
        "normalization": "distribute pure optional borrowed-view consumption",
    }


def certificate(root: Path) -> dict:
    files = source_files(root)
    prepared, law = transform(files[SOURCE].decode())
    expected = {name: digest(contents) for name, contents in files.items()}
    expected[SOURCE] = digest(prepared.encode())
    return {
        "source_sha256": {name: digest(contents) for name, contents in files.items()},
        "fixture_sha256": expected,
        "control": law,
    }


def prepare(root: Path, fixture: Path) -> dict:
    root = root.resolve()
    if fixture.is_symlink() or fixture.exists():
        raise ValueError("outer send source fixture must be fresh")
    fixture = fixture.resolve()
    if fixture == root or root in fixture.parents:
        raise ValueError("outer send source fixture must be outside the checkout")
    proof = certificate(root)
    for name, contents in source_files(root).items():
        if name == SOURCE:
            contents = transform(contents.decode())[0].encode()
        path = fixture / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
    check_fixture(fixture, proof)
    return proof


def check_fixture(fixture: Path, proof: dict) -> None:
    actual = {}
    for path in fixture.rglob("*"):
        if path.is_symlink():
            raise ValueError("outer send fixture symlink")
        if path.is_file():
            actual[path.relative_to(fixture).as_posix()] = digest(path.read_bytes())
    if actual != proof["fixture_sha256"]:
        raise ValueError("outer send fixture source or file roster changed")
