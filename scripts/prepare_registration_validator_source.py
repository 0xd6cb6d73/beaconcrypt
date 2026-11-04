#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Prepare checked parser control boundaries without changing generated files.

The existing parser normalization supplies exact control, singleton and helper
certificates. Only supplemental modules and the isolated module paths change;
the three original EverCDDL files remain byte-identical in the fixture as well.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import prepare_frame_dispatch_source as workspace
import prepare_registration_codec_source as reviewed
from prepare_registration_preflight_source import function_body

ROOT = Path(__file__).resolve().parents[1]
LIB = "beaconcrypt-parse/src/lib.rs"
MANIFEST = "registration-validator-correspondence.json"
ENTRIES = (
    "extraction_decode_init",
    "extraction_decode_response",
)
SUPPLEMENTS = {
    "beaconcrypt-parse/src/generated/"
    + name: "beaconcrypt-parse/src/extraction_validator_"
    + name
    for name in ("cbordetveraux.rs", "cbordetver.rs", "transport.rs")
}


def digest(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


def expected(root: Path = ROOT) -> tuple[dict[str, bytes], dict]:
    originals = workspace.source_files(root)
    for name in (
        "hax.toml",
        "scripts/check_registration_codec_extraction.py",
        "scripts/extract_frame_codec.py",
    ):
        originals[name] = (root / name).read_bytes()
    normalized, certificate = reviewed.expected(root, "parser")
    lib = normalized[LIB]
    output = dict(originals)
    for original, supplement in SUPPLEMENTS.items():
        output[supplement] = normalized[original].encode()
        before = '"generated/' + Path(original).name + '"'
        after = '"' + Path(supplement).name + '"'
        if lib.count(before) != 1:
            raise ValueError("parser module path roster changed")
        lib = lib.replace(before, after, 1)
    frontends = []
    original_lib = (root / LIB).read_text()
    for name, enum, field in (
        ("decode_init", "ParsedInit", "init"),
        ("decode_response", "ParsedResponse", "response"),
    ):
        signature, body = function_body(original_lib, r"pub\s+fn\s+" + name + r"\s*\(")
        pattern = enum + "::Some { v: (" + field + ", []) } => Some(" + field + "),"
        selected = (
            enum
            + "::Some { v: ("
            + field
            + ", extraction_remaining) } => { if extraction_remaining.is_empty() { Some("
            + field
            + ") } else { None } },"
        )
        if body.count(pattern) != 1:
            raise ValueError("original complete-consumption pattern changed")
        prepared_body = body.replace(pattern, selected, 1)
        parse_name = (
            "validate_and_parse_initkex"
            if name == "decode_init"
            else "validate_and_parse_kexresponse"
        )
        scrutinee = "match " + parse_name + "(input) {"
        if prepared_body.count(scrutinee) != 1:
            raise ValueError("public parser scrutinee changed")
        prepared_body = prepared_body.replace(
            scrutinee,
            "let extraction_parsed = "
            + parse_name
            + "(input);\nmatch extraction_parsed {",
            1,
        )

        prepared_signature = signature.replace("fn " + name, "fn extraction_" + name, 1)
        lib += "\n" + prepared_signature + "{" + prepared_body + "}\n"
        frontends.append(
            {
                "function": name,
                "original_signature": signature,
                "original_body": body,
                "prepared_signature": prepared_signature,
                "prepared_body": prepared_body,
                "law": "RegistrationPublicDecoderControl.empty_rest",
            }
        )
    output[LIB] = lib.encode()
    unchanged = {
        name: digest(value) for name, value in originals.items() if name != LIB
    }
    return output, {
        "kind": "checked-parser-boundaries-in-supplemental-modules",
        "public_frontends": frontends,
        "original_control_certificate": certificate,
        "module_paths": SUPPLEMENTS,
        "prepared_sha256": {name: digest(value) for name, value in output.items()},
        "unchanged_sha256": unchanged,
        "generated_files_unchanged": True,
        "public_decoder_law_proved": False,
        "native_wire_instantiated": False,
    }


def check_fixture(directory: Path, root: Path = ROOT) -> None:
    files, certificate = expected(root)
    if json.loads((directory / MANIFEST).read_text()) != certificate:
        raise ValueError("parser control certificate drift")
    actual = {
        path.relative_to(directory).as_posix()
        for path in directory.rglob("*")
        if path.is_file()
    }
    if actual != set(files) | {MANIFEST}:
        raise ValueError("parser source fixture roster changed")
    for name, contents in files.items():
        path = directory / name
        if path.is_symlink() or path.read_bytes() != contents:
            raise ValueError("parser source fixture drift: " + name)


def prepare(directory: Path, root: Path = ROOT) -> dict:
    root = root.resolve()
    unresolved = directory.absolute()
    if any(path.is_symlink() for path in (unresolved, *unresolved.parents)):
        raise ValueError("symbolic-link parser fixture")
    directory = unresolved.resolve()
    if (
        directory == root
        or root in directory.parents
        or directory in root.parents
        or directory.exists()
    ):
        raise ValueError("parser fixture must be a fresh external directory")
    files, certificate = expected(root)
    directory.mkdir(parents=True)
    for name, contents in files.items():
        target = directory / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(contents)
    (directory / MANIFEST).write_text(
        json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root)
    return certificate


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    prepare(args.destination)


if __name__ == "__main__":
    main()
