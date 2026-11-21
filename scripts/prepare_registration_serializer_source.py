#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Prepare exact field-helper boundaries for original registration serializers.

All production generated Rust remains byte-identical, including in the fixture.
A supplemental transport module retains the complete original module before
appending derived entry copies and exact field expressions in typed helpers.
Public entry copies retain their admission checks and relink only those copies.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil

import check_registration_codec_extraction as checkpoint
import prepare_registration_codec_source as reviewed
import prepare_registration_preflight_source as functions
import registration_codec_normalization as normalization

ROOT = checkpoint.ROOT
TRANSPORT = "beaconcrypt-parse/src/generated/transport.rs"
SUPPLEMENT = "beaconcrypt-parse/src/extraction_registration_transport.rs"
LIB = "beaconcrypt-parse/src/lib.rs"
MANIFEST = "registration-serializer-correspondence.json"
ENTRIES = ("extraction_encode_init", "extraction_encode_response")


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = checkpoint.snapshot(root)
    for name in (
        "scripts/prepare_registration_serializer_source.py",
        "scripts/prepare_registration_preflight_source.py",
        "scripts/registration_codec_normalization.py",
        "scripts/prepare_registration_codec_source.py",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationSerializerFieldBoundary.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def expected(root: Path = ROOT) -> tuple[dict[str, str], dict]:
    before = source_snapshot(root)
    reviewed.original_sources(root)
    original = (root / TRANSPORT).read_text()
    if "extraction_" in normalization.mask(original):
        raise ValueError("reserved extraction namespace in original transport")
    originals = []
    for name in ("serialize_initkex", "serialize_kexresponse"):
        signature, body = functions.function_body(
            original, r"pub\s+fn\s+" + name + r"\s*\("
        )
        originals.append({"function": name, "signature": signature, "body": body})
    fragments = "\n".join(
        row["signature"] + "{" + row["body"] + "}" for row in originals
    )
    prepared, boundaries = normalization.outline_serializer_field_sizes(fragments)
    if len(boundaries) != 8:
        raise ValueError("fixed field-boundary roster drift")
    for row in boundaries:
        row["lean_boundary"] = (
            "BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates."
            + row["function"]
        )
    for name in ("serialize_initkex", "serialize_kexresponse"):
        prepared = re.sub(r"\b" + name + r"\b", "extraction_" + name, prepared)
    lib = (root / LIB).read_text()
    if "extraction_" in normalization.mask(lib):
        raise ValueError("reserved extraction namespace in original lib")
    frontends = []
    for public, transport in (
        ("encode_init", "serialize_initkex"),
        ("encode_response", "serialize_kexresponse"),
    ):
        signature, body = functions.function_body(
            lib, r"pub\s+fn\s+" + public + r"\s*\("
        )
        call = "transport::" + transport
        if body.count(call) != 1:
            raise ValueError("public frontend source-call roster drift")
        copied_signature = re.sub(
            r"\b" + public + r"\b", "extraction_" + public, signature
        )
        copied_body = body.replace(call, "transport::extraction_" + transport, 1)
        frontends.append(
            {
                "function": public,
                "original_signature": signature,
                "original_body": body,
                "prepared_signature": copied_signature,
                "prepared_body": copied_body,
            }
        )
    marker = '#[path = "generated/transport.rs"]'
    if lib.count(marker) != 1:
        raise ValueError("transport module path roster drift")
    lib = lib.replace(marker, '#[path = "extraction_registration_transport.rs"]', 1)
    lib += (
        "\n"
        + "\n".join(
            row["prepared_signature"] + "{" + row["prepared_body"] + "}"
            for row in frontends
        )
        + "\n"
    )
    supplement = original + "\n" + prepared + "\n"
    manifest = {
        "kind": "source-field-expression-helper-boundaries",
        "original_functions": originals,
        "original_fragments": fragments,
        "prepared_fragments": prepared,
        "field_boundaries": boundaries,
        "public_frontends": frontends,
        "rust_start_from": list(ENTRIES),
        "generated_rust_files_unchanged": True,
        "original_generated_bodies_unchanged": True,
        "source_correspondence_proved": False,
        "public_codec_law_proved": False,
        "source_sha256": before,
    }
    if before != source_snapshot(root):
        raise ValueError("serializer source changed during preparation")
    return {SUPPLEMENT: supplement, LIB: lib}, manifest


def certificate(boundaries: list[dict]) -> str:
    text = """-- SPDX-License-Identifier: 0BSD
-- Generated exact helper-boundary instances; source correspondence manifest is checked separately.
import BeaconcryptCore.RegistrationSerializerControllerExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates
variable [BeaconcryptCore.Refinement.RegistrationSerializerPrimitive.Operations]
"""
    for row in boundaries:
        helper = "beaconcrypt_parse.transport." + row["function"]
        text += (
            "\ntheorem "
            + row["function"]
            + " (payload output : Slice U8) (low high : Bool) :\n"
        )
        text += (
            "    ((fun captured state lo hi => "
            + helper
            + " captured state lo hi) payload output low high) =\n"
        )
        text += "      " + helper + " payload output low high :=\n"
        text += "  BeaconcryptCore.Refinement.RegistrationSerializerFieldBoundary.helper_eta _ _ _ _ _\n"
    text += "\nend BeaconcryptCore.RegistrationSerializerControllerExtraction.SourceCertificates\n"
    for row in boundaries:
        text += (
            "\n/-- info: '"
            + row["lean_boundary"]
            + "' depends on axioms: [propext,\n Classical.choice,\n Quot.sound] -/\n#guard_msgs in\n#print axioms "
            + row["lean_boundary"]
            + "\n"
        )
    return text


def check_fixture(directory: Path, root: Path = ROOT) -> None:
    if any(
        path.name != MANIFEST
        for path in directory.glob("registration-*-correspondence.json")
    ):
        raise ValueError("serializer fixture cannot impersonate another codec cohort")
    outputs, expected_manifest = expected(root)
    if json.loads((directory / MANIFEST).read_text()) != expected_manifest:
        raise ValueError("serializer helper/source correspondence certificate drift")
    for name, contents in outputs.items():
        if (directory / name).read_text() != contents:
            raise ValueError("serializer prepared source composition drift")
    for path in (root / "beaconcrypt-parse/src/generated").glob("*.rs"):
        if (directory / path.relative_to(root)).read_bytes() != path.read_bytes():
            raise ValueError("serializer fixture modified original generated Rust")


def prepare(directory: Path, root: Path = ROOT) -> None:
    directory, root = directory.resolve(), root.resolve()
    if directory == root or root in directory.parents or directory.exists():
        raise ValueError(
            "preparation requires a new destination outside source worktree"
        )
    outputs, manifest = expected(root)
    directory.mkdir(parents=True)
    for name in ("Cargo.toml", "Cargo.lock", "hax.toml", "LICENSE"):
        shutil.copyfile(root / name, directory / name)
    for name in (
        "beaconcrypt",
        "beaconcrypt-core",
        "beaconcrypt-crypto",
        "beaconcrypt-ffi",
        "beaconcrypt-parse",
        "beaconcrypt-wasm",
    ):
        source, destination = root / name, directory / name
        destination.mkdir()
        shutil.copyfile(source / "Cargo.toml", destination / "Cargo.toml")
        if (source / "src").is_dir():
            shutil.copytree(source / "src", destination / "src")
        if (source / "build.rs").exists():
            shutil.copyfile(source / "build.rs", destination / "build.rs")
    for name, contents in outputs.items():
        (directory / name).write_text(contents)
    (directory / MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    prepare(args.destination)


if __name__ == "__main__":
    main()
