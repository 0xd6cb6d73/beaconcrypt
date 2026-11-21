#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Append an exact original array-writer copy with checked helper boundaries.

All original generated files and bodies remain unchanged. The supplemental
module retains the complete original source, and the copied writer preserves
its GCD, rotation, mutable output and rejection behavior. This is extraction
preparation, not a proved rotation or public codec law.
"""

from __future__ import annotations

import json
from pathlib import Path

import check_registration_codec_extraction as checkpoint
import prepare_registration_preflight_source as functions
import prepare_registration_shallow_source as shallow
import registration_codec_normalization as normalization

ROOT = checkpoint.ROOT
MANIFEST = "registration-array-correspondence.json"
BASE_MANIFEST = "registration-shallow-base-correspondence.json"
ENTRIES = ("cbordetveraux::extraction_array_entry",)


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = shallow.source_snapshot(root)
    for name in (
        "scripts/prepare_registration_array_source.py",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationArrayPlatform.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def expected(root: Path = ROOT) -> tuple[dict[str, str], dict]:
    before = source_snapshot(root)
    outputs, base = shallow.expected(root)
    original = (root / shallow.AUX).read_text()
    normalized, indices = normalization.outline_rotation_indices(original)
    normalized, loops = normalization.outline_rotation_inner_loops(normalized)
    signature, body = functions.function_body(
        normalized, r"fn cbor_serialize_array·\s*\("
    )
    if signature.count("cbor_serialize_array·") != 1:
        raise ValueError("array writer signature roster drift")
    copied = (
        "pub "
        + signature.replace("cbor_serialize_array·", "extraction_serialize_array")
        + "{"
        + body
        + "}"
    )
    marker = "\nfn extraction_rotation_index_0("
    if normalized.count(marker) != 1 or "extraction_" in normalization.mask(original):
        raise ValueError("array helper namespace roster drift")
    helpers = normalized[normalized.index(marker) :]
    entry_signature, entry_body = functions.function_body(
        (root / shallow.DET).read_text(), r"pub fn cbor_det_serialize_array\s*\("
    )
    if (
        entry_body.count("crate::cbordetveraux::cbor_serialize_array") != 1
        or entry_body.count("crate::cbordetveraux::mk_raw_uint64") != 1
    ):
        raise ValueError("array public entry composition drift")
    prepared_entry_signature = entry_signature.replace(
        "cbor_det_serialize_array", "extraction_array_entry", 1
    )
    prepared_entry_body = entry_body.replace(
        "crate::cbordetveraux::cbor_serialize_array", "extraction_serialize_array", 1
    ).replace("crate::cbordetveraux::mk_raw_uint64", "mk_raw_uint64", 1)
    entry = "\n" + prepared_entry_signature + "{" + prepared_entry_body + "}\n"
    outputs[shallow.SUPPLEMENT] += "\n" + copied + "\n" + helpers + entry
    outputs[BASE_MANIFEST] = json.dumps(base, indent=2, sort_keys=True) + "\n"
    original_signature, original_body = functions.function_body(
        original, r"fn cbor_serialize_array·\s*\("
    )
    manifest = {
        "format": 1,
        "source_sha256": before,
        "rust_start_from": list(ENTRIES),
        "prepared_sha256": {
            name: checkpoint.digest(text.encode()) for name, text in outputs.items()
        },
        "base_preparation": base,
        "original_array_writer": {
            "signature": original_signature,
            "body": original_body,
        },
        "copied_array_writer": copied,
        "scalar_helper_boundaries": indices,
        "inner_loop_boundaries": loops,
        "appended_helpers": helpers,
        "entry": {
            "original_signature": entry_signature,
            "original_body": entry_body,
            "prepared_signature": prepared_entry_signature,
            "prepared_body": prepared_entry_body,
            "source": entry,
        },
        "generated_rust_files_unchanged": True,
        "original_generated_bodies_unchanged": True,
        "source_correspondence_proved": False,
        "rotation_law_proved": False,
        "public_codec_law_proved": False,
    }
    if before != source_snapshot(root):
        raise ValueError("array source changed during preparation")
    return outputs, manifest


def check_fixture(directory: Path, root: Path = ROOT) -> None:
    outputs, manifest = expected(root)
    if (directory / shallow.MANIFEST).exists():
        raise ValueError("array fixture cannot impersonate the shallow cohort")
    if json.loads((directory / MANIFEST).read_text()) != manifest:
        raise ValueError("array helper-boundary provenance drift")
    for name, source in outputs.items():
        if (directory / name).read_text() != source:
            raise ValueError("array supplemental composition drift")
    for name in (
        shallow.AUX,
        shallow.DET,
        "beaconcrypt-parse/src/generated/transport.rs",
    ):
        if (directory / name).read_bytes() != (root / name).read_bytes():
            raise ValueError("array fixture modified original generated Rust")


def prepare(directory: Path, root: Path = ROOT) -> None:
    outputs, manifest = expected(root)
    shallow.prepare(directory, root)
    for name, source in outputs.items():
        (directory / name).write_text(source)
    (directory / shallow.MANIFEST).unlink()
    (directory / MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root)
