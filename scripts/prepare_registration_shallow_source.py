#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Prepare exact constructor-restricted EverCDDL bodies outside the worktree.

The generated Rust files are copied unchanged. A supplemental module consists
of the complete original auxiliary module followed by four appended helpers;
each helper embeds a literal original shallow dispatcher branch. The original
deep branches remain in that module. ByteString factory specialization selects
only two closed constructor comparisons; all original size/rejection code stays.
This preparation is not a public codec law or a source-semantics oracle.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import sys

import check_registration_codec_extraction as checkpoint
import prepare_registration_codec_source as originals
import prepare_registration_preflight_source as functions
import registration_codec_normalization as syntax

ROOT = checkpoint.ROOT
LIB = "beaconcrypt-parse/src/lib.rs"
AUX = "beaconcrypt-parse/src/generated/cbordetveraux.rs"
DET = "beaconcrypt-parse/src/generated/cbordetver.rs"
SUPPLEMENT = "beaconcrypt-parse/src/extraction_registration_aux.rs"
MANIFEST = "registration-shallow-correspondence.json"
ENTRIES = (
    "extraction_mk_byte_string",
    "extraction_string_kind_equal",
    "cbordetveraux::extraction_serialize_shallow_int",
    "cbordetveraux::extraction_serialize_shallow_string",
    "cbordetveraux::extraction_size_shallow_int",
    "cbordetveraux::extraction_size_shallow_string",
)


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = checkpoint.snapshot(root)
    for name in (
        "scripts/prepare_registration_shallow_source.py",
        "scripts/prepare_registration_codec_source.py",
        "scripts/prepare_registration_preflight_source.py",
        "scripts/registration_codec_normalization.py",
        "beaconcrypt-parse/generated/README.md",
        "beaconcrypt-parse/schema/transport.cddl",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationConstructorGuards.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationShallowGuards.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def closed_comparison(body: str, condition: str, selected: bool) -> tuple[str, dict]:
    masked = syntax.mask(body)
    matches = list(re.finditer(r"\bif\s+" + re.escape(condition) + r"\s*\{", masked))
    if len(matches) != 1:
        raise ValueError("closed constructor comparison roster drift")
    start = matches[0].start()
    yes_start = masked.index("{", start)
    yes_end = syntax.close(masked, yes_start)
    if masked[yes_end + 1 :].lstrip()[:4] != "else":
        raise ValueError("closed comparison lost its else branch")
    no_start = masked.index("{", yes_end + 1)
    no_end = syntax.close(masked, no_start)
    yes, no = body[yes_start + 1 : yes_end], body[no_start + 1 : no_end]
    choice = yes if selected else no
    expression = body[start : no_end + 1]
    replacement = "{" + choice + "}"
    transformed = body[:start] + replacement + body[no_end + 1 :]
    if (
        transformed[:start] + expression + transformed[start + len(replacement) :]
        != body
    ):
        raise ValueError("closed comparison reconstruction failed")
    return transformed, {
        "condition": condition,
        "constructor": "ByteString",
        "value": selected,
        "original_expression": expression,
        "yes": yes,
        "no": no,
        "selected": choice,
        "offset": start,
    }


def expected(root: Path = ROOT) -> tuple[dict[str, str], dict]:
    before = source_snapshot(root)
    source = originals.original_sources(root)
    _, original_factory = functions.function_body(
        source[DET], r"pub fn cbor_det_mk_string\s*<[^>]*>\s*\("
    )
    factory, first = closed_comparison(
        original_factory, "ty == cbor_det_string_kind::TextString", False
    )
    factory, second = closed_comparison(
        factory, "ty == cbor_det_string_kind::ByteString", True
    )
    if re.search(r"\bty\b", syntax.mask(factory)):
        raise ValueError("ByteString specialization retained an enum parameter")
    factory_helper = (
        "\npub fn extraction_mk_byte_string<'a>(s: &'a [u8]) -> "
        "crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw<'a> {\n"
        "use crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw;\n"
        + factory
        + "\n}\n"
        "\npub fn extraction_string_kind_equal(\n"
        "    left: crate::cbordetver::cbor_det_string_kind,\n"
        "    right: crate::cbordetver::cbor_det_string_kind,\n"
        ") -> bool { left == right }\n"
    )
    appended, dispatchers = [], []
    for name, operation in (("ser·_d", "serialize"), ("siz·_d", "size")):
        signature, original = functions.function_body(
            source[AUX], r"pub\(crate\) fn " + re.escape(name) + r"\s*\("
        )
        masked = syntax.mask(original)
        branch = re.search(r"\bif deep\s*\{", masked)
        if branch is None:
            raise ValueError("missing original shallow/deep dispatcher")
        prefix = original[: branch.start()]
        if prefix.strip() != "let deep: bool = compute_deep(x·);":
            raise ValueError("deep dispatcher prefix drift")
        yes_start = masked.index("{", branch.start())
        yes_end = syntax.close(masked, yes_start)
        if masked[yes_end + 1 :].lstrip()[:4] != "else":
            raise ValueError("deep dispatcher lost its else branch")
        no_start = masked.index("{", yes_end + 1)
        no_end = syntax.close(masked, no_start)
        if masked[no_end + 1 :].strip():
            raise ValueError("unexpected code after shallow dispatcher")
        no = original[no_start + 1 : no_end]
        helpers = []
        for suffix, rust_type, constructor in (
            ("int", "cbor_int", "CBOR_Case_Int"),
            ("string", "cbor_string", "CBOR_Case_String"),
        ):
            helper_name = "extraction_" + operation + "_shallow_" + suffix
            if signature.count("x·: cbor_raw") != 1:
                raise ValueError("dispatcher input type drift")
            specialized = (
                signature.replace("pub(crate)", "pub", 1)
                .replace(name, helper_name, 1)
                .replace("x·: cbor_raw", "value: " + rust_type, 1)
            )
            construction = (
                "let x·: cbor_raw = cbor_raw::" + constructor + " { v: value };"
            )
            helper = "\n" + specialized + "{\n" + construction + "\n" + no + "\n}\n"
            # The body after the local constructor is exactly the original branch.
            if helper.split(construction + "\n", 1)[1][:-3] != no:
                raise ValueError("constructor helper body reconstruction failed")
            appended.append(helper)
            helpers.append(
                {
                    "name": helper_name,
                    "input": rust_type,
                    "constructor": constructor,
                    "signature": specialized,
                    "construction": construction,
                    "source": helper,
                }
            )
        dispatchers.append(
            {
                "name": name,
                "signature": signature,
                "original_body": original,
                "prefix": prefix,
                "deep_branch": original[yes_start + 1 : yes_end],
                "shallow_branch": no,
                "helpers": helpers,
            }
        )
    old_path = '#[path = "generated/cbordetveraux.rs"]'
    new_path = '#[path = "extraction_registration_aux.rs"]'
    if source[LIB].count(old_path) != 1 or "extraction_" in syntax.mask(source[LIB]):
        raise ValueError("original auxiliary module path/helper namespace drift")
    outputs = {
        LIB: source[LIB].replace(old_path, new_path, 1) + factory_helper,
        SUPPLEMENT: source[AUX] + "".join(appended),
    }
    manifest = {
        "format": 1,
        "source_sha256": before,
        "original_codec_sha256": originals.ORIGINALS,
        "prepared_sha256": {
            name: checkpoint.digest(text.encode()) for name, text in outputs.items()
        },
        "rust_start_from": list(ENTRIES),
        "factory": {
            "original_body": original_factory,
            "specialized_body": factory,
            "comparisons": [first, second],
            "source": factory_helper,
        },
        "dispatchers": dispatchers,
        "source_composition": "complete byte-identical original auxiliary module plus appended constructor helpers",
        "checked_guard_endpoints": [
            "RegistrationConstructorGuards.mk_raw_value",
            "RegistrationConstructorGuards.argument_major",
            "RegistrationConstructorGuards.mk_uint",
            "RegistrationConstructorGuards.int_dispatch",
            "RegistrationConstructorGuards.string_dispatch",
            "RegistrationShallowGuards.byte_not_text",
            "RegistrationShallowGuards.byte_is_byte",
            "RegistrationShallowGuards.byte_factory_preserved",
            "RegistrationShallowGuards.registration_byte_kind",
        ],
        "guard_scope": "exact constructor/branch equations; source AST reification and complete public codec closure are separate",
        "generated_rust_files_unchanged": True,
        "original_generated_bodies_unchanged": True,
        "source_correspondence_proved": False,
        "public_codec_law_proved": False,
    }
    if before != source_snapshot(root):
        raise ValueError("source changed during constructor preparation")
    return outputs, manifest


def check_fixture(directory: Path, root: Path = ROOT) -> None:
    outputs, manifest = expected(root)
    if json.loads((directory / MANIFEST).read_text()) != manifest:
        raise ValueError("constructor correspondence provenance drift")
    for name, text in outputs.items():
        if (directory / name).read_text() != text:
            raise ValueError("constructor helper/source composition drift")
    for name in (AUX, DET, "beaconcrypt-parse/src/generated/transport.rs"):
        if (directory / name).read_bytes() != (root / name).read_bytes():
            raise ValueError("constructor fixture modified original generated Rust")


def prepare(directory: Path, root: Path = ROOT) -> None:
    directory = directory.resolve()
    if directory == root.resolve() or root.resolve() in directory.parents:
        raise ValueError("constructor fixture must be outside the worktree")
    if directory.exists():
        raise ValueError("constructor fixture requires a new destination")
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
        src, dst = root / name, directory / name
        dst.mkdir()
        shutil.copyfile(src / "Cargo.toml", dst / "Cargo.toml")
        if (src / "src").is_dir():
            shutil.copytree(src / "src", dst / "src")
        if (src / "build.rs").exists():
            shutil.copyfile(src / "build.rs", dst / "build.rs")
    for name, text in outputs.items():
        (directory / name).write_text(text)
    (directory / MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--write-fixture", type=Path)
    group.add_argument("--check-fixture", type=Path)
    args = parser.parse_args()
    try:
        if args.write_fixture:
            prepare(args.write_fixture)
        else:
            check_fixture(args.check_fixture)
        print("Exact constructor bodies and unchanged original generated Rust match")
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
