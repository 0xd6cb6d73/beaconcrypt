#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Prepare original handwritten preflight with proved standard slice unfoldings.

Only a new external fixture is written. Production and fixture EverCDDL files
remain unchanged. Standard-library bodies and the exact four-field Init and six-field Response callsites
are fingerprinted. No public codec correctness law is assumed or installed.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import sys

import check_registration_codec_extraction as checkpoint
import registration_codec_normalization as syntax

ROOT = checkpoint.ROOT
LIB = "beaconcrypt-parse/src/lib.rs"
LIB_SHA256 = "1566e1f7314eb0c46354c6d0763e019272fbb891ef95a08959ed153d63917b9a"
STD_SOURCE = (
    Path.home()
    / ".rustup/toolchains/nightly-2026-08-18-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/mod.rs"
)
STD_SHA256 = "8026ddec62fb732d01dc6fcb700fbf109aa5dd94d2391387db3202f405669d43"
STD_FUNCTION_HASHES = {
    "split_first": {
        "signature_sha256": "9a28b9e6e8510eb221e2d8b4e6a84192ebb84c16f69599e5d32e74590f020f1d",
        "body_sha256": "cd5e3d256df275026ba44bb2a7cb7b3c570e666d14008edbae1751a19b9a3f2a",
    },
    "split_at_checked": {
        "signature_sha256": "62cfd107d886df639cac54ca5af164d03ab228dbe97c98647a68a77586dd6d66",
        "body_sha256": "3a6537a19246afec0b3e29afbd1165365af2fdcc58c8453a9e8f9921bfe8109b",
    },
    "split_at": {
        "signature_sha256": "0019fdb4119dccf8f7e6426696539ed7ba1058f7614dbd5ca15a92b2b0052c91",
        "body_sha256": "94226ae0e2cae16f7c68a11fbd071c727c0a92d301188e51e5a999b83a56e47b",
    },
    "strip_prefix": {
        "signature_sha256": "1a0d7812735e93f72b143eaad9af3be114e131f64782fe7585fbe465cba95768",
        "body_sha256": "8833d87cb621ef1d75b991d8faef60cf595a4a5c12f5ef490f9cb5d217b0192c",
    },
    "slice_pattern_identity": {
        "signature_sha256": "13b843bf38236cd5c457339fd2d036292779859972760a5d82663c951f94986f",
        "body_sha256": "2337a5088641e5da41e366d75295e7d6cd9233924456dc89f804fae08c8b25ca",
    },
}
CERTIFICATE = "RegistrationPreflightSourceCertificates.lean"
MANIFEST = "registration-preflight-correspondence.json"


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = checkpoint.snapshot(root)
    for name in (
        "scripts/prepare_registration_preflight_source.py",
        "scripts/registration_codec_normalization.py",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecStandardSlices.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecFixedFields.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def function_body(source: str, signature: str) -> tuple[str, str]:
    found = re.search(signature, syntax.mask(source))
    if found is None:
        raise ValueError("missing reviewed function signature")
    start = syntax.mask(source).index("{", found.end())
    end = syntax.close(syntax.mask(source), start)
    return source[found.start() : start], source[start + 1 : end]


def standard_sources(path: Path = STD_SOURCE) -> dict:
    contents = path.read_bytes()
    if checkpoint.digest(contents) != STD_SHA256:
        raise ValueError("unreviewed pinned Rust standard-library source")
    source = contents.decode()
    signatures = {
        "split_first": r"pub const fn split_first\(&self\) -> Option<\(&T, &\[T\]\)>",
        "split_at_checked": r"pub const fn split_at_checked\(&self, mid: usize\) -> Option<\(&\[T\], &\[T\]\)>",
        "split_at": r"pub const fn split_at\(&self, mid: usize\) -> \(&\[T\], &\[T\]\)",
        "strip_prefix": r"pub fn strip_prefix<P: SlicePattern<Item = T> \+ \?Sized>\(&self, prefix: &P\) -> Option<&\[T\]>\s*where\s*T: PartialEq,",
    }
    result = {
        "toolchain": "nightly-2026-08-18",
        "source_sha256": STD_SHA256,
        "functions": {},
    }
    for name, signature in signatures.items():
        signature, body = function_body(source, signature)
        result["functions"][name] = {
            "signature": signature,
            "body": body,
            "body_sha256": checkpoint.digest(body.encode()),
        }
    start = source.index("impl<T> SlicePattern for [T] {")
    signature, body = function_body(
        source[start:], r"fn as_slice\(&self\) -> &\[Self::Item\]"
    )
    if body.strip() != "self":
        raise ValueError("SlicePattern slice identity changed")
    result["functions"]["slice_pattern_identity"] = {
        "signature": signature,
        "body": body,
        "body_sha256": checkpoint.digest(body.encode()),
    }
    return checked_standard_evidence(result)


def checked_standard_evidence(evidence: dict) -> dict:
    if not isinstance(evidence, dict) or set(evidence) != {
        "toolchain",
        "source_sha256",
        "functions",
    }:
        raise ValueError("standard-library evidence roster drift")
    if (
        evidence["toolchain"] != "nightly-2026-08-18"
        or evidence["source_sha256"] != STD_SHA256
    ):
        raise ValueError("standard-library identity drift")
    if not isinstance(evidence["functions"], dict) or set(evidence["functions"]) != set(
        STD_FUNCTION_HASHES
    ):
        raise ValueError("standard function roster drift")
    for name, expected in STD_FUNCTION_HASHES.items():
        item = evidence["functions"][name]
        if not isinstance(item, dict) or set(item) != {
            "signature",
            "body",
            "body_sha256",
        }:
            raise ValueError("standard function evidence drift")
        if (
            checkpoint.digest(item["signature"].encode())
            != expected["signature_sha256"]
            or checkpoint.digest(item["body"].encode()) != expected["body_sha256"]
            or item["body_sha256"] != expected["body_sha256"]
        ):
            raise ValueError("standard function body/signature drift")
    return evidence


def certificate(calls: list[dict]) -> str:
    source = """-- SPDX-License-Identifier: 0BSD
-- Exact production preflight field lists; original Rust and EverCDDL source unchanged.
import Aeneas
import BeaconcryptCore.Refinement.RegistrationCodecFixedFields
import BeaconcryptCore.Refinement.RegistrationCodecStandardSlices

set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates
open Aeneas.Std
universe v
variable {S : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]
"""
    for call in calls:
        fields = [str(value) + "#u8" for value in call["fields"]]
        name = call["role"] + "_fields_preserved"
        source += (
            "\ntheorem "
            + name
            + " (step : S → U8 → m S) (initial : S) :\n    ["
            + ", ".join(fields)
            + "].foldlM step initial = (do\n"
        )
        previous = "initial"
        for number, field in enumerate(fields[:-1]):
            variable = "state" + str(number)
            source += (
                "      let " + variable + " ← step " + previous + " " + field + "\n"
            )
            previous = variable
        source += (
            "      step "
            + previous
            + " "
            + fields[-1]
            + ") :=\n  RegistrationCodecFixedFields.fold_"
            + ("four" if len(fields) == 4 else "six")
            + " step initial "
            + " ".join(fields)
            + "\n"
        )
    source += (
        "\nend BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates\n"
    )
    for call in calls:
        name = (
            "BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates."
            + call["role"]
            + "_fields_preserved"
        )
        source += (
            "\n/-- info: '"
            + name
            + "' depends on axioms: [propext,\n Classical.choice,\n Quot.sound] -/\n#guard_msgs in\n#print axioms "
            + name
            + "\n"
        )
    return source


def expected(
    root: Path = ROOT,
    std_source: Path = STD_SOURCE,
    *,
    std_evidence: dict | None = None,
) -> tuple[str, str, dict]:
    before = source_snapshot(root)
    original = (root / LIB).read_text()
    if checkpoint.digest(original.encode()) != LIB_SHA256:
        raise ValueError("unreviewed original handwritten codec source")
    if "extraction_" in syntax.mask(original):
        raise ValueError("helper namespace collision")
    standard = (
        standard_sources(std_source)
        if std_evidence is None
        else checked_standard_evidence(std_evidence)
    )
    calls = []
    for found in re.finditer(
        r"\bpreflight\(input,\s*&\[([^]]+)\],\s*&\[([^]]+)\]\)\?", syntax.mask(original)
    ):
        prefix = [int(value.strip(), 0) for value in found[1].split(",")]
        fields = [int(value.strip(), 0) for value in found[2].split(",")]
        calls.append(
            {
                "role": "init" if prefix[-1] == 0 else "response",
                "prefix": prefix,
                "fields": fields,
                "original_call": original[found.start() : found.end()],
            }
        )
    expected_calls = [
        ("init", [134, 3, 0], [2, 2, 2, 2]),
        ("response", [136, 3, 1], [2, 2, 2, 2, 0, 2]),
    ]
    if [
        (item["role"], item["prefix"], item["fields"]) for item in calls
    ] != expected_calls:
        raise ValueError("original complete preflight callsite roster changed")
    prepared = original
    start = prepared.index("\tlet (encoded, rest) = rest.split_at_checked(width)?;")
    stop = prepared.index("\n}", start)
    original_tail = prepared[start:stop]
    word_body = (
        original_tail[
            original_tail.index("\tlet mut word") : original_tail.index("\tSome")
        ]
        + "\tu64::from_be_bytes(word)"
    )
    prepared = (
        prepared[:start] + "\textraction_argument_long(rest, width)" + prepared[stop:]
    )
    first = "\tlet (&header, rest) = input.split_first()?;"
    replacement = "\tif input.is_empty() { return None; }\n\tlet header = input[0];\n\tlet (_, rest) = input.split_at(1);"
    if prepared.count(first) != 1:
        raise ValueError("split-first source occurrence changed")
    prepared = prepared.replace(first, replacement, 1)
    preflight = prepared.index("fn preflight(")
    start = prepared.index("\tfor &major in fields {", preflight)
    stop = prepared.index("\n\tremaining.is_empty()", start)
    loop = prepared[start:stop]
    step = loop[loop.index("\n") + 1 : loop.rindex("\n\t}")]
    old_assignment = "\t\tremaining = if major == 2 {"
    if step.count(old_assignment) != 1:
        raise ValueError("preflight singleton step changed")
    step = step.replace(old_assignment, "\t\tlet remaining = if major == 2 {")
    prepared = (
        prepared[:start]
        + "".join(
            "\tremaining = extraction_preflight_field(remaining, fields["
            + str(index)
            + "])?;\n"
            for index in range(6)
        )
        + prepared[stop:]
    )
    signature = "fields: &[u8]) -> Option<()>"
    if prepared.count(signature) != 1:
        raise ValueError("private preflight signature changed")
    prepared = prepared.replace(signature, "fields: &[u8;6]) -> Option<()>", 1)
    long_body = "\tif width > rest.len() { return None; }\n\tlet (encoded, rest) = rest.split_at(width);\n\tlet value = extraction_argument_word(encoded, width);\n\tSome((value,rest))"
    prepared += (
        "\nfn extraction_argument_long(rest: &[u8], width: usize) -> Option<(u64, &[u8])> {\n"
        + long_body
        + "\n}\n"
    )
    prepared += (
        "\nfn extraction_argument_word(encoded: &[u8], width: usize) -> u64 {\n"
        + word_body
        + "\n}\n"
    )
    prepared += (
        "\nfn extraction_preflight_field(remaining: &[u8], major: u8) -> Option<&[u8]> {\n"
        + step
        + "\nSome(remaining)\n}\n"
    )
    prefix_body = standard["functions"]["strip_prefix"]["body"]
    identity = "let prefix = prefix.as_slice();"
    if prefix_body.count(identity) != 1:
        raise ValueError("standard prefix identity occurrence changed")
    prefix_body = prefix_body.replace(identity, "", 1)
    prefix_body = re.sub(r"\bself\b", "input", prefix_body)
    if prepared.count("input.strip_prefix(prefix)?") != 1:
        raise ValueError("preflight standard prefix call changed")
    prepared = prepared.replace(
        "input.strip_prefix(prefix)?", "extraction_strip_prefix(input, prefix)?", 1
    )
    prepared += (
        "\nfn extraction_strip_prefix<'a>(input: &'a [u8], prefix: &[u8]) -> Option<&'a [u8]> {\n"
        + prefix_body
        + "\n}\n"
    )
    six_signature, six_body = function_body(prepared, r"fn preflight\(")
    four_signature = six_signature.replace(
        "fn preflight(", "fn extraction_preflight_four(", 1
    ).replace("fields: &[u8;6]", "fields: &[u8;4]", 1)
    four_body = six_body
    for index in (4, 5):
        step_line = (
            "\tremaining = extraction_preflight_field(remaining, fields["
            + str(index)
            + "])?;\n"
        )
        if four_body.count(step_line) != 1:
            raise ValueError("fixed preflight specialization step roster changed")
        four_body = four_body.replace(step_line, "", 1)
    init_call = calls[0]["original_call"]
    if prepared.count(init_call) != 1:
        raise ValueError("Init preflight specialization call roster changed")
    prepared = prepared.replace(
        init_call, init_call.replace("preflight(", "extraction_preflight_four(", 1), 1
    )
    prepared += "\n" + four_signature + "{" + four_body + "}\n"
    specialization = {
        "original_source_body": loop,
        "six_signature": six_signature,
        "six_body": six_body,
        "four_signature": four_signature,
        "four_body": four_body,
        "init_call": init_call,
        "field_counts": [4, 6],
        "state_forwarded_at_every_step": True,
    }
    lean = certificate(calls)
    manifest = {
        "format": 1,
        "source_sha256": before,
        "original_lib_sha256": LIB_SHA256,
        "prepared_lib_sha256": checkpoint.digest(prepared.encode()),
        "standard_library": standard,
        "original_argument_tail": original_tail,
        "scalar_word_body": word_body,
        "long_argument_body": long_body,
        "split_first_original": first,
        "split_first_lowering": replacement,
        "original_preflight_loop": loop,
        "effectful_field_step": step,
        "standard_prefix_body": prefix_body,
        "callsites": calls,
        "fixed_specializations": specialization,
        "certificate_sha256": checkpoint.digest(lean.encode()),
        "normalization_endpoints": [
            "RegistrationCodecStandardSlices.checked_split_lowering",
            "RegistrationCodecStandardSlices.checked_split_existing_model",
            "RegistrationCodecStandardSlices.copied_first_lowering",
            "RegistrationCodecStandardSlices.slice_pattern_identity",
            "RegistrationCodecFixedFields.fold_four",
            "RegistrationCodecFixedFields.fold_six",
        ],
        "production_source_modified": False,
        "evercddl_source_modified": False,
        "public_codec_law_proved": False,
    }
    if before != source_snapshot(root):
        raise ValueError("source changed during preflight preparation")
    return prepared, lean, manifest


def check_fixture(
    directory: Path, root: Path = ROOT, std_source: Path = STD_SOURCE
) -> None:
    prepared, lean, manifest = expected(root, std_source)
    if json.loads((directory / MANIFEST).read_text()) != manifest:
        raise ValueError("preflight correspondence provenance drift")
    if (directory / LIB).read_text() != prepared or (
        directory / CERTIFICATE
    ).read_text() != lean:
        raise ValueError("preflight prepared source/certificate drift")
    for path in (root / "beaconcrypt-parse/src/generated").glob("*.rs"):
        if (directory / path.relative_to(root)).read_bytes() != path.read_bytes():
            raise ValueError("preflight fixture changed EverCDDL source")


def prepare(directory: Path, root: Path = ROOT, std_source: Path = STD_SOURCE) -> None:
    directory = directory.resolve()
    if directory == root.resolve() or root.resolve() in directory.parents:
        raise ValueError("preflight fixture must be outside the worktree")
    if directory.exists():
        raise ValueError("preflight fixture requires a new destination")
    prepared, lean, manifest = expected(root, std_source)
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
    (directory / LIB).write_text(prepared)
    (directory / CERTIFICATE).write_text(lean)
    (directory / MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root, std_source)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write-fixture", type=Path)
    modes.add_argument("--check-fixture", type=Path)
    parser.add_argument("--std-source", type=Path, default=STD_SOURCE)
    args = parser.parse_args()
    try:
        if args.write_fixture:
            prepare(args.write_fixture, std_source=args.std_source)
            print(
                "Wrote isolated original-preflight preparation; production and EverCDDL source unchanged"
            )
        else:
            check_fixture(args.check_fixture, std_source=args.std_source)
            print(
                "Original preflight, pinned standard source and normalization certificates match"
            )
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
