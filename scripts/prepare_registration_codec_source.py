#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Prepare isolated extraction input and explicit source control certificates.

Production EverCDDL output is read-only. This command writes only a new external
fixture. It records every original/prepared file, typed helper body and control
fragment; it never installs generated Lean or treats preparation as codec proof.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import sys

import check_registration_codec_extraction as checkpoint
import registration_codec_normalization as normalization

ROOT = checkpoint.ROOT
ORIGINALS = {
    "beaconcrypt-parse/src/lib.rs": "e3ee33763548d8e22950e0f1b459b686f392a182f85d55289f718dd8a3f3b378",
    "beaconcrypt-parse/src/generated/cbordetver.rs": "e60e27d58b3fe7eeaca202e9751b596c88884b4a76d5bf57a345a21861066d6c",
    "beaconcrypt-parse/src/generated/cbordetveraux.rs": "36420e78b9feed0a4c4a1b6a57b28aeba16ae38be9c61f5ff8165fa088ac3589",
    "beaconcrypt-parse/src/generated/transport.rs": "218245bef2baa287d6d2a77f6013fe7d78c887b4416a88756618240ad83e3fa8",
}
WRAPPER = """
/// Extraction-only value wrapper; delegates exactly once to the original generated helper.
pub fn extraction_iterator_next_value<'a>(
    iterator: cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw<'a>,
) -> (cbordetveraux::cbor_raw<'a>, cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw<'a>) {
    let mut cell = [iterator; 1];
    let value = cbordetver::cbor_det_array_iterator_next(&mut cell);
    (value, cell[0])
}
"""
CERTIFICATE = "RegistrationCodecSourceCertificates.lean"
MANIFEST = "registration-source-correspondence.json"


def original_sources(root: Path = ROOT) -> dict[str, str]:
    result = {}
    for relative, digest in ORIGINALS.items():
        contents = (root / relative).read_bytes()
        if checkpoint.digest(contents) != digest:
            raise ValueError("unreviewed original codec source: " + relative)
        result[relative] = contents.decode()
    return result


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = checkpoint.snapshot(root)
    for name in (
        "scripts/registration_codec_normalization.py",
        "scripts/prepare_registration_codec_source.py",
        "beaconcrypt-parse/schema/transport.cddl",
        "beaconcrypt-parse/generated/README.md",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecControlNormalization.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecSingletonNormalization.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecSourceControl.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecArraySingleton.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def control(expression: str) -> dict:
    parsed = normalization.as_block(expression)
    branch = normalization.conditional(parsed.tail)
    if branch:
        condition, yes, no = branch
        tail = {
            "kind": "branch",
            "condition": condition,
            "yes": control("".join(x.source for x in yes.bindings) + yes.tail),
            "no": control("".join(x.source for x in no.bindings) + no.tail),
        }
    elif parsed.tail in ("true", "false"):
        tail = {"kind": "done", "value": parsed.tail == "true"}
    else:
        tail = {"kind": "expression", "source": parsed.tail}
    for binding in reversed(parsed.bindings):
        tail = {
            "kind": "statement",
            "binding": binding.name,
            "rust_type": binding.ty,
            "expression": binding.expression,
            "source": binding.source,
            "next": tail,
        }
    return tail


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def lean_control(value: dict) -> str:
    if value["kind"] == "done":
        return ".done " + str(value["value"]).lower()
    if value["kind"] == "expression":
        return ".expression " + lean_string(value["source"])
    if value["kind"] == "branch":
        return (
            "(.branch "
            + lean_string(value["condition"])
            + "\n  ("
            + lean_control(value["yes"])
            + ")\n  ("
            + lean_control(value["no"])
            + "))"
        )
    if value["kind"] == "statement":
        statement = (
            "{ binding := "
            + lean_string(value["binding"])
            + ", rustType := "
            + lean_string(value["rust_type"])
            + ", expression := "
            + lean_string(value["expression"])
            + ", source := "
            + lean_string(value["source"])
            + " }"
        )
        return "(.statement " + statement + "\n  (" + lean_control(value["next"]) + "))"
    raise ValueError("unknown source control node")


def certificate(fragments: list[dict], checks: list[dict]) -> str:
    result = """-- SPDX-License-Identifier: 0BSD
-- Generated from exact original EverCDDL control fragments; production Rust is unchanged.
import BeaconcryptCore.Refinement.RegistrationCodecSourceControl
import BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
import BeaconcryptCore.RegistrationSchemaExtraction.Types

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

namespace BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates
open RegistrationCodecSourceControl RegistrationCodecControlNormalization
universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {Environment Result : Type}
"""
    for item in fragments:
        name = item["name"]
        result += (
            "\ndef " + name + " : Control :=\n  " + lean_control(item["control"]) + "\n"
        )
        result += (
            "\ntheorem "
            + name
            + "_preserves (semantics : Semantics m Environment)\n    (environment : Environment) (next : Bool × Environment → m Result) :\n    cps next (controlTree semantics "
            + name
            + " environment) =\n      evaluate (controlTree semantics "
            + name
            + " environment) >>= next :=\n  fragment_preserved _ _ _ _\n"
        )
    iterator = (
        "beaconcrypt_parse.cbordetveraux.bcExtractedToken"
        + "cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw".encode().hex()
    )
    result += "\nabbrev Iterator := " + iterator + "\n"
    for check in checks:
        name = check["function"].replace("_", "") + "State"
        result += (
            "\ntheorem "
            + name
            + " (work : RegistrationCodecArraySingleton.Single Iterator →\n    m (Bool × RegistrationCodecArraySingleton.Single Iterator))\n    (before : RegistrationCodecArraySingleton.Single Iterator)\n    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :\n    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=\n      fun result => next result.2) = (work before >>= fun result => next result.2) :=\n  RegistrationCodecArraySingleton.ignored_result_preserved work before next\n"
        )
    result += "\nend BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates\n"
    for item in fragments:
        name = (
            "BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates."
            + item["name"]
            + "_preserves"
        )
        result += (
            "\n/-- info: '"
            + name
            + "' depends on axioms: [propext,\n Quot.sound] -/\n#guard_msgs in\n#print axioms "
            + name
            + "\n"
        )
    for check in checks:
        name = (
            "BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates."
            + check["function"].replace("_", "")
            + "State"
        )
        result += (
            "\n/-- info: '"
            + name
            + "' depends on axioms: [propext,\n Classical.choice,\n Quot.sound] -/\n#guard_msgs in\n#print axioms "
            + name
            + "\n"
        )
    return result


def transform(
    original: dict[str, str], phase: str
) -> tuple[dict[str, str], list[dict], list[dict]]:
    if phase not in ("schema", "parser", "serializer"):
        raise ValueError("unreviewed preparation phase")
    files = dict(original)
    steps, fragments = [], []
    lib_name = "beaconcrypt-parse/src/lib.rs"
    aux_name = "beaconcrypt-parse/src/generated/cbordetveraux.rs"
    det_name = "beaconcrypt-parse/src/generated/cbordetver.rs"
    transport_name = "beaconcrypt-parse/src/generated/transport.rs"
    if any("extraction_" in normalization.mask(text) for text in original.values()):
        raise ValueError("original source collides with the helper namespace")
    files[lib_name] += WRAPPER
    steps.append(
        {
            "rule": "singleton-next-value-wrapper",
            "body": WRAPPER,
            "source_operation": "cbordetver::cbor_det_array_iterator_next",
            "state_type": "[Iterator;1]",
            "result_type": "(Raw,Iterator)",
        }
    )
    aux = files[aux_name]
    function = aux.index("fn jump_raw_data_item(")
    begin = aux.index("        let off10: usize =\n", function) + len(
        "        let off10: usize =\n"
    )
    end = aux.index(";\n        (&mut poffset)", begin)
    expression = aux[begin:end]
    if "&" in normalization.mask(expression) or "[" in normalization.mask(expression):
        raise ValueError("scalar jump eta captures a reference")
    aux = aux[:begin] + "(move || {\n" + expression + "\n})()" + aux[end:]
    steps.append(
        {
            "rule": "scalar-jump-offset-eta",
            "expression": expression,
            "result_type": "usize",
        }
    )
    if phase == "parser":
        aux, item = normalization.eta_raw_guard(aux)
        steps.append(item)
        aux, items = normalization.eta_canonical_offsets(aux)
        steps.extend(items)
        aux, items = normalization.scalarize_shared_cells(aux)
        steps.extend(items)
        aux, items = normalization.outline_canonical_scans(aux)
        steps.extend(items)
        aux, item = normalization.outline_sorted_scan(aux)
        steps.append(item)
    if phase == "serializer":
        aux, items = normalization.outline_rotation_indices(aux)
        steps.extend(items)
        aux, items = normalization.outline_rotation_inner_loops(aux)
        steps.extend(items)
        for function, result, parameters in (
            (
                "ser·_d",
                "usize",
                {
                    "x·": ("cbor_raw<'a>", False),
                    "out": ("&'b mut [u8]", False),
                    "offset": ("usize", False),
                },
            ),
            (
                "siz·_d",
                "bool",
                {"x·": ("cbor_raw<'a>", False), "out": ("&'b mut [usize]", False)},
            ),
        ):
            aux, items = normalization.outline_effectful_branches(
                aux, function, result, parameters
            )
            steps.extend(items)
    files[aux_name] = aux
    transport = files[transport_name]
    pattern = r"crate::cbordetver::cbor_det_array_iterator_next\(\s*&mut\s*([A-Za-z_][A-Za-z_0-9]*)\s*\)"
    cells = []

    def replace_next(match):
        cell = match[1]
        cells.append(cell)
        return (
            "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value("
            + cell
            + "[0]); "
            + cell
            + "[0] = extraction_after; extraction_value }"
        )

    transport, count = re.subn(pattern, replace_next, transport)
    if count != 60:
        raise ValueError("original iterator-call roster changed: " + str(count))
    steps.append(
        {
            "rule": "singleton-next-copy-in-out",
            "calls": count,
            "cells": cells,
            "updated_state_forwarded": True,
        }
    )
    if phase == "serializer":
        transport, sizes = normalization.outline_serializer_field_sizes(transport)
        steps.extend(sizes)
        for item in sizes:
            transport, items = normalization.outline_effectful_branches(
                transport,
                item["function"],
                "usize",
                {
                    item["payload"]: ("&'a [u8]", False),
                    "out1": ("&'b mut [u8]", False),
                    "lo_ok": ("bool", False),
                    "hi_ok": ("bool", False),
                },
            )
            steps.extend(items)
    transport, items = normalization.normalize(transport)
    steps.extend(items)
    for item in items:
        for number, distribution in enumerate(item["certificate"]):
            fragments.append(
                {
                    "name": item["function"].replace("_", "")
                    + "Fragment"
                    + str(number),
                    "function": item["function"],
                    "rule": distribution["rule"],
                    "control": control(distribution["typed_leaf"]["source"]),
                }
            )
    for function in ("parse_initkex", "parse_kexresponse"):
        transport, helpers, item = normalization.outline_parse_checks(
            transport, function
        )
        transport += "\n" + "".join(helpers)
        steps.append(item)
    if phase == "serializer":
        for function in ("serialize_initkex", "serialize_kexresponse"):
            transport, item = normalization.normalize_serializer(transport, function)
            steps.append(item)
            fragments.append(
                {
                    "name": function.replace("_", "") + "Root",
                    "function": function,
                    "rule": item["rule"],
                    "control": control(item["root_expression"]),
                }
            )
            for number, distribution in enumerate(item["certificate"]):
                fragments.append(
                    {
                        "name": function.replace("_", "") + "Fragment" + str(number),
                        "function": function,
                        "rule": distribution["rule"],
                        "control": control(distribution["typed_leaf"]["source"]),
                    }
                )
        transport, items = normalization.eta_option_size_matches(transport)
        steps.extend(items)
    files[transport_name] = transport
    files[det_name], item = normalization.named_dispatcher(
        files[det_name], "cbor_det_destruct"
    )
    steps.append(item)
    return files, steps, fragments


def expected(root: Path, phase: str) -> tuple[dict[str, str], dict]:
    before = source_snapshot(root)
    original = original_sources(root)
    prepared, steps, fragments = transform(original, phase)
    checks = [
        check
        for item in steps
        if item.get("rule") == "typed-parse-check-outlining"
        for check in item["checks"]
    ]
    lean = certificate(fragments, checks)
    outputs = {**prepared, CERTIFICATE: lean}
    manifest = {
        "format": 1,
        "phase": phase,
        "source_sha256": before,
        "original_codec_sha256": ORIGINALS,
        "prepared_codec_sha256": {
            name: checkpoint.digest(value.encode()) for name, value in prepared.items()
        },
        "certificate_sha256": checkpoint.digest(lean.encode()),
        "transformation_steps": steps,
        "control_fragments": fragments,
        "state_helpers": checks,
        "semantic_normalization_endpoints": [
            "RegistrationCodecControlNormalization.cps_preserves",
            "RegistrationCodecArraySingleton.ofCell_toCell",
            "RegistrationCodecArraySingleton.toCell_ofCell",
            "RegistrationCodecArraySingleton.index_pack",
            "RegistrationCodecArraySingleton.update_pack",
            "RegistrationCodecArraySingleton.continuation_preserved",
            "RegistrationCodecArraySingleton.ignored_result_preserved",
        ],
        "source_correspondence_proved": False,
        "public_codec_law_proved": False,
        "production_generated_source_modified": False,
        "certificate_scope": "Exact source control normalization with arbitrary full-environment effects; no public codec readback or malformed-input law.",
    }
    if before != source_snapshot(root):
        raise ValueError("source changed during preparation")
    return outputs, json.loads(json.dumps(manifest))


def check_fixture(directory: Path, root: Path = ROOT) -> None:
    manifest = json.loads((directory / MANIFEST).read_text())
    outputs, expected_manifest = expected(root, manifest["phase"])
    if manifest != expected_manifest:
        raise ValueError("source transformation/certificate provenance drift")
    for name, value in outputs.items():
        if (directory / name).read_text() != value:
            raise ValueError("prepared source/certificate body drift: " + name)


def prepare(directory: Path, root: Path = ROOT, phase: str = "schema") -> None:
    directory = directory.resolve()
    if directory == root.resolve() or root.resolve() in directory.parents:
        raise ValueError("preparation destination must be outside the source worktree")
    if directory.exists():
        raise ValueError("preparation requires a new destination")
    outputs, manifest = expected(root, phase)
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
    for name, value in outputs.items():
        (directory / name).write_text(value)
    (directory / MANIFEST).write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    check_fixture(directory, root)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write-fixture", type=Path)
    mode.add_argument("--check-fixture", type=Path)
    parser.add_argument(
        "--phase", choices=("schema", "parser", "serializer"), default="schema"
    )
    args = parser.parse_args()
    try:
        if args.write_fixture:
            prepare(args.write_fixture, phase=args.phase)
            print(
                "Wrote isolated source preparation and finite control certificate; production source unchanged"
            )
        else:
            check_fixture(args.check_fixture)
            print(
                "Isolated source preparation and finite control certificate match exact original source"
            )
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
