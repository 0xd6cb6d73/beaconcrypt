#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Extract exact registration encoder controllers with explicit codec leaves.

The original generated Rust files remain unchanged. Exact field-expression
helper boundaries enable the pinned backend; every controller and thin serializer
wrapper body is retained. No codec law or primitive correctness axiom is installed.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile

import check_registration_codec_extraction as checkpoint
import extract_registration_primitives as primitives
import extract_registration_schema as schema
import extract_registration_shallow as shallow
import prepare_registration_serializer_source as preparation
from extract_frame_codec import configuration, isolated_work

ROOT = checkpoint.ROOT
SUBDIRECTORY = "BeaconcryptCore/RegistrationSerializerControllerExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
COHORT = "registration-serializer-source"
ENTRIES = preparation.ENTRIES
NAMESPACE = primitives.NAMESPACE
MODELS = {
    "TypesExternal.lean": "-- SPDX-License-Identifier: 0BSD\nimport BeaconcryptCore.RegistrationShallowExtraction.Types\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM\nset_option autoImplicit false\nset_option warningAsError true\nnamespace BeaconcryptCore.Refinement.RegistrationSerializerPrimitive\n/-! Explicit source codec calls. No functional law or security conclusion is a field.\nAll mutable slice poststates are returned. Concrete reachable source instances and\ncomplete public codec laws are discharged separately. -/\nclass Operations where\n  mkString : beaconcrypt_parse.cbordetver.cbor_det_string_kind → Slice U8 → RustM beaconcrypt_parse.cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177\n  sizeRaw : beaconcrypt_parse.cbordetveraux.cbor_raw → Slice Usize → RustM (Bool × Slice Usize)\n  serializeRaw : beaconcrypt_parse.cbordetveraux.cbor_raw → Slice U8 → Usize → RustM (Usize × Slice U8)\n  serializeArray : U64 → Slice U8 → Usize → RustM (Usize × Slice U8)\n  utf8Correct : Slice U8 → RustM Bool\nend BeaconcryptCore.Refinement.RegistrationSerializerPrimitive\n",
    "FunsExternal.lean": "-- SPDX-License-Identifier: 0BSD\nimport BeaconcryptCore.Extraction.Funs\nimport BeaconcryptCore.RegistrationSerializerControllerExtraction.Types\nimport BeaconcryptCore.RegistrationShallowExtraction.Funs\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM\nset_option autoImplicit false\nset_option warningAsError true\nnamespace beaconcrypt_parse.registration_serializer_primitive\nvariable [ops : BeaconcryptCore.Refinement.RegistrationSerializerPrimitive.Operations]\ndef mkString := ops.mkString\ndef sizeRaw := ops.sizeRaw\ndef serializeRaw := ops.serializeRaw\ndef serializeArray := ops.serializeArray\ndef utf8Correct := ops.utf8Correct\nend beaconcrypt_parse.registration_serializer_primitive\n",
}

INSTALLED = (
    "Types.lean",
    "Funs.lean",
    "TypesExternal.lean",
    "FunsExternal.lean",
    "external-signatures.json",
    "SourceCertificates.lean",
)
OPAQUE = (
    "cbordetveraux",
    "cbordetver::cbor_det_mk_string",
    "cbordetver::cbor_det_serialize_array",
    "cbordetver::cbor_impl_utf8_correct",
)
INCLUDED = (
    "mk_raw_uint64",
    "cbor_size",
    "cbor_serialize",
    "sizet_lte_u64",
    "u64_lte_sizet",
    "cbor_raw",
    "cbor_int",
    "cbor_string",
    "cbor_tagged",
    "cbor_array",
    "cbor_map",
    "cbor_map_entry",
    "cbor_serialized",
    "raw_uint64",
    "initial_byte_t",
    "long_argument",
    "header",
    "cbor_major_type_uint64",
    "cbor_major_type_neg_int64",
    "cbor_major_type_byte_string",
    "cbor_major_type_text_string",
    "cbor_major_type_array",
    "cbor_major_type_map",
    "cbor_major_type_tagged",
    "cbor_major_type_simple_value",
    "max_simple_value_additional_info",
)
TEMPLATE_SHA256 = {
    "TypesExternal_Template.lean": "c07da04e32da19a0f64c83b869e621e4ddee0450ebaf48e820b9c5aa1b828735",
    "FunsExternal_Template.lean": "2fc5c045e2b4b8f9b637136232022c26d949c1b903da8ccf667ecaddfa190ff2",
}
CALLS = {
    "cbordetver.cbor_det_mk_string": "registration_serializer_primitive.mkString",
    "cbordetveraux.ser·_d": "registration_serializer_primitive.serializeRaw",
    "cbordetveraux.siz·_d": "registration_serializer_primitive.sizeRaw",
    "cbordetver.cbor_det_serialize_array": "registration_serializer_primitive.serializeArray",
    "cbordetver.cbor_impl_utf8_correct": "registration_serializer_primitive.utf8Correct",
}
OPERATIONS_VARIABLE = "variable [BeaconcryptCore.Refinement.RegistrationSerializerPrimitive.Operations]\n\n"


def rename_calls(body: str, reverse: bool = False) -> str:
    changes = []
    masked = checkpoint.code(body.encode())
    for before, after in CALLS.items():
        before = primitives.identifiers(before)
        if reverse:
            before, after = after, before
        for found in re.finditer(
            r"(?<![\w])" + re.escape(before) + r"(?![\w])", masked
        ):
            changes.append((found.start(), found.end(), after))
    for start, end, after in sorted(changes, reverse=True):
        body = body[:start] + after + body[end:]
    return body


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = preparation.source_snapshot(root)
    for name in (
        "scripts/extract_registration_serializer.py",
        "scripts/extract_registration_primitives.py",
        "scripts/extract_registration_schema.py",
        "scripts/extract_registration_shallow.py",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    for directory in (primitives.DESTINATION, schema.DESTINATION, shallow.DESTINATION):
        for name in ("Types.lean", "Funs.lean", "provenance.json"):
            path = directory / name
            result[str(path.relative_to(ROOT))] = checkpoint.digest(path.read_bytes())
    return result


def shared_groups(name: str) -> dict[tuple[str, ...], tuple[str, str]]:
    result = {}
    for directory in (primitives.DESTINATION, schema.DESTINATION, shallow.DESTINATION):
        path = directory / name
        body = path.read_text().split(NAMESPACE)[1]
        for names, chunk in schema.chunks(body):
            if names in result:
                raise ValueError("ambiguous shared serializer-source declaration")
            result[names] = (str(path.relative_to(ROOT)), chunk)
    return result


def normalize(raw: bytes, name: str) -> tuple[str, dict]:
    checkpoint.checked_lean(raw, name)
    text = raw.decode()
    if text.count(NAMESPACE) != 1:
        raise ValueError("serializer-source namespace roster drift")
    header, body = text.split(NAMESPACE)
    original_header = header
    if not header.startswith("-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n"):
        raise ValueError("missing original Aeneas header")
    for linter in primitives.LINTERS:
        option = "set_option linter." + linter + " false\n"
        if header.count(option) != 1:
            raise ValueError("serializer-source linter roster drift")
        header = header.replace(option, "")
    if "set_option linter." in header or "set_option warningAsError" in header:
        raise ValueError("unreviewed serializer-source header option")
    last_import = header.rfind("\nimport ")
    last_end = header.index("\n", last_import + 1)
    header = (
        header[: last_end + 1]
        + "\nset_option warningAsError true\n"
        + header[last_end + 1 :]
    )
    if name == "Types.lean":
        for element, count in primitives.POSITIVE_FIELDS.items():
            original = "Slice " + element
            if body.count(original) != count:
                raise ValueError("serializer recursive-slice field roster drift")
            body = body.replace(original, primitives.POSITIVE_SLICE + " " + element)
    body = schema.qualified_names(primitives.identifiers(body))
    if name == "Funs.lean":
        body = rename_calls(body)
        header += OPERATIONS_VARIABLE
    shared = shared_groups(name)
    owners = {declaration: names for names in shared for declaration in names}
    ordered, retained, omitted = [], [], []
    for names, chunk in schema.chunks(body):
        matches = {owners[item] for item in names if item in owners}
        if matches:
            if matches != {names} or schema.tokens(chunk) != schema.tokens(
                shared[names][1]
            ):
                raise ValueError(
                    "shared serializer-source declaration drift: " + ",".join(names)
                )
            owner, canonical = shared[names]
            omitted.append(
                {
                    "names": list(names),
                    "source": chunk,
                    "owner": owner,
                    "shared_sha256": checkpoint.digest(canonical.encode()),
                }
            )
            ordered.append({"shared": len(omitted) - 1})
        else:
            retained.append(chunk)
            ordered.append({"retained": len(retained) - 1})
    result = header + NAMESPACE + "".join(retained) + "end beaconcrypt_parse\n"
    return result, {
        "raw_header": original_header,
        "normalized_header": header,
        "ordered_groups": ordered,
        "retained_groups": retained,
        "omitted_shared_groups": omitted,
        "raw_sha256": checkpoint.digest(raw),
    }


def assemble(generated: Path) -> tuple[dict[str, bytes], dict]:
    contents, evidence, templates = {}, {}, {}
    for name in ("Types.lean", "Funs.lean"):
        normalized, item = normalize((generated / name).read_bytes(), name)
        contents[name], evidence[name] = normalized.encode(), item
    for path in sorted(generated.glob("*_Template.lean")):
        source = path.read_bytes()
        if checkpoint.digest(source) != TEMPLATE_SHA256.get(path.name):
            raise ValueError("unreviewed serializer external signature")
        templates[path.name] = {
            "source": source.decode(),
            "sha256": checkpoint.digest(source),
        }
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("serializer-source external-template roster drift")
    contents.update({name: text.encode() for name, text in MODELS.items()})
    contents["external-signatures.json"] = (
        json.dumps(templates, indent=2, sort_keys=True) + "\n"
    ).encode()
    contents["SourceCertificates.lean"] = preparation.certificate(
        preparation.expected()[1]["field_boundaries"]
    ).encode()
    return contents, {"normalization": evidence, "external_templates": templates}


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    configuration(root)
    primitives.check_source(root)
    schema.check_source(root)
    shallow.check_source(root)
    provenance = json.loads((destination / "provenance.json").read_text())
    if provenance.get("source_sha256") != source_snapshot(root):
        raise ValueError("serializer-source source provenance drift")
    if (
        provenance.get("rust_start_from") != list(ENTRIES)
        or provenance.get("tools") != checkpoint.TOOLS
    ):
        raise ValueError("serializer-source entry/tool roster drift")
    primitives.hash_roster(
        provenance.get("tool_sha256"), set(checkpoint.TOOLS), "tool_sha256"
    )
    if (
        provenance.get("public_codec_law_proved") is not False
        or provenance.get("source_correspondence_proved") is not False
        or provenance.get("original_generated_source_unchanged") is not True
        or provenance.get("request_lifting_proved") is not False
        or provenance.get("opaque") != list(OPAQUE)
        or provenance.get("included") != list(INCLUDED)
    ):
        raise ValueError(
            "serializer-source component cannot assert complete codec/source closure"
        )
    _, expected_preparation = preparation.expected(root)
    if (destination / "SourceCertificates.lean").read_text() != preparation.certificate(
        expected_preparation["field_boundaries"]
    ):
        raise ValueError("serializer helper-boundary Lean certificate drift")
    if provenance.get("source_preparation") != expected_preparation:
        raise ValueError("serializer source preparation certificate drift")
    installed = provenance.get("installed_sha256")
    if not isinstance(installed, dict) or set(installed) != set(INSTALLED):
        raise ValueError("serializer-source installed roster drift")
    for name in INSTALLED:
        if checkpoint.digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError("serializer-source installed body drift")
    for name, text in MODELS.items():
        if (destination / name).read_text() != text:
            raise ValueError(
                "serializer-source Operations and bindings must match reviewed definitions"
            )
    for name in ("Types.lean", "Funs.lean"):
        item, groups = provenance["normalization"][name], []
        shared = shared_groups(name)
        for index in item["ordered_groups"]:
            if set(index) == {"retained"}:
                groups.append(item["retained_groups"][index["retained"]])
            elif set(index) == {"shared"}:
                omitted = item["omitted_shared_groups"][index["shared"]]
                names = tuple(omitted["names"])
                if (
                    names not in shared
                    or omitted["owner"] != shared[names][0]
                    or schema.tokens(omitted["source"])
                    != schema.tokens(shared[names][1])
                    or checkpoint.digest(shared[names][1].encode())
                    != omitted["shared_sha256"]
                ):
                    raise ValueError("serializer-source shared source drift")
                groups.append(omitted["source"])
            else:
                raise ValueError("malformed serializer-source reconstruction order")
        reconstructed_body = "".join(groups) + "end beaconcrypt_parse\n"
        if name == "Funs.lean":
            reconstructed_body = rename_calls(reconstructed_body, reverse=True)
        body = primitives.identifiers(
            schema.qualified_names(reconstructed_body, reverse=True),
            reverse=True,
        )
        if name == "Types.lean":
            for element in primitives.POSITIVE_FIELDS:
                body = body.replace(
                    primitives.POSITIVE_SLICE + " " + element, "Slice " + element
                )
        raw = (item["raw_header"] + NAMESPACE + body).encode()
        normalized, reconstructed = normalize(raw, name)
        if (
            normalized != (destination / name).read_text()
            or checkpoint.digest(raw) != item["raw_sha256"]
            or reconstructed != item
        ):
            raise ValueError(
                "serializer-source raw generated source reconstruction drift"
            )
    source = checkpoint.code((destination / "Funs.lean").read_bytes())
    for entry in ENTRIES:
        name = entry.replace("::", ".")
        if len(re.findall(r"^def " + re.escape(name) + r"\b", source, re.M)) != 1:
            raise ValueError("serializer-source entry point drift")
    templates = json.loads((destination / "external-signatures.json").read_text())
    if templates != provenance["external_templates"] or set(templates) != {
        "TypesExternal_Template.lean",
        "FunsExternal_Template.lean",
    }:
        raise ValueError("serializer-source external template evidence drift")
    for name, item in templates.items():
        if (
            set(item) != {"source", "sha256"}
            or item["sha256"] != TEMPLATE_SHA256[name]
            or checkpoint.digest(item["source"].encode()) != TEMPLATE_SHA256[name]
        ):
            raise ValueError("unreviewed serializer external signature")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--check-source", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument(
        "--tools-root",
        type=Path,
        default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
        / "hax/tools",
    )
    args = parser.parse_args()
    try:
        if args.check_source:
            check_source()
            print(
                "Prepared encoder source, codec-leaf signatures and generated cohort match"
            )
            return 0
        if args.work_dir is None or args.timeout <= 0:
            raise ValueError(
                "serializer-source extraction requires external work directory and positive timeout"
            )
        primitives.check_source()
        schema.check_source()
        shallow.check_source()
        before = source_snapshot()
        parent = isolated_work(args.work_dir)
        parent.mkdir(parents=True, exist_ok=True)
        work = Path(
            tempfile.mkdtemp(prefix="registration-serializer-source-", dir=parent)
        )
        fixture = work / "source"
        preparation.prepare(fixture)
        (fixture / "scripts").mkdir()
        for name in (
            "check_registration_codec_extraction.py",
            "extract_frame_codec.py",
        ):
            (fixture / "scripts" / name).write_bytes(
                (ROOT / "scripts" / name).read_bytes()
            )
        tools = {
            name: args.tools_root / name / version / name
            for name, version in checkpoint.TOOLS.items()
        }
        original_root, original_snapshot, original_subdirectory, original_commands = (
            checkpoint.ROOT,
            checkpoint.snapshot,
            checkpoint.SUBDIRECTORY,
            checkpoint.commands,
        )

        def commands(*args):
            charon, aeneas = original_commands(*args)
            position = charon.index("--dest-file")
            charon[position:position] = [
                "--opaque=beaconcrypt_parse::" + name for name in OPAQUE
            ] + [
                "--include=beaconcrypt_parse::cbordetveraux::" + name
                for name in INCLUDED
            ]
            return charon, aeneas

        try:
            checkpoint.ROOT, checkpoint.SUBDIRECTORY = fixture, SUBDIRECTORY
            checkpoint.snapshot = lambda: original_snapshot(fixture)
            checkpoint.commands = commands
            checkpoint.COHORTS[COHORT] = ENTRIES
            report = checkpoint.run(work, tools, COHORT, args.timeout, False)
        finally:
            (
                checkpoint.ROOT,
                checkpoint.snapshot,
                checkpoint.SUBDIRECTORY,
                checkpoint.commands,
            ) = (
                original_root,
                original_snapshot,
                original_subdirectory,
                original_commands,
            )
            checkpoint.COHORTS.pop(COHORT, None)
        preparation.check_fixture(fixture)
        if (
            any(row.get("returncode") != 0 for row in report["commands"])
            or len(report["commands"]) != 2
        ):
            raise ValueError(
                "serializer controller extraction blocked; " + str(work / "report.json")
            )
        for name in ("charon", "aeneas"):
            checkpoint.checked_diagnostics((work / (name + ".log")).read_text())
        contents, evidence = assemble(work / "generated" / SUBDIRECTORY)
        if before != source_snapshot():
            raise ValueError("serializer-source source changed during extraction")
        provenance = {
            "tools": checkpoint.TOOLS,
            "tool_sha256": report["tool_sha256"],
            "rust_start_from": list(ENTRIES),
            "source_sha256": before,
            **evidence,
            "installed_sha256": {
                name: checkpoint.digest(value) for name, value in contents.items()
            },
            "public_codec_law_proved": False,
            "source_correspondence_proved": False,
            "original_generated_source_unchanged": True,
            "request_lifting_proved": False,
            "opaque": list(OPAQUE),
            "included": list(INCLUDED),
            "source_preparation": preparation.expected()[1],
        }
        contents["provenance.json"] = (
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        ).encode()
        if args.write:
            DESTINATION.mkdir(parents=True, exist_ok=True)
            for name, value in contents.items():
                (DESTINATION / name).write_bytes(value)
            check_source()
            print(
                "Wrote original encoder controllers with explicit codec calls; complete codec source instances remain separate"
            )
        else:
            changed = [
                name
                for name, value in contents.items()
                if not (DESTINATION / name).is_file()
                or (DESTINATION / name).read_bytes() != value
            ]
            if changed:
                raise ValueError(
                    "serializer-source fresh extraction drift: " + ",".join(changed)
                )
            print("Serializer controller cohort matches fresh pinned extraction")
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
