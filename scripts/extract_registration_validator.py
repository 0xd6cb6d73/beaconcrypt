#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Extract actual canonical validators and registration parser controllers.

The original generated Rust files remain unchanged. Checked control, singleton
and helper boundaries enable the pinned backend. Actual schema bodies are
imported from their independently checked source extraction. No complete codec law is installed.
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
import extract_registration_header_optimal as optimal
import extract_registration_preflight as preflight
import prepare_registration_validator_source as preparation
from extract_frame_codec import configuration, isolated_work

ROOT = checkpoint.ROOT
SUBDIRECTORY = "BeaconcryptCore/RegistrationValidatorExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
COHORT = "registration-validator-source"
ENTRIES = preparation.ENTRIES
NAMESPACE = primitives.NAMESPACE
MODELS = {
    "TypesExternal.lean": "-- SPDX-License-Identifier: 0BSD\nimport BeaconcryptCore.RegistrationSchemaExtraction.Types\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM\nset_option autoImplicit false\nset_option warningAsError true\nnamespace BeaconcryptCore.Refinement.RegistrationValidatorPrimitive\n/-! Complete effects for text and map-only branches. No parser law is a field. -/\nclass Operations where\n  utf8Correct : Slice U8 → RustM Bool\n  sortedMap : Slice U8 → Slice U8 → U64 → RustM Bool\nend BeaconcryptCore.Refinement.RegistrationValidatorPrimitive\n",
    "FunsExternal.lean": "-- SPDX-License-Identifier: 0BSD\nimport BeaconcryptCore.RegistrationValidatorExtraction.Types\nimport BeaconcryptCore.RegistrationSchemaExtraction.Funs\nimport BeaconcryptCore.RegistrationHeaderOptimalExtraction.Funs\nimport BeaconcryptCore.RegistrationPreflightExtraction.Funs\nopen CoreModels Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen RustM\nset_option autoImplicit false\nset_option warningAsError true\nnamespace beaconcrypt_parse.registration_validator_primitive\nvariable [ops : BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations]\ndef utf8Correct := ops.utf8Correct\ndef sortedMap := ops.sortedMap\ndef preflightSlice (input start fields : Slice U8) : RustM (core.option.Option Unit) := do\n  let copied ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from\n    6#usize core.U8.Insts.CoreMarkerCopy fields\n  match copied with\n  | .Err _ => fail .panic\n  | .Ok values => beaconcrypt_parse.preflight input start values\nend beaconcrypt_parse.registration_validator_primitive\n",
}

INSTALLED = (
    "Types.lean",
    "Funs.lean",
    "TypesExternal.lean",
    "FunsExternal.lean",
    "external-signatures.json",
)
OPAQUE = (
    "preflight",
    "cbordetveraux::impl_correct",
    "cbordetveraux::extraction_sorted_map_scan",
    "transport::validate_initkex",
    "transport::parse_initkex",
    "transport::validate_kexresponse",
    "transport::parse_kexresponse",
)
INCLUDED = ()

TEMPLATE_SHA256 = {
    "FunsExternal_Template.lean": "fb1b6283a6fb29121a2ac0e11d7e7f5ce0cc3b9099a3059d266604bcc6b1acb0",
    "TypesExternal_Template.lean": "c07da04e32da19a0f64c83b869e621e4ddee0450ebaf48e820b9c5aa1b828735",
}
CALLS = {
    "preflight": "registration_validator_primitive.preflightSlice",
    "cbordetveraux.impl_correct": "registration_validator_primitive.utf8Correct",
    "cbordetveraux.extraction_sorted_map_scan": "registration_validator_primitive.sortedMap",
}

OPERATIONS_VARIABLE = "variable [BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations]\n\n"


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
    result = preparation.reviewed.source_snapshot(root)
    for name in (
        "scripts/extract_registration_validator.py",
        "scripts/extract_registration_header_optimal.py",
        "scripts/prepare_registration_validator_source.py",
        "scripts/test_extract_registration_validator.py",
        "scripts/test_prepare_registration_validator_source.py",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationPublicDecoderControl.lean",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    for directory in (
        primitives.DESTINATION,
        schema.DESTINATION,
        optimal.DESTINATION,
        preflight.DESTINATION,
    ):
        for name in ("Types.lean", "Funs.lean", "provenance.json"):
            path = directory / name
            result[str(path.relative_to(ROOT))] = checkpoint.digest(path.read_bytes())
    return result


def shared_groups(name: str) -> dict[tuple[str, ...], tuple[str, str]]:
    result = {}
    for directory in (
        primitives.DESTINATION,
        schema.DESTINATION,
        optimal.DESTINATION,
        preflight.DESTINATION,
    ):
        path = directory / name
        body = path.read_text().split(NAMESPACE)[1]
        if checkpoint.code(body.encode()).strip() == "end beaconcrypt_parse":
            continue
        for names, chunk in schema.chunks(body):
            if names in result:
                raise ValueError("ambiguous shared validator-source declaration")
            result[names] = (str(path.relative_to(ROOT)), chunk)
    return result


def unused_ignore(body: str, reverse: bool = False) -> str:
    groups = [
        (names, chunk)
        for names, chunk in schema.chunks(body)
        if names == ("lowstar.ignore.bcSchemaRepeatedIgnore2",)
    ]
    if len(groups) != 1:
        raise ValueError("validator ignored-value declaration roster drift")
    chunk = groups[0][1]
    before, after = ("_t", "t") if reverse else ("t", "_t")
    expression = chunk.split(":=", 1)[1]
    if re.search(
        r"(?<![\w])" + before + r"(?![\w])", checkpoint.code(expression.encode())
    ):
        raise ValueError("ignored value gained a reference")
    binder = "(" + before + " :"
    if chunk.count(binder) != 1:
        raise ValueError("ignored value binder drift")
    return body.replace(chunk, chunk.replace(binder, "(" + after + " :", 1), 1)


def normalize(raw: bytes, name: str) -> tuple[str, dict]:
    checkpoint.checked_lean(raw, name)
    text = raw.decode()
    if text.count(NAMESPACE) != 1:
        raise ValueError("validator-source namespace roster drift")
    header, body = text.split(NAMESPACE)
    original_header = header
    if not header.startswith("-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n"):
        raise ValueError("missing original Aeneas header")
    for linter in primitives.LINTERS:
        option = "set_option linter." + linter + " false\n"
        if header.count(option) != 1:
            raise ValueError("validator-source linter roster drift")
        header = header.replace(option, "")
    if "set_option linter." in header or "set_option warningAsError" in header:
        raise ValueError("unreviewed validator-source header option")
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
    if name == "Funs.lean":
        if body.count("let __anf0 ←") != 4:
            raise ValueError("validator Boolean binding roster drift")
        body = body.replace("let __anf0 ←", "let __anf0 : Bool ←")
    body = schema.qualified_names(primitives.identifiers(body))
    if name == "Funs.lean":
        body = rename_calls(unused_ignore(body))
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
                    "shared validator-source declaration drift: " + ",".join(names)
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
        raise ValueError("validator-source external-template roster drift")
    contents.update({name: text.encode() for name, text in MODELS.items()})
    contents["external-signatures.json"] = (
        json.dumps(templates, indent=2, sort_keys=True) + "\n"
    ).encode()
    return contents, {"normalization": evidence, "external_templates": templates}


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    configuration(root)
    primitives.check_source(root)
    schema.check_source(root)
    optimal.check_source(root)
    preflight.check_source(root)
    provenance = json.loads((destination / "provenance.json").read_text())
    if set(provenance) != {
        "tools",
        "tool_sha256",
        "rust_start_from",
        "source_sha256",
        "normalization",
        "external_templates",
        "installed_sha256",
        "public_codec_law_proved",
        "source_correspondence_proved",
        "original_generated_source_unchanged",
        "request_lifting_proved",
        "opaque",
        "included",
        "source_preparation",
    }:
        raise ValueError("validator provenance metadata roster changed")

    if provenance.get("source_sha256") != source_snapshot(root):
        raise ValueError("validator-source source provenance drift")
    if (
        provenance.get("rust_start_from") != list(ENTRIES)
        or provenance.get("tools") != checkpoint.TOOLS
    ):
        raise ValueError("validator-source entry/tool roster drift")
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
            "validator-source component cannot assert complete codec/source closure"
        )
    _, expected_preparation = preparation.expected(root)
    if provenance.get("source_preparation") != expected_preparation:
        raise ValueError("serializer source preparation certificate drift")
    installed = provenance.get("installed_sha256")
    if not isinstance(installed, dict) or set(installed) != set(INSTALLED):
        raise ValueError("validator-source installed roster drift")
    for name in INSTALLED:
        if checkpoint.digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError("validator-source installed body drift")
    for name, text in MODELS.items():
        if (destination / name).read_text() != text:
            raise ValueError(
                "validator-source Operations and bindings must match reviewed definitions"
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
                    raise ValueError("validator-source shared source drift")
                groups.append(omitted["source"])
            else:
                raise ValueError("malformed validator-source reconstruction order")
        reconstructed_body = "".join(groups) + "end beaconcrypt_parse\n"
        if name == "Funs.lean":
            reconstructed_body = unused_ignore(
                rename_calls(reconstructed_body, reverse=True), reverse=True
            )
        body = primitives.identifiers(
            schema.qualified_names(reconstructed_body, reverse=True),
            reverse=True,
        )
        if name == "Funs.lean":
            if body.count("let __anf0 : Bool ←") != 4:
                raise ValueError("validator Boolean reconstruction drift")
            body = body.replace("let __anf0 : Bool ←", "let __anf0 ←")
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
                "validator-source raw generated source reconstruction drift"
            )
    source = checkpoint.code((destination / "Funs.lean").read_bytes())
    for entry in ENTRIES:
        name = entry.replace("::", ".")
        if len(re.findall(r"^def " + re.escape(name) + r"\b", source, re.M)) != 1:
            raise ValueError("validator-source entry point drift")
    templates = json.loads((destination / "external-signatures.json").read_text())
    if templates != provenance["external_templates"] or set(templates) != {
        "TypesExternal_Template.lean",
        "FunsExternal_Template.lean",
    }:
        raise ValueError("validator-source external template evidence drift")
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
                "Prepared parser source, text/map leaf signatures and generated cohort match"
            )
            return 0
        if args.work_dir is None or args.timeout <= 0:
            raise ValueError(
                "validator-source extraction requires external work directory and positive timeout"
            )
        primitives.check_source()
        schema.check_source()
        optimal.check_source()
        preflight.check_source()
        before = source_snapshot()
        parent = isolated_work(args.work_dir)
        parent.mkdir(parents=True, exist_ok=True)
        work = Path(
            tempfile.mkdtemp(prefix="registration-validator-source-", dir=parent)
        )
        fixture = work / "source"
        preparation.prepare(fixture)
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
                "validator controller extraction blocked; " + str(work / "report.json")
            )
        for name in ("charon", "aeneas"):
            checkpoint.checked_diagnostics((work / (name + ".log")).read_text())
        contents, evidence = assemble(work / "generated" / SUBDIRECTORY)
        if before != source_snapshot():
            raise ValueError("validator-source source changed during extraction")
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
                "Wrote original parser controllers with explicit codec calls; complete codec source instances remain separate"
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
                    "validator-source fresh extraction drift: " + ",".join(changed)
                )
            print("Validator controller cohort matches fresh pinned extraction")
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
