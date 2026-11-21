#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Extract actual generated registration schema validators and field projections.

The byte-input deterministic CBOR dispatcher and public codec laws remain separate.
Shared primitive declarations must match the existing strict cohort token for
token. No source body is made opaque and external templates must be empty.
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
import prepare_registration_codec_source as preparation
from extract_frame_codec import configuration, isolated_work

ROOT = checkpoint.ROOT
SUBDIRECTORY = "BeaconcryptCore/RegistrationSchemaExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
CERTIFICATE_DESTINATION = (
    ROOT
    / "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationCodecSourceCertificates.lean"
)
COHORT = "registration-schema"
ENTRIES = (
    "transport::validate_initkex",
    "transport::validate_kexresponse",
    "transport::parse_initkex",
    "transport::parse_kexresponse",
)
MODELS = {
    "TypesExternal.lean": "import BeaconcryptCore.RegistrationPrimitiveExtraction.Types\n\nset_option warningAsError true\n",
    "FunsExternal.lean": "import BeaconcryptCore.RegistrationSchemaExtraction.Types\nimport BeaconcryptCore.RegistrationPrimitiveExtraction.Funs\nimport BeaconcryptCore.Refinement.RegistrationPrimitivePlatform\n\nset_option warningAsError true\n",
}
NAMESPACE = "namespace beaconcrypt_parse\n"
INSTALLED = (
    "Types.lean",
    "Funs.lean",
    "TypesExternal.lean",
    "FunsExternal.lean",
    "external-signatures.json",
)


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = preparation.source_snapshot(root)
    for name in (
        "scripts/extract_registration_schema.py",
        "scripts/extract_registration_primitives.py",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/RegistrationPrimitiveExtraction/Types.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/RegistrationPrimitiveExtraction/Funs.lean",
        "beaconcrypt-core/proofs/lean/BeaconcryptCore/RegistrationPrimitiveExtraction/provenance.json",
    ):
        result[name] = checkpoint.digest((root / name).read_bytes())
    return result


def tokens(source: str) -> tuple[str, ...]:
    result, index = [], 0
    while index < len(source):
        if source[index].isspace():
            index += 1
        elif source.startswith("--", index):
            stop = source.find("\n", index)
            index = len(source) if stop < 0 else stop
        elif source.startswith("/-", index):
            depth = 1
            index += 2
            while depth and index < len(source):
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("unclosed Lean comment")
        elif source[index] == '"':
            start = index
            index += 1
            while index < len(source):
                if source[index] == "\\":
                    index += 2
                elif source[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            else:
                raise ValueError("unclosed Lean string")
            result.append(source[start:index])
        else:
            match = re.match(r"[\w'·]+|.", source[index:])
            result.append(match[0])
            index += len(match[0])
    return tuple(result)


def chunks(body: str) -> list[tuple[tuple[str, ...], str]]:
    if not body.endswith("end beaconcrypt_parse\n"):
        raise ValueError("unreviewed generated namespace ending")
    body = body[: -len("end beaconcrypt_parse\n")]
    lines = body.splitlines(keepends=True)
    offsets, total = [], 0
    for line in lines:
        offsets.append(total)
        total += len(line)
    declarations, mutual = [], 0
    for index, line in enumerate(lines):
        if line.strip() == "mutual":
            if mutual:
                raise ValueError("nested Lean mutual group")
            declarations.append((index, None))
            mutual = 1
        elif line.strip() == "end" and mutual:
            mutual = 0
        elif not mutual:
            found = re.match(
                r"^(?:def|theorem|structure|inductive)\s+([^\s(:]+)",
                "".join(lines[index : index + 2]),
            )
            if found:
                declarations.append((index, found[1]))
    if mutual or not declarations:
        raise ValueError("malformed generated declaration groups")
    starts = []
    for line, name in declarations:
        first = line
        while first and (
            not lines[first - 1].strip() or lines[first - 1].startswith("@[")
        ):
            first -= 1
        if first and lines[first - 1].rstrip().endswith("-/"):
            first -= 1
            while first and not lines[first].lstrip().startswith("/--"):
                first -= 1
            if not lines[first].lstrip().startswith("/--"):
                raise ValueError("unrecognized declaration comment")
        starts.append(offsets[first])
    if any(left >= right for left, right in zip(starts, starts[1:])):
        raise ValueError("overlapping declaration groups")
    if tokens(body[: starts[0]]):
        raise ValueError("unrecognized generated namespace prefix")
    starts[0] = 0
    result = []
    for index, start in enumerate(starts):
        stop = starts[index + 1] if index + 1 < len(starts) else len(body)
        chunk = body[start:stop]
        names = tuple(
            re.findall(
                r"^(?:def|theorem|structure|inductive)\s+([^\s(:]+)", chunk, re.M
            )
        )
        if not names:
            raise ValueError("declaration group without a name")
        result.append((names, chunk))
    if tokens(body[: starts[0]]):
        raise ValueError("unrecognized generated namespace prefix")
    return result


REPEATED_PREFIXES = {
    "closure": "bcSchemaRepeatedClosure",
    "ignore": "bcSchemaRepeatedIgnore",
}


def qualified_names(source: str, *, reverse: bool = False) -> str:
    changes = []
    pattern = r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)+"
    for found in re.finditer(pattern, checkpoint.code(source.encode())):
        original = source[found.start() : found.end()]
        seen, result = {}, []
        for component in original.split("."):
            encoded = [
                (name, prefix)
                for name, prefix in REPEATED_PREFIXES.items()
                if component.startswith(prefix)
            ]
            if encoded:
                name, prefix = encoded[0]
                ordinal = component[len(prefix) :]
                if (
                    not reverse
                    or not ordinal.isdigit()
                    or int(ordinal) != seen.get(name, 0) + 1
                    or int(ordinal) < 2
                ):
                    raise ValueError("malformed/colliding repeated namespace name")
                component = name
            seen[component] = seen.get(component, 0) + 1
            if not reverse and seen[component] > 1:
                if component not in REPEATED_PREFIXES:
                    raise ValueError("unreviewed repeated generated namespace")
                result.append(REPEATED_PREFIXES[component] + str(seen[component]))
            else:
                result.append(component)
        replacement = ".".join(result)
        if replacement != original:
            changes.append((found.start(), found.end(), replacement))
    for begin, end, replacement in reversed(changes):
        source = source[:begin] + replacement + source[end:]
    return source


def unused_binders(body: str, *, reverse: bool = False) -> str:
    changes = []
    for names, chunk in chunks(body):
        if len(names) != 1:
            continue
        name = names[0]
        if name == "lowstar.ignore.bcSchemaRepeatedIgnore2":
            binder = "t"
        elif re.match(
            r"transport\.validate_(?:initkex|kexresponse)\.closure\.Insts\.", name
        ) and name.endswith(".call"):
            binder = "c"
        else:
            continue
        before = "_" + binder if reverse else binder
        after = binder if reverse else "_" + binder
        expression = chunk.split(":=", 1)[1]
        if re.search(
            r"(?<![\w])" + re.escape(before) + r"(?![\w])",
            checkpoint.code(expression.encode()),
        ):
            raise ValueError("reviewed unused binder gained a body reference")
        original = "(" + before + " :"
        if chunk.count(original) != 1:
            raise ValueError("unused generated binder roster drift")
        changes.append((chunk, chunk.replace(original, "(" + after + " :", 1)))
    if len(changes) != 3:
        raise ValueError("unused binder cohort changed")
    for before, after in changes:
        body = body.replace(before, after, 1)
    return body


def normalize(raw: bytes, name: str) -> tuple[str, dict]:
    checkpoint.checked_lean(raw, name)
    text = raw.decode()
    if text.count(NAMESPACE) != 1:
        raise ValueError("schema namespace roster drift")
    header, body = text.split(NAMESPACE)
    if not header.startswith("-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n"):
        raise ValueError("missing generated header")
    for linter in primitives.LINTERS:
        option = "set_option linter." + linter + " false\n"
        if header.count(option) != 1:
            raise ValueError("schema linter roster drift")
        header = header.replace(option, "")
    if "set_option linter." in header or "set_option warningAsError" in header:
        raise ValueError("unreviewed schema option")
    last_import = header.rfind("\nimport ")
    last_import_end = header.index("\n", last_import + 1)
    header = (
        header[: last_import_end + 1]
        + "\nset_option warningAsError true\n"
        + header[last_import_end + 1 :]
    )
    body = qualified_names(primitives.identifiers(body))
    if name == "Types.lean":
        for element, count in primitives.POSITIVE_FIELDS.items():
            if body.count("Slice " + element) < count:
                raise ValueError("missing recursive slice representation sites")
            body = body.replace(
                "Slice " + element, primitives.POSITIVE_SLICE + " " + element, count
            )
    else:
        body = unused_binders(body)
    shared_body = (primitives.DESTINATION / name).read_text().split(NAMESPACE)[1]
    shared = {names: chunk for names, chunk in chunks(shared_body)}
    owners = {declaration: names for names in shared for declaration in names}
    ordered, retained, omitted = [], [], []
    for names, chunk in chunks(body):
        matches = {owners[name] for name in names if name in owners}
        if matches:
            if matches != {names} or tokens(chunk) != tokens(shared[names]):
                raise ValueError("shared primitive body/type drift: " + ",".join(names))
            omitted.append(
                {
                    "names": names,
                    "source": chunk,
                    "shared_sha256": checkpoint.digest(shared[names].encode()),
                }
            )
            ordered.append({"shared": len(omitted) - 1})
        else:
            retained.append(chunk)
            ordered.append({"retained": len(retained) - 1})
    installed = header + NAMESPACE + "".join(retained) + "end beaconcrypt_parse\n"
    return installed, {
        "raw_header": text.split(NAMESPACE)[0],
        "normalized_header": header,
        "ordered_groups": ordered,
        "retained_groups": retained,
        "omitted_shared_groups": omitted,
        "raw_sha256": checkpoint.digest(raw),
    }


def assemble(generated: Path) -> tuple[dict[str, bytes], dict]:
    contents, normalization, templates = {}, {}, {}
    for name in ("Types.lean", "Funs.lean"):
        text, evidence = normalize((generated / name).read_bytes(), name)
        contents[name] = text.encode()
        normalization[name] = evidence
    functions = checkpoint.code(contents["Funs.lean"])
    for entry in ENTRIES:
        if (
            len(
                re.findall(
                    r"^def " + re.escape(entry.replace("::", ".")) + r"\b",
                    functions,
                    re.M,
                )
            )
            != 1
        ):
            raise ValueError("missing schema entry point")
    for path in sorted(generated.glob("*_Template.lean")):
        value = path.read_bytes()
        checkpoint.checked_template(value)
        templates[path.name] = {
            "source": value.decode(),
            "sha256": checkpoint.digest(value),
        }
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("schema external-template roster drift")
    contents.update({name: value.encode() for name, value in MODELS.items()})
    contents["external-signatures.json"] = (
        json.dumps(templates, indent=2, sort_keys=True) + "\n"
    ).encode()
    return contents, {"normalization": normalization, "external_templates": templates}


def check_source(
    root: Path = ROOT,
    destination: Path = DESTINATION,
    certificate_path: Path = CERTIFICATE_DESTINATION,
) -> None:
    configuration(root)
    primitives.check_source(root)
    provenance = json.loads((destination / "provenance.json").read_text())
    if provenance.get("source_sha256") != source_snapshot(root):
        raise ValueError("schema source provenance drift")
    if (
        provenance.get("rust_start_from") != list(ENTRIES)
        or provenance.get("tools") != checkpoint.TOOLS
    ):
        raise ValueError("schema entry/tool roster drift")
    primitives.hash_roster(
        provenance.get("tool_sha256"), set(checkpoint.TOOLS), "tool_sha256"
    )
    if provenance.get("public_codec_law_proved") is not False:
        raise ValueError("schema extraction cannot assert a public codec law")
    outputs, manifest = preparation.expected(root, "schema")
    if provenance.get("source_preparation") != manifest:
        raise ValueError("schema source transformation drift")
    if certificate_path.read_text() != outputs[preparation.CERTIFICATE]:
        raise ValueError("schema finite control certificate drift")
    installed = provenance.get("installed_sha256")
    if not isinstance(installed, dict) or set(installed) != set(INSTALLED):
        raise ValueError("schema installed roster drift")
    for name in INSTALLED:
        if checkpoint.digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError("schema installed body drift")
    for name, value in MODELS.items():
        if (destination / name).read_text() != value:
            raise ValueError("schema external files must contain imports only")
    for name in ("Types.lean", "Funs.lean"):
        evidence = provenance["normalization"][name]
        groups = []
        shared_body = (primitives.DESTINATION / name).read_text().split(NAMESPACE)[1]
        shared = {names: chunk for names, chunk in chunks(shared_body)}
        for item in evidence["ordered_groups"]:
            if set(item) == {"retained"}:
                groups.append(evidence["retained_groups"][item["retained"]])
            elif set(item) == {"shared"}:
                omitted = evidence["omitted_shared_groups"][item["shared"]]
                names = tuple(omitted["names"])
                if (
                    names not in shared
                    or tokens(omitted["source"]) != tokens(shared[names])
                    or checkpoint.digest(shared[names].encode())
                    != omitted["shared_sha256"]
                ):
                    raise ValueError("schema shared declaration drift")
                groups.append(omitted["source"])
            else:
                raise ValueError("malformed schema declaration reconstruction")
        body = "".join(groups) + "end beaconcrypt_parse\n"
        if name == "Funs.lean":
            body = unused_binders(body, reverse=True)
        body = primitives.identifiers(qualified_names(body, reverse=True), reverse=True)
        if name == "Types.lean":
            for element in primitives.POSITIVE_FIELDS:
                body = body.replace(
                    primitives.POSITIVE_SLICE + " " + element, "Slice " + element
                )
        raw = (evidence["raw_header"] + NAMESPACE + body).encode()
        normalized, reproduced = normalize(raw, name)
        if (
            normalized != (destination / name).read_text()
            or checkpoint.digest(raw) != evidence["raw_sha256"]
            or json.loads(json.dumps(reproduced)) != evidence
        ):
            raise ValueError("schema generated-source reconstruction drift")
    functions = checkpoint.code((destination / "Funs.lean").read_bytes())
    for entry in ENTRIES:
        if (
            len(
                re.findall(
                    r"^def " + re.escape(entry.replace("::", ".")) + r"\b",
                    functions,
                    re.M,
                )
            )
            != 1
        ):
            raise ValueError("schema installed entry-point roster drift")
    templates = json.loads((destination / "external-signatures.json").read_text())
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("schema external-template evidence roster drift")
    if templates != provenance["external_templates"]:
        raise ValueError("schema external-template evidence drift")
    for item in templates.values():
        checkpoint.checked_template(item["source"].encode())
        if checkpoint.digest(item["source"].encode()) != item["sha256"]:
            raise ValueError("schema external-template hash drift")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--write", action="store_true")
    modes.add_argument("--check", action="store_true")
    modes.add_argument("--check-source", action="store_true")
    parser.add_argument("--work-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
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
                "Generated registration schema source, preparation and strict cohort match"
            )
            return 0
        if args.work_dir is None or args.timeout <= 0:
            raise ValueError(
                "extraction requires external work directory and positive timeout"
            )
        primitives.check_source()
        before = source_snapshot()
        parent = isolated_work(args.work_dir)
        parent.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="registration-schema-", dir=parent))
        fixture = work / "source"
        preparation.prepare(fixture)
        (fixture / "scripts").mkdir()
        for name in (
            "check_registration_codec_extraction.py",
            "extract_frame_codec.py",
        ):
            shutil_copy = ROOT / "scripts" / name
            (fixture / "scripts" / name).write_bytes(shutil_copy.read_bytes())
        tools = {
            name: args.tools_root / name / version / name
            for name, version in checkpoint.TOOLS.items()
        }
        original_root, original_snapshot, original_subdirectory = (
            checkpoint.ROOT,
            checkpoint.snapshot,
            checkpoint.SUBDIRECTORY,
        )
        try:
            checkpoint.ROOT = fixture
            checkpoint.snapshot = lambda: original_snapshot(fixture)
            checkpoint.SUBDIRECTORY = SUBDIRECTORY
            checkpoint.COHORTS[COHORT] = ENTRIES
            report = checkpoint.run(work, tools, COHORT, args.timeout, False)
        finally:
            checkpoint.ROOT = original_root
            checkpoint.snapshot = original_snapshot
            checkpoint.SUBDIRECTORY = original_subdirectory
            checkpoint.COHORTS.pop(COHORT, None)
        if report["status"] != "extracted-without-external-obligations":
            raise ValueError(
                "schema extraction blocked: "
                + str(report.get("error"))
                + "; "
                + str(work / "report.json")
            )
        contents, evidence = assemble(work / "generated" / SUBDIRECTORY)
        outputs, manifest = preparation.expected(ROOT, "schema")
        if before != source_snapshot():
            raise ValueError("schema source changed during extraction")
        provenance = {
            "tools": checkpoint.TOOLS,
            "tool_sha256": report["tool_sha256"],
            "rust_start_from": ENTRIES,
            "source_sha256": before,
            "source_preparation": manifest,
            **evidence,
            "installed_sha256": {
                name: checkpoint.digest(value) for name, value in contents.items()
            },
            "public_codec_law_proved": False,
        }
        contents["provenance.json"] = (
            json.dumps(provenance, indent=2, sort_keys=True) + "\n"
        ).encode()
        if args.write:
            DESTINATION.mkdir(parents=True, exist_ok=True)
            for name, value in contents.items():
                (DESTINATION / name).write_bytes(value)
            CERTIFICATE_DESTINATION.write_text(outputs[preparation.CERTIFICATE])
            check_source()
            print(
                "Wrote actual schema validators/projections and finite source control certificate; public byte codecs remain separate"
            )
        else:
            changed = [
                name
                for name, value in contents.items()
                if not (DESTINATION / name).is_file()
                or (DESTINATION / name).read_bytes() != value
            ]
            if changed:
                raise ValueError("schema fresh-extraction drift: " + ",".join(changed))
            print("Actual schema validators/projections match fresh pinned extraction")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
