#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Extract unchanged generated CBOR primitives for registration correspondence.

The public registration dispatcher remains a separate obligation. This cohort
contains actual generated header, raw-value and leaf-count operations, with no
opaque parser operation or external correctness assumption.
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
from extract_frame_codec import configuration, hash_roster, isolated_work

ROOT = checkpoint.ROOT
SUBDIRECTORY = "BeaconcryptCore/RegistrationPrimitiveExtraction"
DESTINATION = ROOT / "beaconcrypt-core/proofs/lean" / SUBDIRECTORY
ENTRIES = (
    "cbordetveraux::read_header",
    "cbordetveraux::jump_header",
    "cbordetveraux::argument_as_uint64",
    "cbordetveraux::cbor_read",
    "cbordetveraux::validate_header",
    "cbordetveraux::validate_recursive_step_count_leaf",
    "cbordetveraux::write_header",
    "transport::initkex_right",
    "transport::kexresponse_right",
    "cbordetver::cbor_det_mk_int64",
    "cbordetveraux::compute_deep",
    "cbordetveraux::raw_uint64_as_argument",
    "cbordetveraux::mk_raw_uint64",
)
COHORT = "registration-primitives"
NAMESPACE = "namespace beaconcrypt_parse\n"
LINTERS = (
    "dupNamespace",
    "hashCommand",
    "unusedVariables",
    "style.whitespace",
    "style.setOption",
    "style.longLine",
)
POSITIVE_SLICE = "BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice"
POSITIVE_FIELDS = {"cbordetveraux.cbor_raw": 4, "cbordetveraux.cbor_map_entry": 2}
SLICE_COERCIONS = {
    "core.slice.Slice.len ca.cbor_array_ptr": "core.slice.Slice.len (ca.cbor_array_ptr : Slice cbordetveraux.cbor_raw)",
    "core.slice.Slice.len cm.cbor_map_ptr": "core.slice.Slice.len (cm.cbor_map_ptr : Slice cbordetveraux.cbor_map_entry)",
}
TRANSFORMATION = {
    "kind": "strict-header-and-positive-recursive-slice-representation",
    "linter_options": list(LINTERS),
    "positive_slice_fields": POSITIVE_FIELDS,
    "slice_isomorphism": [
        "BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice.toSlice_ofSlice",
        "BeaconcryptCore.Refinement.RegistrationPositiveSlice.PositiveSlice.ofSlice_toSlice",
    ],
    "identifier_encoding": "bcExtractedToken + UTF-8 hex for generated identifiers containing double underscores or middle dots",
    "restored_bool_bindings": {"__anf0": 2},
    "positive_slice_coercions": SLICE_COERCIONS,
}
MODELS = {
    "TypesExternal.lean": "import BeaconcryptCore.Refinement.RegistrationPositiveSlice\n\nset_option warningAsError true\n",
    "FunsExternal.lean": "import BeaconcryptCore.RegistrationPrimitiveExtraction.Types\nimport BeaconcryptCore.Refinement.RegistrationPrimitivePlatform\n\nset_option warningAsError true\n",
}
INSTALLED = (
    "Types.lean",
    "Funs.lean",
    "TypesExternal.lean",
    "FunsExternal.lean",
    "external-signatures.json",
)


def source_snapshot(root: Path = ROOT) -> dict[str, str]:
    result = checkpoint.snapshot(root)
    name = "scripts/extract_registration_primitives.py"
    result[name] = checkpoint.digest((root / name).read_bytes())
    name = "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationPositiveSlice.lean"
    result[name] = checkpoint.digest((root / name).read_bytes())
    name = "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/RegistrationPrimitivePlatform.lean"
    result[name] = checkpoint.digest((root / name).read_bytes())
    return result


IDENTIFIER = re.compile(
    r"«[^»\n]+»|[A-Za-z_·\u00c0-\uffff][A-Za-z0-9_'·\u00c0-\uffff]*"
)
TOKEN_PREFIX = "bcExtractedToken"


def identifiers(value: str, *, reverse: bool = False) -> str:
    """Bijective token renaming, leaving comments, strings and operators alone."""
    masked = checkpoint.code(value.encode())
    changes = []
    for match in IDENTIFIER.finditer(masked):
        token = value[match.start() : match.end()]
        if reverse:
            if not token.startswith(TOKEN_PREFIX):
                continue
            try:
                original = bytes.fromhex(token[len(TOKEN_PREFIX) :]).decode()
            except (ValueError, UnicodeError):
                raise ValueError("malformed normalized primitive identifier") from None
            if "__" not in original and "·" not in original:
                raise ValueError("unreviewed normalized primitive identifier")
            replacement = original
        else:
            if token.startswith(TOKEN_PREFIX):
                raise ValueError(
                    "raw primitive identifier collides with encoding namespace"
                )
            if "__" not in token and "·" not in token:
                continue
            if token == "·":
                continue
            if not token.startswith("«") and not token.replace("'", "_").isidentifier():
                raise ValueError("unsupported generated identifier token")
            replacement = TOKEN_PREFIX + token.encode().hex()
        changes.append((match.start(), match.end(), replacement))
    for start, end, replacement in reversed(changes):
        value = value[:start] + replacement + value[end:]
    return value


def normalize(value: bytes, name: str) -> tuple[bytes, str]:
    checkpoint.checked_lean(value, name)
    text = value.decode()
    if text.count(NAMESPACE) != 1:
        raise ValueError("unexpected generated primitive namespace")
    header, body = text.split(NAMESPACE, 1)
    if not header.startswith("-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n"):
        raise ValueError("missing generated primitive header")
    for linter in LINTERS:
        directive = f"set_option linter.{linter} false\n"
        if header.count(directive) != 1:
            raise ValueError("unexpected generated primitive linter-option roster")
        header = header.replace(directive, "")
    if "set_option linter." in header or "set_option warningAsError" in header:
        raise ValueError("unreviewed generated primitive header option")
    if any(
        line.lstrip().startswith(
            ("def ", "theorem ", "lemma ", "namespace ", "section ")
        )
        for line in header.splitlines()
    ):
        raise ValueError("generated declaration before the primitive namespace")
    lines = header.splitlines(keepends=True)
    last_import = max(i for i, line in enumerate(lines) if line.startswith("import "))
    lines.insert(last_import + 1, "\nset_option warningAsError true\n")
    if name == "Types.lean":
        if POSITIVE_SLICE in body:
            raise ValueError(
                "raw primitive types already contain a transformed representation"
            )
        for element, expected_count in POSITIVE_FIELDS.items():
            original = "Slice " + element
            if body.count(original) != expected_count:
                raise ValueError("unexpected recursive slice representation roster")
            body = body.replace(original, POSITIVE_SLICE + " " + element)
    if name == "Funs.lean":
        original = "let __anf0 ←"
        if body.count(original) != 2:
            raise ValueError("unexpected generated Boolean binding roster")
        body = body.replace(original, "let __anf0 : Bool ←")
        for original, converted in SLICE_COERCIONS.items():
            if body.count(original) != 1 or converted in body:
                raise ValueError("positive slice primitive coercion roster drift")
            body = body.replace(original, converted)
    normalized = ("".join(lines) + NAMESPACE + identifiers(body)).encode()
    if re.search(
        r"set_option\s+(?:linter\.\S+|warningAsError)\s+false\b",
        checkpoint.code(normalized),
    ):
        raise ValueError("primitive output disables a Lean warning or linter")
    return normalized, text.split(NAMESPACE, 1)[0]


def checked_entries(value: bytes) -> None:
    source = checkpoint.code(value)
    for entry in ENTRIES:
        if (
            len(
                re.findall(
                    r"^def " + re.escape(entry.replace("::", ".")) + r"\b",
                    source,
                    re.MULTILINE,
                )
            )
            != 1
        ):
            raise ValueError("primitive generated entry-point roster drift")


def assemble(generated: Path) -> tuple[dict[str, bytes], dict]:
    contents, headers, raw_hashes, templates = {}, {}, {}, {}
    for name in ("Types.lean", "Funs.lean"):
        raw = (generated / name).read_bytes()
        contents[name], headers[name] = normalize(raw, name)
        raw_hashes[name] = checkpoint.digest(raw)
    checked_entries(contents["Funs.lean"])
    for path in sorted(generated.glob("*_Template.lean")):
        raw = path.read_bytes()
        checkpoint.checked_template(raw)
        raw_hashes[path.name] = checkpoint.digest(raw)
        templates[path.name] = {
            "sha256": checkpoint.digest(raw),
            "source": raw.decode(),
        }
    if set(templates) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("unexpected primitive external-template roster")
    contents.update({name: value.encode() for name, value in MODELS.items()})
    contents["external-signatures.json"] = (
        json.dumps(templates, indent=2, sort_keys=True) + "\n"
    ).encode()
    return contents, {"raw_generated_sha256": raw_hashes, "raw_headers": headers}


def metadata() -> dict:
    return {
        "tools": checkpoint.TOOLS,
        "versions": checkpoint.VERSIONS,
        "rust_start_from": ["beaconcrypt_parse::" + name for name in ENTRIES],
        "charon_sysroot": "default",
        "rustflags": checkpoint.RUSTFLAGS,
        "lean_namespace": "beaconcrypt_parse",
        "generated_transformation": TRANSFORMATION,
        "external_obligations": [],
    }


def check_source(root: Path = ROOT, destination: Path = DESTINATION) -> None:
    configuration(root)
    provenance = json.loads((destination / "provenance.json").read_bytes())
    for key, value in metadata().items():
        if provenance.get(key) != value:
            raise ValueError(f"primitive provenance drift: {key}")
    current = source_snapshot(root)
    if (
        hash_roster(provenance.get("source_sha256"), set(current), "source_sha256")
        != current
    ):
        raise ValueError("primitive source drift")
    hash_roster(provenance.get("tool_sha256"), set(checkpoint.TOOLS), "tool_sha256")
    installed = hash_roster(
        provenance.get("installed_sha256"), set(INSTALLED), "installed_sha256"
    )
    raw = hash_roster(
        provenance.get("raw_generated_sha256"),
        {
            "Types.lean",
            "Funs.lean",
            "TypesExternal_Template.lean",
            "FunsExternal_Template.lean",
        },
        "raw_generated_sha256",
    )
    for name in INSTALLED:
        if checkpoint.digest((destination / name).read_bytes()) != installed[name]:
            raise ValueError(f"primitive installed-file drift: {name}")
    headers = provenance.get("raw_headers")
    if not isinstance(headers, dict) or set(headers) != {"Types.lean", "Funs.lean"}:
        raise ValueError("primitive raw-header roster drift")
    for name in headers:
        installed_body = (destination / name).read_bytes()
        _, body = installed_body.decode().split(NAMESPACE, 1)
        body = identifiers(body, reverse=True)
        if name == "Funs.lean":
            body = body.replace("let __anf0 : Bool ←", "let __anf0 ←")
            for original, converted in SLICE_COERCIONS.items():
                body = body.replace(converted, original)
        if name == "Types.lean":
            for element in POSITIVE_FIELDS:
                body = body.replace(POSITIVE_SLICE + " " + element, "Slice " + element)
        reconstructed = (headers[name] + NAMESPACE + body).encode()
        normalized, _ = normalize(reconstructed, name)
        if (
            normalized != installed_body
            or checkpoint.digest(reconstructed) != raw[name]
        ):
            raise ValueError("primitive body or header transformation drift")
    checked_entries((destination / "Funs.lean").read_bytes())
    for name, expected in MODELS.items():
        if (destination / name).read_text() != expected:
            raise ValueError("primitive external files must contain imports only")
    evidence = json.loads((destination / "external-signatures.json").read_bytes())
    if set(evidence) != {"TypesExternal_Template.lean", "FunsExternal_Template.lean"}:
        raise ValueError("primitive external-template evidence roster drift")
    for name, item in evidence.items():
        if not isinstance(item, dict) or set(item) != {"source", "sha256"}:
            raise ValueError("malformed primitive external-template evidence")
        value = item["source"].encode()
        checkpoint.checked_template(value)
        if checkpoint.digest(value) != item["sha256"] or item["sha256"] != raw[name]:
            raise ValueError("primitive external-template evidence drift")


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
            print("Generated registration primitive source/provenance match")
            return 0
        if args.work_dir is None or args.timeout <= 0:
            raise ValueError("extraction requires --work-dir and a positive timeout")
        configuration()
        directory = isolated_work(args.work_dir)
        directory.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="registration-primitives-", dir=directory))
        tools = {
            name: args.tools_root / name / version / name
            for name, version in checkpoint.TOOLS.items()
        }
        before = source_snapshot()
        old_subdirectory = checkpoint.SUBDIRECTORY
        try:
            checkpoint.SUBDIRECTORY = SUBDIRECTORY
            checkpoint.COHORTS[COHORT] = ENTRIES
            report = checkpoint.run(work, tools, COHORT, args.timeout, False)
        finally:
            checkpoint.SUBDIRECTORY = old_subdirectory
            checkpoint.COHORTS.pop(COHORT, None)
        if report["status"] != "extracted-without-external-obligations":
            raise ValueError(
                f"primitive extraction blocked: {report.get('error')}; {work / 'report.json'}"
            )
        contents, generated = assemble(work / "generated" / SUBDIRECTORY)
        if before != source_snapshot():
            raise ValueError("primitive source changed during extraction")
        provenance = {
            **metadata(),
            **generated,
            "source_sha256": before,
            "tool_sha256": report["tool_sha256"],
            "installed_sha256": {
                name: checkpoint.digest(value) for name, value in contents.items()
            },
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
                "Wrote actual generated CBOR primitive cohort; operations unchanged, identifiers encoded, recursive slice representation isomorphic"
            )
        else:
            changed = [
                name
                for name, value in contents.items()
                if not (DESTINATION / name).is_file()
                or (DESTINATION / name).read_bytes() != value
            ]
            if changed:
                raise ValueError("primitive extraction drift: " + ", ".join(changed))
            print("Generated CBOR primitive cohort matches fresh pinned extraction")
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
