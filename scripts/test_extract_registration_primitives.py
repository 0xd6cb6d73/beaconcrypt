#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Fail-closed source, type-representation and generator normalization controls."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_primitives as primitives


class RegistrationPrimitiveExtractionTests(unittest.TestCase):
    def fixture(self, directory: Path) -> tuple[Path, Path, dict]:
        root, destination = directory / "source", directory / "cohort"
        provenance = json.loads(
            (primitives.DESTINATION / "provenance.json").read_text()
        )
        for relative in provenance["source_sha256"]:
            target = root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(primitives.ROOT / relative, target)
        shutil.copytree(primitives.DESTINATION, destination)
        return root, destination, provenance

    def raw(self, name: str) -> bytes:
        provenance = json.loads(
            (primitives.DESTINATION / "provenance.json").read_text()
        )
        body = (
            (primitives.DESTINATION / name)
            .read_text()
            .split(primitives.NAMESPACE, 1)[1]
        )
        body = primitives.identifiers(body, reverse=True)
        if name == "Types.lean":
            for element in primitives.POSITIVE_FIELDS:
                body = body.replace(
                    primitives.POSITIVE_SLICE + " " + element, "Slice " + element
                )
        else:
            body = body.replace("let __anf0 : Bool ←", "let __anf0 ←")
            for original, converted in primitives.SLICE_COERCIONS.items():
                body = body.replace(converted, original)
        return (provenance["raw_headers"][name] + primitives.NAMESPACE + body).encode()

    def test_recorded_cohort_passes_source_check(self):
        primitives.check_source()

    def test_normalization_roundtrip_preserves_every_other_token(self):
        for name in ("Types.lean", "Funs.lean"):
            normalized, _ = primitives.normalize(self.raw(name), name)
            self.assertEqual(normalized, (primitives.DESTINATION / name).read_bytes())

    def test_missing_or_added_generator_linter_option_is_rejected(self):
        raw = self.raw("Funs.lean")
        for altered in (
            raw.replace(b"set_option linter.dupNamespace false\n", b""),
            raw.replace(
                b"namespace beaconcrypt_parse\n",
                b"set_option linter.extra false\nnamespace beaconcrypt_parse\n",
            ),
        ):
            with self.assertRaises(ValueError):
                primitives.normalize(altered, "Funs.lean")

    def test_body_cannot_disable_warning_or_linter(self):
        for option in ("warningAsError", "linter.style.nameCheck", "linter.deprecated"):
            with self.subTest(option=option), self.assertRaises(ValueError):
                primitives.normalize(
                    self.raw("Funs.lean") + f"\nset_option {option} false\n".encode(),
                    "Funs.lean",
                )

    def test_unreviewed_recursive_slice_roster_is_rejected(self):
        raw = self.raw("Types.lean")
        with self.assertRaises(ValueError):
            primitives.normalize(
                raw.replace(
                    b"Slice cbordetveraux.cbor_raw", b"List cbordetveraux.cbor_raw", 1
                ),
                "Types.lean",
            )

    def test_restored_bool_annotation_requires_exact_source_roster(self):
        raw = self.raw("Funs.lean")
        with self.assertRaises(ValueError):
            primitives.normalize(
                raw.replace("let __anf0 ←".encode(), "let different ←".encode(), 1),
                "Funs.lean",
            )

    def test_identifier_encoding_is_bijective_and_comment_string_safe(self):
        source = 'def name__part (value·1 : Nat) := value·1\n-- name__part value·1\n#check "name__part value·1"\n'
        encoded = primitives.identifiers(source)
        self.assertEqual(primitives.identifiers(encoded, reverse=True), source)
        self.assertIn("-- name__part value·1", encoded)
        self.assertIn('"name__part value·1"', encoded)

    def test_identifier_collision_or_malformed_reverse_is_rejected(self):
        with self.assertRaises(ValueError):
            primitives.identifiers("def bcExtractedToken6162 := 1")
        with self.assertRaises(ValueError):
            primitives.identifiers("def bcExtractedTokenxyz := 1", reverse=True)

    def test_identifier_encoding_cannot_rewrite_anonymous_function_syntax(self):
        self.assertEqual(primitives.identifiers("fun x => (· + x)"), "fun x => (· + x)")
        with self.assertRaises(ValueError):
            primitives.identifiers("fun x·↔y => x")

    def test_comment_cannot_replace_entry_point(self):
        contents = (primitives.DESTINATION / "Funs.lean").read_bytes()
        first = primitives.ENTRIES[0].replace("::", ".").encode()
        with self.assertRaises(ValueError):
            primitives.checked_entries(
                contents.replace(b"def " + first, b"-- def " + first)
            )

    def test_actual_source_or_generated_body_mutation_is_rejected(self):
        for relative in ("beaconcrypt-parse/src/generated/cbordetveraux.rs", None):
            with tempfile.TemporaryDirectory() as directory:
                root, destination, _ = self.fixture(Path(directory))
                path = root / relative if relative else destination / "Funs.lean"
                path.write_text(path.read_text() + "\n-- mutation\n")
                with self.assertRaises(ValueError):
                    primitives.check_source(root, destination)

    def test_external_model_cannot_add_an_operation_even_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            root, destination, provenance = self.fixture(Path(directory))
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\ndef parser_correct : Prop := True\n")
            provenance["installed_sha256"][path.name] = primitives.checkpoint.digest(
                path.read_bytes()
            )
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaises(ValueError):
                primitives.check_source(root, destination)


if __name__ == "__main__":
    unittest.main()
