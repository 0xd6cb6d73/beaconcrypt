#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Source/cohort sharing and finite certificate integrity regression controls."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_schema as schema


class RegistrationSchemaExtractionTests(unittest.TestCase):
    def fixture(self, root):
        destination = root / "cohort"
        certificate = root / "certificate.lean"
        shutil.copytree(schema.DESTINATION, destination)
        shutil.copyfile(schema.CERTIFICATE_DESTINATION, certificate)
        return destination, certificate

    def test_current_source_and_finite_certificates_match(self):
        schema.check_source()

    def test_comment_insensitive_sharing_keeps_exact_string_literals(self):
        self.assertEqual(schema.tokens("def x := 1 -- note"), schema.tokens("def x:=1"))
        self.assertNotEqual(
            schema.tokens('panic "bad input"'), schema.tokens('panic "badinput"')
        )
        self.assertNotEqual(
            schema.tokens('panic "bad input"'), schema.tokens('panic "bad  input"')
        )
        with self.assertRaises(ValueError):
            schema.tokens("/* wrong syntax /- open")

    def test_multiline_function_names_are_separate_declaration_groups(self):
        body = "\n/-- first -/\ndef first := 1\n\n/-- second -/\ndef\n  second := 2\n\nend beaconcrypt_parse\n"
        groups = schema.chunks(body)
        self.assertEqual([names for names, _ in groups], [("first",), ("second",)])
        self.assertEqual(
            "".join(group for _, group in groups) + "end beaconcrypt_parse\n", body
        )

    def test_installed_body_mutation_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            path = destination / "Funs.lean"
            path.write_text(path.read_text() + "\n-- drift\n")
            with self.assertRaises(ValueError):
                schema.check_source(
                    destination=destination, certificate_path=certificate
                )

    def test_finite_source_certificate_cannot_be_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            certificate.write_text(
                certificate.read_text().replace(".done false", ".done true", 1)
            )
            with self.assertRaisesRegex(ValueError, "certificate drift"):
                schema.check_source(
                    destination=destination, certificate_path=certificate
                )

    def test_external_file_cannot_gain_a_parser_law_even_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\naxiom parser_correct : True\n")
            provenance = json.loads((destination / "provenance.json").read_text())
            provenance["installed_sha256"][path.name] = schema.checkpoint.digest(
                path.read_bytes()
            )
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaisesRegex(ValueError, "imports only"):
                schema.check_source(
                    destination=destination, certificate_path=certificate
                )

    def test_schema_component_cannot_claim_public_codec_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            provenance = json.loads((destination / "provenance.json").read_text())
            provenance["public_codec_law_proved"] = True
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaisesRegex(ValueError, "public codec law"):
                schema.check_source(
                    destination=destination, certificate_path=certificate
                )

    def test_shared_primitive_declarations_are_checked_token_for_token(self):
        provenance = json.loads((schema.DESTINATION / "provenance.json").read_text())
        evidence = provenance["normalization"]["Funs.lean"]
        changed = False
        for omitted in evidence["omitted_shared_groups"]:
            if "cbordetveraux.argument_as_uint64" in omitted["names"]:
                omitted["source"] = omitted["source"].replace("ok v", "ok 0#u64", 1)
                changed = True
        self.assertTrue(changed)
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaises(ValueError):
                schema.check_source(
                    destination=destination, certificate_path=certificate
                )


if __name__ == "__main__":
    unittest.main()
