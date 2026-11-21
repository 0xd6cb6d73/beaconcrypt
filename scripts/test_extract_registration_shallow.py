#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for exact constructor restriction and source composition."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_shallow as extraction
import prepare_registration_shallow_source as preparation


class RegistrationShallowTests(unittest.TestCase):
    def installed(self, directory):
        destination = Path(directory) / "installed"
        shutil.copytree(extraction.DESTINATION, destination)
        return destination

    def prepared(self, directory):
        destination = Path(directory) / "fixture"
        outputs, manifest = preparation.expected()
        for name, text in outputs.items():
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        for name in (
            preparation.AUX,
            preparation.DET,
            "beaconcrypt-parse/src/generated/transport.rs",
        ):
            path = destination / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(preparation.ROOT / name, path)
        (destination / preparation.MANIFEST).write_text(json.dumps(manifest))
        return destination

    def test_current_source_reconstruction_matches(self):
        extraction.check_source()

    def test_original_auxiliary_module_is_exact_prefix(self):
        outputs, manifest = preparation.expected()
        original = (preparation.ROOT / preparation.AUX).read_text()
        self.assertTrue(outputs[preparation.SUPPLEMENT].startswith(original))
        self.assertEqual(len(manifest["dispatchers"]), 2)
        for dispatcher in manifest["dispatchers"]:
            self.assertIn(dispatcher["deep_branch"], original)
            self.assertIn(dispatcher["shallow_branch"], original)
            for helper in dispatcher["helpers"]:
                self.assertIn(dispatcher["shallow_branch"], helper["source"])
        self.assertFalse(manifest["public_codec_law_proved"])

    def test_byte_factory_keeps_rejection_and_closed_tests(self):
        _, manifest = preparation.expected()
        factory = manifest["factory"]
        self.assertEqual(
            [item["value"] for item in factory["comparisons"]], [False, True]
        )
        self.assertIn("q4 < 16usize", factory["specialized_body"])
        self.assertEqual(
            factory["original_body"].count("::None"),
            factory["specialized_body"].count("::None"),
        )
        self.assertIn("cbor_impl_utf8_correct(s)", factory["original_body"])
        self.assertNotIn("cbor_impl_utf8_correct(s)", factory["specialized_body"])

    def test_closed_comparison_requires_exact_else_and_single_occurrence(self):
        with self.assertRaises(ValueError):
            preparation.closed_comparison("if test { yes }", "test", True)
        with self.assertRaises(ValueError):
            preparation.closed_comparison(
                "if test { yes } else { no }; if test { y } else { n }", "test", True
            )
        actual, _ = preparation.closed_comparison(
            "if test { side_effect() } else { rejected() }", "test", False
        )
        self.assertEqual(actual, "{ rejected() }")

    def test_fixture_generated_file_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.AUX
            path.write_text(path.read_text() + "\n// changed\n")
            with self.assertRaisesRegex(ValueError, "modified original"):
                preparation.check_fixture(fixture)

    def test_fixture_deep_branch_removal_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.SUPPLEMENT
            path.write_text(path.read_text().replace("if deep", "if false", 1))
            with self.assertRaisesRegex(ValueError, "composition drift"):
                preparation.check_fixture(fixture)

    def test_fixture_factory_rejection_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.LIB
            path.write_text(path.read_text().replace("q4 < 16usize", "true", 1))
            with self.assertRaisesRegex(ValueError, "composition drift"):
                preparation.check_fixture(fixture)

    def test_closed_constructor_certificate_cannot_be_changed(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            value["source_preparation"]["factory"]["comparisons"][0]["value"] = True
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "certificate drift"):
                extraction.check_source(destination=destination)

    def test_component_cannot_claim_public_codec_or_source_closure(self):
        for field in ("public_codec_law_proved", "source_correspondence_proved"):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                path = destination / "provenance.json"
                value = json.loads(path.read_text())
                value[field] = True
                path.write_text(json.dumps(value))
                with self.assertRaisesRegex(ValueError, "cannot assert"):
                    extraction.check_source(destination=destination)

    def test_import_only_external_cannot_gain_an_axiom_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            external = destination / "FunsExternal.lean"
            external.write_text(
                external.read_text() + "\naxiom parser_correct : True\n"
            )
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            value["installed_sha256"][external.name] = extraction.checkpoint.digest(
                external.read_bytes()
            )
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "imports only"):
                extraction.check_source(destination=destination)

    def test_shared_declaration_mutation_rejected_after_installed_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            omitted = value["normalization"]["Funs.lean"]["omitted_shared_groups"][0]
            omitted["source"] += "\ndef fabricated := True\n"
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "shared source drift"):
                extraction.check_source(destination=destination)

    def test_fixture_must_be_new_and_external(self):
        with self.assertRaisesRegex(ValueError, "outside the worktree"):
            preparation.prepare(preparation.ROOT / "var/forbidden-constructor-fixture")
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "new destination"):
                preparation.prepare(Path(directory))


if __name__ == "__main__":
    unittest.main()
