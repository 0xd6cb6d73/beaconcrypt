#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the source array-writer extraction component."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_array as extraction
import prepare_registration_array_source as preparation


class RegistrationArrayTests(unittest.TestCase):
    def installed(self, directory):
        path = Path(directory) / "installed"
        shutil.copytree(extraction.DESTINATION, path)
        return path

    def prepared(self, directory):
        path = Path(directory) / "fixture"
        outputs, manifest = preparation.expected()
        for name, source in outputs.items():
            target = path / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source)
        for name in (
            preparation.shallow.AUX,
            preparation.shallow.DET,
            "beaconcrypt-parse/src/generated/transport.rs",
        ):
            target = path / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(preparation.ROOT / name, target)
        (path / preparation.MANIFEST).write_text(json.dumps(manifest))
        return path

    def test_current_pinned_source_and_output_match(self):
        extraction.check_source()

    def test_complete_original_source_and_loop_state_retained(self):
        outputs, manifest = preparation.expected()
        original = (preparation.ROOT / preparation.shallow.AUX).read_text()
        self.assertTrue(outputs[preparation.shallow.SUPPLEMENT].startswith(original))
        self.assertIn(manifest["original_array_writer"]["body"], original)
        self.assertEqual(len(manifest["scalar_helper_boundaries"]), 5)
        self.assertEqual(len(manifest["inner_loop_boundaries"]), 5)
        self.assertIn("while", manifest["appended_helpers"])
        self.assertIn("&mut [u8]", manifest["appended_helpers"])
        self.assertFalse(manifest["rotation_law_proved"])

    def test_entry_is_derived_from_original_public_wrapper(self):
        _, manifest = preparation.expected()
        entry = manifest["entry"]
        self.assertEqual(
            entry["prepared_body"],
            entry["original_body"]
            .replace(
                "crate::cbordetveraux::cbor_serialize_array",
                "extraction_serialize_array",
                1,
            )
            .replace("crate::cbordetveraux::mk_raw_uint64", "mk_raw_uint64", 1),
        )

    def test_original_generated_file_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.shallow.AUX
            path.write_text(path.read_text() + "\n// mutation\n")
            with self.assertRaisesRegex(ValueError, "modified original"):
                preparation.check_fixture(fixture)

    def test_helper_body_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.shallow.SUPPLEMENT
            path.write_text(path.read_text().replace("while", "if", 1))
            with self.assertRaisesRegex(ValueError, "composition drift"):
                preparation.check_fixture(fixture)

    def test_fixture_cannot_impersonate_shallow_cohort(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            (fixture / preparation.shallow.MANIFEST).write_text("{}")
            with self.assertRaisesRegex(ValueError, "impersonate"):
                preparation.check_fixture(fixture)

    def test_loop_certificate_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            value["source_preparation"]["inner_loop_boundaries"][0][
                "original_body"
            ] += " break;"
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "certificate drift"):
                extraction.check_source(destination=destination)

    def test_cannot_claim_rotation_codec_or_source_law(self):
        for field in (
            "rotation_law_proved",
            "public_codec_law_proved",
            "source_correspondence_proved",
        ):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                path = destination / "provenance.json"
                value = json.loads(path.read_text())
                value[field] = True
                path.write_text(json.dumps(value))
                with self.assertRaisesRegex(ValueError, "cannot assert"):
                    extraction.check_source(destination=destination)

    def test_import_only_external_cannot_gain_law_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\naxiom rotation_correct : True\n")
            provenance = destination / "provenance.json"
            value = json.loads(provenance.read_text())
            value["installed_sha256"][path.name] = extraction.checkpoint.digest(
                path.read_bytes()
            )
            provenance.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "imports only"):
                extraction.check_source(destination=destination)

    def test_entry_and_default_pins_cannot_be_changed(self):
        for field, replacement in (
            ("rust_start_from", ["opaque_parser"]),
            ("tools", {"aeneas": "candidate"}),
        ):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                path = destination / "provenance.json"
                value = json.loads(path.read_text())
                value[field] = replacement
                path.write_text(json.dumps(value))
                with self.assertRaisesRegex(ValueError, "entry/tool"):
                    extraction.check_source(destination=destination)


if __name__ == "__main__":
    unittest.main()
