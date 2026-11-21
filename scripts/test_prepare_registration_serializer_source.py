#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for exact source field boundaries and public frontends."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import prepare_registration_serializer_source as preparation


class RegistrationSerializerPreparationTests(unittest.TestCase):
    def prepared(self, directory):
        path = Path(directory) / "fixture"
        outputs, manifest = preparation.expected()
        for name, contents in outputs.items():
            target = path / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(contents)
        for source in (preparation.ROOT / "beaconcrypt-parse/src/generated").glob(
            "*.rs"
        ):
            target = path / source.relative_to(preparation.ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        (path / preparation.MANIFEST).write_text(json.dumps(manifest))
        return path

    def test_original_generated_source_complete_prefix_retained(self):
        outputs, manifest = preparation.expected()
        original = (preparation.ROOT / preparation.TRANSPORT).read_text()
        self.assertTrue(outputs[preparation.SUPPLEMENT].startswith(original))
        self.assertEqual(len(manifest["field_boundaries"]), 8)
        self.assertTrue(manifest["generated_rust_files_unchanged"])
        self.assertTrue(manifest["original_generated_bodies_unchanged"])
        self.assertFalse(manifest["source_correspondence_proved"])
        self.assertFalse(manifest["public_codec_law_proved"])

    def test_every_helper_retains_original_expression_and_types(self):
        outputs, manifest = preparation.expected()
        for row in manifest["field_boundaries"]:
            self.assertIn(row["original_expression"], outputs[preparation.SUPPLEMENT])
            self.assertEqual(
                row["parameter_types"], ["&'a[u8]", "&'b mut[u8]", "bool", "bool"]
            )
            self.assertEqual(row["return_type"], "usize")
            self.assertIn("lo_ok && hi_ok", row["original_expression"])
            self.assertIn("cbor_det_serialize", row["original_expression"])

    def test_public_frontend_changes_only_name_and_selected_call(self):
        _, manifest = preparation.expected()
        for row in manifest["public_frontends"]:
            self.assertEqual(
                row["prepared_signature"],
                row["original_signature"].replace(
                    row["function"], "extraction_" + row["function"]
                ),
            )
            source = (
                "serialize_initkex"
                if row["function"] == "encode_init"
                else "serialize_kexresponse"
            )
            self.assertEqual(
                row["prepared_body"],
                row["original_body"].replace(
                    "transport::" + source, "transport::extraction_" + source, 1
                ),
            )
            self.assertIn(".is_none()", row["prepared_body"])
            self.assertIn("return 0;", row["prepared_body"])

    def test_current_prepared_fixture_matches(self):
        with tempfile.TemporaryDirectory() as directory:
            preparation.check_fixture(self.prepared(directory))

    def test_original_generated_file_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.TRANSPORT
            path.write_text(path.read_text() + "\n// changed original\n")
            with self.assertRaisesRegex(ValueError, "modified original"):
                preparation.check_fixture(fixture)

    def test_prepared_helper_body_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.SUPPLEMENT
            path.write_text(path.read_text() + "\nfn unreviewed() {}\n")
            with self.assertRaisesRegex(ValueError, "composition drift"):
                preparation.check_fixture(fixture)

    def test_public_admission_change_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.LIB
            path.write_text(path.read_text().replace(".is_none()", ".is_some()", 1))
            with self.assertRaisesRegex(ValueError, "composition drift"):
                preparation.check_fixture(fixture)

    def test_correspondence_row_change_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            path = fixture / preparation.MANIFEST
            value = json.loads(path.read_text())
            value["field_boundaries"][0]["original_expression"] += " return 0;"
            path.write_text(json.dumps(value))
            with self.assertRaisesRegex(ValueError, "certificate drift"):
                preparation.check_fixture(fixture)

    def test_component_cannot_claim_full_codec(self):
        for key in ("source_correspondence_proved", "public_codec_law_proved"):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                fixture = self.prepared(directory)
                path = fixture / preparation.MANIFEST
                value = json.loads(path.read_text())
                value[key] = True
                path.write_text(json.dumps(value))
                with self.assertRaisesRegex(ValueError, "certificate drift"):
                    preparation.check_fixture(fixture)

    def test_fixture_cannot_impersonate_other_cohort(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = self.prepared(directory)
            (fixture / "registration-source-correspondence.json").write_text("{}")
            with self.assertRaisesRegex(ValueError, "impersonate"):
                preparation.check_fixture(fixture)

    def test_existing_destination_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "existing"
            fixture.mkdir()
            (fixture / "keep").write_text("evidence")
            with self.assertRaisesRegex(ValueError, "new destination"):
                preparation.prepare(fixture)
            self.assertEqual((fixture / "keep").read_text(), "evidence")

    def test_source_worktree_destination_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside source worktree"):
            preparation.prepare(
                preparation.ROOT / "var" / "serializer-preparation-forbidden"
            )


if __name__ == "__main__":
    unittest.main()
