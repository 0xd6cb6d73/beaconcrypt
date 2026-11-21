#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed source transformation and production immutability controls."""

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import prepare_registration_codec_source as preparation
import registration_codec_normalization as normalization


class RegistrationSourcePreparationTests(unittest.TestCase):
    def test_exact_original_codec_fingerprints_match(self):
        self.assertEqual(
            set(preparation.original_sources()), set(preparation.ORIGINALS)
        )

    def test_changed_original_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in preparation.ORIGINALS:
                destination = root / name
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(preparation.ROOT / name, destination)
            path = root / next(iter(preparation.ORIGINALS))
            path.write_text(path.read_text() + "\n// drift\n")
            with self.assertRaisesRegex(ValueError, "unreviewed original"):
                preparation.original_sources(root)

    def test_preparation_cannot_write_into_production_worktree(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            preparation.prepare(preparation.ROOT / "var/forbidden-codec-fixture")

    def test_prepare_never_overwrites_existing_destination(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            marker = path / "marker"
            marker.write_text("keep")
            with self.assertRaisesRegex(ValueError, "new destination"):
                preparation.prepare(path)
            self.assertEqual(marker.read_text(), "keep")

    def test_external_fixture_is_reproducible_and_production_unchanged(self):
        before = preparation.source_snapshot()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture"
            preparation.prepare(path)
            preparation.check_fixture(path)
            manifest = json.loads((path / preparation.MANIFEST).read_text())
            self.assertFalse(manifest["production_generated_source_modified"])
            self.assertFalse(manifest["public_codec_law_proved"])
            self.assertFalse(manifest["source_correspondence_proved"])
        self.assertEqual(preparation.source_snapshot(), before)

    def test_prepared_body_cannot_change_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture"
            preparation.prepare(path)
            name = "beaconcrypt-parse/src/generated/transport.rs"
            prepared = path / name
            prepared.write_text(prepared.read_text() + "\n// altered\n")
            manifest_path = path / preparation.MANIFEST
            manifest = json.loads(manifest_path.read_text())
            manifest["prepared_codec_sha256"][name] = preparation.checkpoint.digest(
                prepared.read_bytes()
            )
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "provenance drift"):
                preparation.check_fixture(path)

    def test_typed_leaf_or_control_certificate_cannot_be_replaced(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture"
            preparation.prepare(path)
            manifest_path = path / preparation.MANIFEST
            manifest = json.loads(manifest_path.read_text())
            manifest["control_fragments"][0]["control"] = {
                "kind": "done",
                "value": True,
            }
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "provenance drift"):
                preparation.check_fixture(path)

    def test_every_bool_distribution_has_a_finite_source_control_fragment(self):
        _, steps, fragments = preparation.transform(
            preparation.original_sources(), "schema"
        )
        distributions = [item for step in steps for item in step.get("certificate", [])]
        self.assertEqual(len(fragments), 14)
        self.assertEqual(len(distributions), len(fragments))
        self.assertEqual(len({item["name"] for item in fragments}), len(fragments))
        for item in distributions:
            self.assertEqual(item["typed_leaf"]["type"], "bool")
            self.assertIn("source", item["typed_leaf"])

    def test_ignored_boolean_checks_forward_original_updated_cell(self):
        files, steps, _ = preparation.transform(
            preparation.original_sources(), "schema"
        )
        checks = [
            step for step in steps if step.get("rule") == "typed-parse-check-outlining"
        ]
        self.assertEqual([len(step["checks"]) for step in checks], [5, 7])
        transport = files["beaconcrypt-parse/src/generated/transport.rs"]
        for step in checks:
            for index, check in enumerate(step["checks"]):
                self.assertIn(check["original_expression"], transport)
                self.assertIn(
                    check["state_cell"] + " = extraction_after_" + str(index), transport
                )

    def test_singleton_scalarization_rejects_an_escaping_cell(self):
        source = preparation.original_sources()[
            "beaconcrypt-parse/src/generated/cbordetveraux.rs"
        ]
        altered = source.replace("let mut pkey:", "let mut pkey:", 1).replace(
            "let pairs: u64 = nbpairs",
            "crate::lowstar::ignore::ignore(&pkey); let pairs: u64 = nbpairs",
            1,
        )
        with self.assertRaisesRegex(ValueError, "escapes"):
            normalization.scalarize_shared_cells(altered)

    def test_nested_comments_and_literals_do_not_create_source_control(self):
        source = '/* if false { /* nested */ } */ "if true { }"\nif flag { true } else { false }'
        masked = normalization.mask(source)
        self.assertEqual(masked.count("if"), 1)
        with self.assertRaises(ValueError):
            normalization.mask("/* never closed")

    def test_match_condition_keeps_its_complete_arm_set(self):
        source = (
            "if match raw { Raw::A { .. } => true, _ => false } { true } else { false }"
        )
        condition, yes, no = normalization.conditional(source)
        self.assertEqual(condition, "match raw { Raw::A { .. } => true, _ => false }")
        self.assertEqual((yes.tail, no.tail), ("true", "false"))

    def test_unknown_phase_or_reserved_helper_source_is_rejected(self):
        original = preparation.original_sources()
        with self.assertRaisesRegex(ValueError, "phase"):
            preparation.transform(original, "current-pin-accepted")
        original = copy.deepcopy(original)
        original[
            "beaconcrypt-parse/src/lib.rs"
        ] += "\npub fn extraction_override() {}\n"
        with self.assertRaisesRegex(ValueError, "namespace"):
            preparation.transform(original, "schema")


if __name__ == "__main__":
    unittest.main()
