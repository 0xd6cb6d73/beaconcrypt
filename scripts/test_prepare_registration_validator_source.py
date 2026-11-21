#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for immutable parser source and normalization."""

import json
from pathlib import Path
import tempfile
import unittest
import prepare_registration_validator_source as preparation


class ValidatorPreparationTests(unittest.TestCase):
    def fixture(self, directory):
        target = Path(directory) / "source"
        preparation.prepare(target)
        return target

    def test_original_generated_files_unchanged(self):
        files, certificate = preparation.expected()
        for original in preparation.SUPPLEMENTS:
            self.assertEqual(
                files[original], (preparation.ROOT / original).read_bytes()
            )
            self.assertIn(original, certificate["unchanged_sha256"])
        self.assertTrue(certificate["generated_files_unchanged"])
        self.assertFalse(certificate["public_decoder_law_proved"])
        self.assertFalse(certificate["native_wire_instantiated"])

    def test_exact_fixture(self):
        with tempfile.TemporaryDirectory() as directory:
            preparation.check_fixture(self.fixture(directory))

    def test_changed_sources(self):
        names = [
            next(iter(preparation.SUPPLEMENTS)),
            next(iter(preparation.SUPPLEMENTS.values())),
            preparation.LIB,
        ]
        for name in names:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory:
                target = self.fixture(directory)
                path = target / name
                path.write_bytes(path.read_bytes() + b"\n// changed\n")
                with self.assertRaises(ValueError):
                    preparation.check_fixture(target)

    def test_extra_file(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.fixture(directory)
            (target / "unchecked.rs").write_text("")
            with self.assertRaises(ValueError):
                preparation.check_fixture(target)

    def test_missing_evidence_or_false_claim(self):
        for key in (
            "unchanged_sha256",
            "public_decoder_law_proved",
            "native_wire_instantiated",
        ):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                target = self.fixture(directory)
                path = target / preparation.MANIFEST
                value = json.loads(path.read_text())
                if key == "unchanged_sha256":
                    value[key].popitem()
                else:
                    value[key] = True
                path.write_text(json.dumps(value))
                with self.assertRaises(ValueError):
                    preparation.check_fixture(target)

    def test_destination_boundaries(self):
        for target in (
            preparation.ROOT,
            preparation.ROOT.parent,
            preparation.ROOT / "fixture",
        ):
            with self.assertRaises(ValueError):
                preparation.prepare(target)
        with tempfile.TemporaryDirectory() as directory:
            target = Path(directory) / "existing"
            target.mkdir()
            (target / "keep").write_text("evidence")
            with self.assertRaises(ValueError):
                preparation.prepare(target)
            self.assertEqual((target / "keep").read_text(), "evidence")


if __name__ == "__main__":
    unittest.main()
