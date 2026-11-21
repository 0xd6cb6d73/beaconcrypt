#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the source-selected finite frame dispatcher."""

import json
from pathlib import Path
import tempfile
import unittest

import extract_frame_dispatch as extraction
import prepare_frame_dispatch_source as preparation


class FrameDispatchTests(unittest.TestCase):
    def setUp(self):
        self.original = (extraction.ROOT / preparation.SOURCE).read_text()

    def test_source(self):
        extraction.check_source()

    def test_normalization_roundtrip(self):
        for name in ("Types.lean", "Funs.lean"):
            installed = (extraction.DESTINATION / name).read_bytes()
            self.assertEqual(
                extraction.normalize(extraction.denormalize(installed, name), name),
                installed,
            )

    def test_changed_selected_encoder(self):
        raw = extraction.denormalize(
            (extraction.DESTINATION / "Funs.lean").read_bytes(), "Funs.lean"
        )
        changed = raw.replace(b"frame.encode_three", b"frame.unreviewed", 1)
        self.assertNotEqual(raw, changed)
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_appended_axiom(self):
        installed = (extraction.DESTINATION / "Funs.lean").read_bytes()
        with self.assertRaises(ValueError):
            extraction.denormalize(installed + b"\naxiom bypass : False\n", "Funs.lean")

    def test_warning_suppression(self):
        installed = (extraction.DESTINATION / "Funs.lean").read_bytes()
        with self.assertRaises(ValueError):
            extraction.denormalize(
                installed + b"\nset_option linter.deprecated false\n", "Funs.lean"
            )

    def test_preparation_preserves_fallback(self):
        prepared, certificate = preparation.transform(self.original)
        self.assertIn(certificate["outlined_tail"], prepared)
        self.assertFalse(certificate["fallback_claimed_reachable"])
        self.assertEqual(certificate["length_prefix"], preparation.PREFIX)

    def test_changed_original_rejected(self):
        for before, after in (
            ("parts.len()", "parts.capacity()"),
            ("payload_length", "unreviewed_length"),
            ("encode_three(sequence, sender", "encode_three(sender, sequence"),
        ):
            start = self.original.index("pub(crate) fn encode_parts(")
            changed = self.original[:start] + self.original[start:].replace(
                before, after, 1
            )
            self.assertNotEqual(changed, self.original)
            with self.assertRaises(ValueError):
                preparation.transform(changed)

    def test_destination_rejected(self):
        for destination in (
            extraction.ROOT,
            extraction.ROOT.parent,
            extraction.ROOT / "fixture",
        ):
            with self.assertRaises(ValueError):
                preparation.prepare(extraction.ROOT, destination)

    def test_fixture_preserves_generated_files(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "fixture"
            certificate = preparation.prepare(extraction.ROOT, fixture)
            for name, expected in certificate["unchanged_sha256"].items():
                self.assertEqual(
                    preparation.digest((fixture / name).read_bytes()), expected
                )
            self.assertIn(
                "beaconcrypt-parse/src/generated/transport.rs",
                certificate["unchanged_sha256"],
            )

    def fixture_rejected(self, change):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = preparation.source_files(extraction.ROOT)
            files.update(
                {
                    name: (extraction.ROOT / name).read_bytes()
                    for name in extraction.SOURCE_FILES
                }
            )
            for name, contents in files.items():
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(contents)
            cohort = root / "cohort"
            cohort.mkdir()
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (cohort / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            extraction.check_source(root, cohort)
            change(root, cohort)
            with self.assertRaises(ValueError):
                extraction.check_source(root, cohort)

    def test_rehashed_missing_immutable_source(self):
        def change(_, cohort):
            target = cohort / "external-signatures.json"
            value = json.loads(target.read_text())
            value["source_preparation"]["unchanged_sha256"].popitem()
            target.write_text(json.dumps(value))
            provenance = cohort / "provenance.json"
            record = json.loads(provenance.read_text())
            record["installed_sha256"][target.name] = extraction.digest(
                target.read_bytes()
            )
            provenance.write_text(json.dumps(record))

        self.fixture_rejected(change)

    def test_generated_source_drift(self):
        self.fixture_rejected(
            lambda root, _: (
                root / "beaconcrypt-parse/src/generated/transport.rs"
            ).write_text("// changed\n")
        )

    def test_model_drift(self):
        self.fixture_rejected(
            lambda _, cohort: (cohort / "FunsExternal.lean").write_text("// changed\n")
        )


if __name__ == "__main__":
    unittest.main()
