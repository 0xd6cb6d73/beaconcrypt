#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed source/provenance controls for unchanged header optimality."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_header_optimal as extraction


class RegistrationHeaderOptimalTests(unittest.TestCase):
    def installed(self, directory):
        path = Path(directory) / "installed"
        shutil.copytree(extraction.DESTINATION, path)
        return path

    def rewrite_provenance(self, destination, update):
        path = destination / "provenance.json"
        value = json.loads(path.read_text())
        update(value)
        path.write_text(json.dumps(value))

    def test_current_pinned_source_and_output_match(self):
        extraction.check_source()
        self.assertEqual(extraction.ENTRIES, ("cbordetveraux::cbor_raw_ints_optimal",))
        source = (extraction.DESTINATION / "Funs.lean").read_text()
        self.assertIn("def cbordetveraux.impl_raw_uint64_optimal", source)
        self.assertIn("def cbordetveraux.cbor_raw_ints_optimal", source)
        self.assertIn("256#u64 <= x.value", source)
        self.assertIn("65536#u64 <= x.value", source)
        self.assertIn("4294967296#u64 <= x.value", source)
        self.assertIn("false", source)

    def test_source_hash_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            self.rewrite_provenance(
                destination,
                lambda value: value["source_sha256"].update({"extra": "0" * 64}),
            )
            with self.assertRaisesRegex(ValueError, "source provenance"):
                extraction.check_source(destination=destination)

    def test_entry_and_default_pins_cannot_change(self):
        for field, replacement in (
            ("rust_start_from", ["opaque_parser"]),
            ("tools", {"aeneas": "candidate"}),
        ):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                self.rewrite_provenance(
                    destination, lambda value: value.update({field: replacement})
                )
                with self.assertRaisesRegex(ValueError, "entry/tool"):
                    extraction.check_source(destination=destination)

    def test_component_cannot_claim_full_public_codec(self):
        for field, replacement in (
            ("public_codec_law_proved", True),
            ("source_correspondence_proved", True),
            ("original_generated_source_unchanged", False),
        ):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                self.rewrite_provenance(
                    destination, lambda value: value.update({field: replacement})
                )
                with self.assertRaisesRegex(ValueError, "cannot assert"):
                    extraction.check_source(destination=destination)

    def test_installed_body_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "Funs.lean"
            path.write_text(path.read_text().replace("256#u64", "255#u64", 1))
            with self.assertRaisesRegex(ValueError, "installed body"):
                extraction.check_source(destination=destination)

    def test_rehashed_body_still_requires_exact_raw_reconstruction(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "Funs.lean"
            path.write_text(path.read_text().replace("256#u64", "255#u64", 1))
            self.rewrite_provenance(
                destination,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaisesRegex(
                ValueError, "raw generated source reconstruction"
            ):
                extraction.check_source(destination=destination)

    def test_shared_body_must_match_original_primitive(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)

            def mutate(value):
                item = value["normalization"]["Funs.lean"]["omitted_shared_groups"][0]
                item["source"] += "\naxiom changed_shared_body : True\n"

            self.rewrite_provenance(destination, mutate)
            with self.assertRaisesRegex(ValueError, "shared source"):
                extraction.check_source(destination=destination)

    def test_import_only_external_cannot_gain_law_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\naxiom parser_correct : True\n")
            self.rewrite_provenance(
                destination,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaisesRegex(ValueError, "imports only"):
                extraction.check_source(destination=destination)


if __name__ == "__main__":
    unittest.main()
