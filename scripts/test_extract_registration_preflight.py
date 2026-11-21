#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Production immutability, standard-source fidelity and preflight provenance."""

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_preflight as extraction
import prepare_registration_preflight_source as preparation


class RegistrationPreflightTests(unittest.TestCase):
    def fixture(self, path):
        destination = path / "cohort"
        certificate = path / "certificate.lean"
        shutil.copytree(extraction.DESTINATION, destination)
        shutil.copyfile(extraction.CERTIFICATE_DESTINATION, certificate)
        return destination, certificate

    def test_recorded_source_and_certificates_match(self):
        extraction.check_source()

    def test_recorded_standard_evidence_is_portable(self):
        _, _, metadata = preparation.expected()
        self.assertEqual(
            preparation.expected(std_evidence=metadata["standard_library"])[2], metadata
        )

    def test_standard_body_or_signature_change_is_rejected_after_rehash(self):
        standard = preparation.standard_sources()
        for field in ("signature", "body"):
            altered = copy.deepcopy(standard)
            item = altered["functions"]["strip_prefix"]
            item[field] += "\n// altered\n"
            item["body_sha256"] = preparation.checkpoint.digest(item["body"].encode())
            with self.assertRaises(ValueError):
                preparation.checked_standard_evidence(altered)

    def test_standard_function_roster_cannot_be_replaced(self):
        standard = preparation.standard_sources()
        del standard["functions"]["split_first"]
        with self.assertRaises(ValueError):
            preparation.checked_standard_evidence(standard)

    def test_actual_standard_source_file_is_fingerprinted(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "mod.rs"
            path.write_bytes(preparation.STD_SOURCE.read_bytes() + b"\n// changed\n")
            with self.assertRaisesRegex(ValueError, "standard-library source"):
                preparation.standard_sources(path)

    def test_exact_two_original_field_lists_are_preserved(self):
        source, certificate, metadata = preparation.expected()
        self.assertEqual(
            [item["fields"] for item in metadata["callsites"]],
            [[2, 2, 2, 2], [2, 2, 2, 2, 0, 2]],
        )
        self.assertEqual(source.count("remaining = extraction_preflight_field"), 10)
        self.assertIn("init_fields_preserved", certificate)
        self.assertIn("response_fields_preserved", certificate)
        self.assertNotIn("axiom ", certificate)

    def test_isolated_fixture_keeps_all_evercddl_source_unchanged(self):
        before = preparation.checkpoint.snapshot()
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "fixture"
            preparation.prepare(fixture)
            preparation.check_fixture(fixture)
            path = fixture / "beaconcrypt-parse/src/generated/transport.rs"
            path.write_text(path.read_text() + "\n// forbidden\n")
            with self.assertRaisesRegex(ValueError, "EverCDDL"):
                preparation.check_fixture(fixture)
        self.assertEqual(preparation.checkpoint.snapshot(), before)

    def test_existing_or_worktree_destination_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "new destination"):
                preparation.prepare(Path(directory))
        with self.assertRaisesRegex(ValueError, "outside"):
            preparation.prepare(preparation.ROOT / "var/forbidden-preflight")

    def test_prepared_source_cannot_change_after_manifest_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "fixture"
            preparation.prepare(fixture)
            path = fixture / preparation.LIB
            path.write_text(
                path.read_text().replace(
                    "if width > rest.len()", "if width >= rest.len()", 1
                )
            )
            manifest_path = fixture / preparation.MANIFEST
            manifest = json.loads(manifest_path.read_text())
            manifest["prepared_lib_sha256"] = preparation.checkpoint.digest(
                path.read_bytes()
            )
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                preparation.check_fixture(fixture)

    def test_generated_body_mutation_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            path = destination / "Funs.lean"
            path.write_text(path.read_text() + "\n-- changed\n")
            with self.assertRaises(ValueError):
                extraction.check_source(
                    destination=destination, certificate=certificate
                )

    def test_external_file_cannot_add_a_codec_law_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\naxiom codec_correct : True\n")
            provenance = json.loads((destination / "provenance.json").read_text())
            provenance["installed_sha256"][path.name] = extraction.checkpoint.digest(
                path.read_bytes()
            )
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaisesRegex(ValueError, "imports only"):
                extraction.check_source(
                    destination=destination, certificate=certificate
                )

    def test_preflight_cannot_claim_complete_public_codec_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            destination, certificate = self.fixture(Path(directory))
            provenance = json.loads((destination / "provenance.json").read_text())
            provenance["public_codec_law_proved"] = True
            (destination / "provenance.json").write_text(json.dumps(provenance))
            with self.assertRaisesRegex(ValueError, "public codec law"):
                extraction.check_source(
                    destination=destination, certificate=certificate
                )


if __name__ == "__main__":
    unittest.main()
