#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the original guard and typed source-leaf certificate."""

import json
from pathlib import Path
import tempfile
import unittest

import certify_registration_shallow_dispatch as certificate


class ShallowDispatchCertificateTests(unittest.TestCase):
    def fixture(self, directory):
        directory = Path(directory)
        lean, manifest = certificate.expected()
        lean_path, manifest_path = (
            directory / "control.lean",
            directory / "control.json",
        )
        lean_path.write_text(lean)
        manifest_path.write_text(json.dumps(manifest))
        return lean_path, manifest_path

    def mutate_manifest(self, update):
        with tempfile.TemporaryDirectory() as directory:
            lean_path, manifest_path = self.fixture(directory)
            manifest = json.loads(manifest_path.read_text())
            update(manifest)
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "provenance drift"):
                certificate.check(lean_path=lean_path, manifest_path=manifest_path)

    def test_current_exact_original_branches_and_checked_leaves_match(self):
        certificate.check()
        _, manifest = certificate.expected()
        self.assertEqual(len(manifest["typed_constructor_leaves"]), 4)
        self.assertEqual(len(manifest["control"]), 2)
        self.assertFalse(manifest["whole_generic_dispatcher_extracted"])
        self.assertTrue(manifest["generated_rust_files_unchanged"])

    def test_source_guard_mutation_is_rejected(self):
        self.mutate_manifest(
            lambda value: value["control"][0].update(
                {"prefix": "let deep: bool = false;"}
            )
        )

    def test_original_deep_failure_paths_cannot_be_dropped(self):
        self.mutate_manifest(
            lambda value: value["control"][1].update({"deep_branch": "true"})
        )

    def test_constructor_leaf_source_change_is_rejected(self):
        self.mutate_manifest(
            lambda value: value["typed_constructor_leaves"][2].update(
                {"source": "return true;"}
            )
        )

    def test_constructor_signature_change_is_rejected(self):
        self.mutate_manifest(
            lambda value: value["typed_constructor_leaves"][0].update(
                {"input": "cbor_array"}
            )
        )

    def test_full_codec_and_native_claims_are_rejected(self):
        for key in (
            "whole_generic_dispatcher_extracted",
            "public_codec_law_proved",
            "native_codec_instance_proved",
        ):
            with self.subTest(key=key):
                self.mutate_manifest(lambda value: value.update({key: True}))

    def test_source_and_generator_provenance_changes_are_rejected(self):
        for key in (
            "source_sha256",
            "certificate_generator_sha256",
            "extracted_source_provenance_sha256",
        ):
            with self.subTest(key=key):
                self.mutate_manifest(lambda value: value.update({key: "0" * 64}))

    def test_rehashed_wrong_leaf_still_fails_exact_reconstruction(self):
        with tempfile.TemporaryDirectory() as directory:
            lean_path, manifest_path = self.fixture(directory)
            wrong = lean_path.read_text().replace(
                "extraction_serialize_shallow_int integer out offset",
                "other (.CBOR_Case_Int integer) out offset",
                1,
            )
            lean_path.write_text(wrong)
            manifest = json.loads(manifest_path.read_text())
            manifest["checked_lean_sha256"] = certificate.checkpoint.digest(
                wrong.encode()
            )
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(ValueError, "leaf instantiation drift"):
                certificate.check(lean_path=lean_path, manifest_path=manifest_path)

    def test_guards_and_appended_axioms_cannot_be_changed(self):
        for transform in (
            lambda value: value.replace("#guard_msgs in\n", "", 1),
            lambda value: value + "\naxiom completed_codec : False\n",
        ):
            with (
                self.subTest(transform=transform),
                tempfile.TemporaryDirectory() as directory,
            ):
                lean_path, manifest_path = self.fixture(directory)
                lean_path.write_text(transform(lean_path.read_text()))
                with self.assertRaisesRegex(ValueError, "leaf instantiation drift"):
                    certificate.check(lean_path=lean_path, manifest_path=manifest_path)


if __name__ == "__main__":
    unittest.main()
