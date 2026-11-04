#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for source encoder controllers and explicit codec calls."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest

import extract_registration_serializer as extraction


class RegistrationSerializerExtractionTests(unittest.TestCase):
    def installed(self, directory):
        path = Path(directory) / "installed"
        shutil.copytree(extraction.DESTINATION, path)
        return path

    def rewrite(self, destination, update):
        path = destination / "provenance.json"
        value = json.loads(path.read_text())
        update(value)
        path.write_text(json.dumps(value))

    def test_current_source_and_complete_controller_bodies_match(self):
        extraction.check_source()
        self.assertEqual(
            extraction.ENTRIES, ("extraction_encode_init", "extraction_encode_response")
        )
        source = (extraction.DESTINATION / "Funs.lean").read_text()
        for name in (
            "extraction_encode_init",
            "extraction_encode_response",
            "transport.extraction_serialize_initkex",
            "transport.extraction_serialize_kexresponse",
            "cbordetver.cbor_det_serialize",
            "cbordetveraux.cbor_size",
            "cbordetveraux.cbor_serialize",
        ):
            self.assertIn("def " + name, source)
        self.assertIn("beaconcrypt_core.transport.encoded_init_len", source)
        self.assertIn("beaconcrypt_core.transport.encoded_response_len", source)

    def test_explicit_signatures_have_complete_mutable_poststate(self):
        templates = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_text()
        )
        source = templates["FunsExternal_Template.lean"]["source"]
        self.assertEqual(source.count("axiom "), 5)
        self.assertIn("RustM (Bool × (Slice", source)
        self.assertIn("RustM (Std.Usize ×", source)
        installed = (extraction.DESTINATION / "TypesExternal.lean").read_text()
        self.assertNotIn("axiom ", installed)
        self.assertNotIn(" : Prop", installed)

    def test_component_cannot_claim_full_codec_or_stateful_lift(self):
        for key in (
            "public_codec_law_proved",
            "source_correspondence_proved",
            "request_lifting_proved",
        ):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                self.rewrite(destination, lambda value: value.update({key: True}))
                with self.assertRaisesRegex(ValueError, "cannot assert"):
                    extraction.check_source(destination=destination)

    def test_entry_pin_or_opacity_mutation_rejected(self):
        for key, replacement in (
            ("rust_start_from", ["opaque_parser"]),
            ("tools", {"aeneas": "candidate"}),
            ("opaque", []),
            ("included", []),
        ):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                destination = self.installed(directory)
                self.rewrite(
                    destination, lambda value: value.update({key: replacement})
                )
                with self.assertRaises(ValueError):
                    extraction.check_source(destination=destination)

    def test_rehashed_controller_mutation_still_requires_raw_reconstruction(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "Funs.lean"
            path.write_text(path.read_text().replace("3309#u64", "3308#u64", 1))
            self.rewrite(
                destination,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaisesRegex(
                ValueError, "raw generated source reconstruction"
            ):
                extraction.check_source(destination=destination)

    def test_external_cannot_gain_codec_law_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "TypesExternal.lean"
            path.write_text(path.read_text() + "\naxiom complete_codec : True\n")
            self.rewrite(
                destination,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaisesRegex(ValueError, "Operations and bindings"):
                extraction.check_source(destination=destination)

    def test_source_boundary_certificate_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)

            def mutate(value):
                value["source_preparation"]["field_boundaries"][0][
                    "original_expression"
                ] += " return 0;"

            self.rewrite(destination, mutate)
            with self.assertRaisesRegex(ValueError, "preparation certificate"):
                extraction.check_source(destination=destination)

    def test_lean_boundary_certificate_is_exact_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "SourceCertificates.lean"
            path.write_text(
                path.read_text().replace("helper_eta", "unreviewed_boundary", 1)
            )
            self.rewrite(
                destination,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaisesRegex(ValueError, "Lean certificate"):
                extraction.check_source(destination=destination)

    def test_template_names_cannot_be_swapped_after_rehash(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)
            path = destination / "external-signatures.json"
            value = json.loads(path.read_text())
            first, second = "TypesExternal_Template.lean", "FunsExternal_Template.lean"
            value[first], value[second] = value[second], value[first]
            path.write_text(json.dumps(value))

            def mutate(provenance):
                provenance["external_templates"] = value
                provenance["installed_sha256"][path.name] = (
                    extraction.checkpoint.digest(path.read_bytes())
                )

            self.rewrite(destination, mutate)
            with self.assertRaisesRegex(
                ValueError, "unreviewed serializer external signature"
            ):
                extraction.check_source(destination=destination)

    def test_shared_source_mutation_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            destination = self.installed(directory)

            def mutate(value):
                value["normalization"]["Funs.lean"]["omitted_shared_groups"][0][
                    "source"
                ] += "\naxiom changed : True\n"

            self.rewrite(destination, mutate)
            with self.assertRaisesRegex(ValueError, "shared source"):
                extraction.check_source(destination=destination)


if __name__ == "__main__":
    unittest.main()
