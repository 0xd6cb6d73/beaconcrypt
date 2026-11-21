#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Strict provenance controls for the two actual runtime registration writers."""

import json
from pathlib import Path
import tempfile
import unittest
import extract_adapter_registration_writer as extraction


class RegistrationWriterExtraction(unittest.TestCase):
    def setUp(self):
        self.raw = {
            name: extraction.denormalize(
                (extraction.DESTINATION / name).read_bytes(), name
            )
            for name in ("Types.lean", "Funs.lean")
        }

    def test_reviewed_source(self):
        extraction.check_source()

    def test_roundtrip(self):
        for name, raw in self.raw.items():
            self.assertEqual(
                extraction.normalize(raw, name),
                (extraction.DESTINATION / name).read_bytes(),
            )

    def test_reject_omitted_remaining_key_field(self):
        changed = self.raw["Funs.lean"].replace(b"init.one_time_key", b"init.pq_key", 1)
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_reject_reordered_response_fields(self):
        changed = self.raw["Funs.lean"].replace(
            b"response.app_cipher_text", b"response.signature", 1
        )
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_reject_changed_writer_helper(self):
        changed = self.raw["Funs.lean"].replace(
            b"wire.encode_record", b"wire.unsafe_write", 1
        )
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_reject_new_obligation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom encode_readback : True\n", "Funs.lean"
            )

    def test_reject_mutable_serializer_interface_change(self):
        changed = (
            (extraction.DESTINATION / "Funs.lean")
            .read_bytes()
            .replace(
                b"AdapterWirePrimitive.Serializer",
                b"AdapterWirePrimitive.OtherSerializer",
                1,
            )
        )
        with self.assertRaises(ValueError):
            extraction.denormalize(changed, "Funs.lean")

    def test_reject_warning_suppression(self):
        changed = (
            extraction.DESTINATION / "Funs.lean"
        ).read_bytes() + b"\nset_option linter.deprecated false\n"
        with self.assertRaises(ValueError):
            extraction.denormalize(changed, "Funs.lean")

    def test_reject_changed_external_signature(self):
        evidence = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_bytes()
        )
        templates = {
            name: value["source"].encode()
            for name, value in evidence["templates"].items()
        }
        templates["FunsExternal_Template.lean"] += b"\naxiom extra : Nat\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(templates)

    def fixture(self, change):
        with tempfile.TemporaryDirectory(
            prefix="bc-registration-writer-control-"
        ) as directory:
            root = Path(directory)
            destination = root / "cohort"
            destination.mkdir()
            for name in extraction.SOURCE_FILES:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((extraction.ROOT / name).read_bytes())
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reject_runtime_source_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/wire.rs").write_text(
                "fn changed() {}\n"
            )
        )

    def test_reject_model_drift(self):
        self.fixture(
            lambda _, destination: (destination / "FunsExternal.lean").write_text(
                "-- changed\n"
            )
        )

    def test_reject_pure_writer_substitution(self):
        self.fixture(
            lambda root, _: (
                root
                / "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/Funs.lean"
            ).write_text("-- discarded allocator\n")
        )

    def test_reject_installed_output_drift(self):
        self.fixture(
            lambda _, destination: (destination / "Funs.lean").write_text(
                "-- changed\n"
            )
        )

    def test_reject_extra_provenance(self):
        def change(_, destination):
            path = destination / "provenance.json"
            contents = json.loads(path.read_bytes())
            contents["unreviewed"] = True
            path.write_text(json.dumps(contents))

        self.fixture(change)


if __name__ == "__main__":
    unittest.main()
