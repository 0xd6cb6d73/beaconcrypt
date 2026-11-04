#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the original runtime Init authentication cohort."""

import json
import tempfile
from pathlib import Path
import unittest
import extract_adapter_init_authentication as extraction


class InitAuthenticationExtraction(unittest.TestCase):
    def setUp(self):
        self.raw = {
            name: extraction.denormalize(
                (extraction.DESTINATION / name).read_bytes(), name
            )
            for name in ["Types.lean", "Funs.lean"]
        }

    def test_reviewed_source(self):
        extraction.check_source()

    def test_exact_roundtrip(self):
        for name, raw in self.raw.items():
            self.assertEqual(
                extraction.normalize(raw, name),
                (extraction.DESTINATION / name).read_bytes(),
            )

    def rejected(self, before, after):
        raw = self.raw["Funs.lean"]
        self.assertIn(before, raw)
        with self.assertRaises(ValueError):
            extraction.normalize(raw.replace(before, after, 1), "Funs.lean")

    def test_changed_parse(self):
        self.rejected(b"PublicKey.from_bytes s1", b"PublicKey.from_bytes s")

    def test_changed_ed_open(self):
        self.rejected(b"crypto_sign.verify s val", b"crypto_sign.verify s1 val")

    def test_changed_hash(self):
        self.rejected(b"auth.execute_hash hr", b"auth.unreviewed_hash hr")

    def test_changed_mldsa_verdict(self):
        self.rejected(b"        verified", b"        true")

    def test_changed_opened_reply(self):
        self.rejected(
            b"Verification.resume pending o", b"Verification.resume pending .None"
        )

    def test_changed_retained_state(self):
        self.rejected(b"ok (cont effect1)", b"ok (cont effect)")

    def test_changed_terminal(self):
        self.rejected(
            b"done (core.option.Option.Some authenticated)",
            b"done core.option.Option.None",
        )

    def test_reject_warning_override(self):
        with self.assertRaises(ValueError):
            extraction.denormalize(
                (extraction.DESTINATION / "Funs.lean").read_bytes()
                + b"\nset_option warningAsError false\n",
                "Funs.lean",
            )

    def test_reject_external_signature(self):
        evidence = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_text()
        )
        templates = {
            name: value["source"].encode()
            for name, value in evidence["templates"].items()
        }
        templates["FunsExternal_Template.lean"] += b"\naxiom extra : Bool\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(templates)

    def test_reject_external_type(self):
        evidence = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_text()
        )
        templates = {
            name: value["source"].encode()
            for name, value in evidence["templates"].items()
        }
        templates["TypesExternal_Template.lean"] += b"\naxiom Key : Type\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(templates)

    def fixture(self, change):
        with tempfile.TemporaryDirectory(prefix="bc-test-init-source-") as directory:
            root = Path(directory)
            destination = root / "cohort"
            destination.mkdir()
            for name in extraction.SOURCE_FILES:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((extraction.ROOT / name).read_bytes())
            for name in [*extraction.MODELS, *extraction.INSTALLED, "provenance.json"]:
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reject_rust_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/auth.rs").write_text(
                "// changed\n"
            )
        )

    def test_reject_primitive_model_drift(self):
        self.fixture(
            lambda _, destination: (destination / "FunsExternal.lean").write_text(
                "// changed\n"
            )
        )

    def test_reject_installed_body_drift(self):
        self.fixture(
            lambda _, destination: (destination / "Funs.lean").write_bytes(
                (destination / "Funs.lean")
                .read_bytes()
                .replace(b"cont effect1", b"cont effect")
            )
        )


if __name__ == "__main__":
    unittest.main()
