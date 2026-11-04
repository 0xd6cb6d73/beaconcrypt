#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Provenance and negative controls for the original source writer cohort."""

import json
from pathlib import Path
import tempfile
import unittest
import extract_adapter_wire as extraction


class WriterExtraction(unittest.TestCase):
    def setUp(self):
        self.raw = {
            name: extraction.denormalize(
                (extraction.DESTINATION / name).read_bytes(), name
            )
            for name in ["Types.lean", "Funs.lean"]
        }

    def test_reviewed_source(self):
        extraction.check_source()

    def test_roundtrip(self):
        for name, raw in self.raw.items():
            self.assertEqual(
                extraction.normalize(raw, name),
                (extraction.DESTINATION / name).read_bytes(),
            )

    def test_reject_changed_branch(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    b"written = 0#usize", b"written = 1#usize"
                ),
                "Funs.lean",
            )

    def test_reject_reordered_reservation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    b"let output \xe2\x86\x90 alloc.vec.Vec.new Std.U8",
                    b"let output \xe2\x86\x90 alloc.vec.Vec.new Std.U8\n  let _ := capacity",
                ),
                "Funs.lean",
            )

    def test_reject_changed_serializer(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    extraction.RAW_SIGNATURE.encode(),
                    b"core.ops.function.FnOnce T0 (Slice Std.U8) Std.U64",
                ),
                "Funs.lean",
            )

    def test_reject_extra_declaration(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\ndef extra := 0\n", "Funs.lean"
            )

    def test_reject_external_type(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Types.lean"] + b"\ninductive Extra where | extra\n",
                "Types.lean",
            )

    def test_reject_unknown_warning_header(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\nset_option linter.unusedSimpArgs false\n",
                "Funs.lean",
            )

    def test_reject_unchecked_primitive(self):
        templates = {
            name: b"-- empty\n"
            for name in extraction.GENERATED
            if name.endswith("_Template.lean")
        }
        templates["FunsExternal_Template.lean"] = b"axiom codec : Nat\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(templates)

    def test_reject_missing_external_template(self):
        with self.assertRaises(ValueError):
            extraction.validate_templates({})

    def test_reject_warning_suppression(self):
        contents = (
            extraction.DESTINATION / "Funs.lean"
        ).read_bytes() + b"\nset_option warningAsError false\n"
        with self.assertRaises(ValueError):
            extraction.denormalize(contents, "Funs.lean")

    def fixture(self, change):
        with tempfile.TemporaryDirectory(prefix="bc-test-source-writer-") as directory:
            root = Path(directory)
            destination = root / "cohort"
            destination.mkdir()
            for name in extraction.SOURCE_FILES:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((extraction.ROOT / name).read_bytes())
            for name in [*extraction.MODELS, *extraction.INSTALLED, "provenance.json"]:
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reject_production_source_drift(self):
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

    def test_reject_installed_body_drift(self):
        self.fixture(
            lambda _, destination: (destination / "Funs.lean").write_bytes(
                (destination / "Funs.lean")
                .read_bytes()
                .replace(b"written = 0#usize", b"written = 1#usize")
            )
        )

    def test_reject_signature_drift(self):
        def change(_, destination):
            path = destination / "external-signatures.json"
            evidence = json.loads(path.read_text())
            evidence["platform_signatures"]["extra"] = "assume success"
            path.write_text(json.dumps(evidence))

        self.fixture(change)

    def test_reject_unknown_provenance_field(self):
        def change(_, destination):
            path = destination / "provenance.json"
            evidence = json.loads(path.read_text())
            evidence["unreviewed"] = "extra"
            path.write_text(json.dumps(evidence))

        self.fixture(change)


if __name__ == "__main__":
    unittest.main()
