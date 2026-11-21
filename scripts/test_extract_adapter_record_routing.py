#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for actual Raw/Frame dispatcher extraction."""

import json
from pathlib import Path
import tempfile
import unittest
import extract_adapter_record_routing as extraction


class RoutingExtraction(unittest.TestCase):
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
        for name, source in self.raw.items():
            self.assertEqual(
                extraction.normalize(source, name),
                (extraction.DESTINATION / name).read_bytes(),
            )

    def reject(self, before, after):
        changed = self.raw["Funs.lean"].replace(before, after, 1)
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_reject_changed_raw_helper(self):
        self.reject(b"ratchet.join_record_parts parts", b"ratchet.other parts")

    def test_reject_changed_frame_helper(self):
        self.reject(
            b"wire.encode_frame_parts sequence sender s",
            b"wire.encode_frame_parts sender sequence s",
        )

    def test_reject_changed_branch(self):
        self.reject(b"RecordWriteRequest.Raw parts", b"RecordWriteRequest.Other parts")

    def test_reject_missing_slice_view(self):
        self.reject(b"lift (Array.to_slice parts)", b"ok arbitrary")

    def test_reject_unsafe_addition(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom route : True\n", "Funs.lean"
            )

    def test_reject_warning_suppression(self):
        source = (
            extraction.DESTINATION / "Funs.lean"
        ).read_bytes() + b"\nset_option linter.deprecated false\n"
        with self.assertRaises(ValueError):
            extraction.denormalize(source, "Funs.lean")

    def fixture(self, change):
        with tempfile.TemporaryDirectory(
            prefix="bc-record-route-control-"
        ) as temporary:
            root = Path(temporary)
            destination = root / "cohort"
            destination.mkdir()
            for name in extraction.SOURCE_FILES:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((extraction.ROOT / name).read_bytes())
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reject_runtime_source_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/ratchet.rs").write_text(
                "// changed\n"
            )
        )

    def test_reject_callback_model_drift(self):
        self.fixture(
            lambda _, destination: (destination / "FunsExternal.lean").write_text(
                "// changed\n"
            )
        )

    def test_reject_installed_source_drift(self):
        self.fixture(
            lambda _, destination: (destination / "Funs.lean").write_text(
                "// changed\n"
            )
        )

    def test_reject_new_signature(self):
        def change(_, destination):
            path = destination / "external-signatures.json"
            value = json.loads(path.read_bytes())
            value["platform_signatures"]["extra"] = "unchecked"
            path.write_text(json.dumps(value))

        self.fixture(change)


if __name__ == "__main__":
    unittest.main()
