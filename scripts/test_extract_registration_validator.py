#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for actual parser source and text/map boundaries."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
import extract_registration_validator as extraction


class ValidatorExtractionTests(unittest.TestCase):
    def installed(self, directory):
        target = Path(directory) / "installed"
        shutil.copytree(extraction.DESTINATION, target)
        return target

    def rewrite(self, target, update):
        path = target / "provenance.json"
        value = json.loads(path.read_text())
        update(value)
        path.write_text(json.dumps(value))

    def test_current_source(self):
        extraction.check_source()
        source = (extraction.DESTINATION / "Funs.lean").read_text()
        for name in (
            "cbordetver.cbor_det_parse",
            "cbordetveraux.cbor_validate",
            "transport.validate_and_parse_initkex",
            "transport.validate_and_parse_kexresponse",
        ):
            self.assertIn("def " + name, source)

    def test_only_two_effects_and_actual_schema(self):
        types = (extraction.DESTINATION / "TypesExternal.lean").read_text()
        bindings = (extraction.DESTINATION / "FunsExternal.lean").read_text()
        self.assertEqual(types.count("→ RustM Bool"), 2)
        self.assertNotIn(" : Prop", types)
        self.assertNotIn("axiom ", types + bindings)
        self.assertIn(
            "import BeaconcryptCore.RegistrationSchemaExtraction.Funs", bindings
        )

    def test_false_full_claim(self):
        for key in (
            "public_codec_law_proved",
            "source_correspondence_proved",
            "request_lifting_proved",
        ):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                target = self.installed(directory)
                self.rewrite(target, lambda value: value.update({key: True}))
                with self.assertRaises(ValueError):
                    extraction.check_source(destination=target)

    def test_wrong_entry_tools_opacity(self):
        for key, value in (
            ("rust_start_from", []),
            ("tools", {}),
            ("opaque", []),
            ("included", ["unchecked"]),
        ):
            with self.subTest(key=key), tempfile.TemporaryDirectory() as directory:
                target = self.installed(directory)
                self.rewrite(target, lambda record: record.update({key: value}))
                with self.assertRaises(ValueError):
                    extraction.check_source(destination=target)

    def test_rehashed_controller(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.installed(directory)
            path = target / "Funs.lean"
            before = path.read_text()
            changed = before.replace("1#usize", "2#usize", 1)
            self.assertNotEqual(before, changed)
            path.write_text(changed)
            self.rewrite(
                target,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaises(ValueError):
                extraction.check_source(destination=target)

    def test_rehashed_model_law(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.installed(directory)
            path = target / "TypesExternal.lean"
            path.write_text(path.read_text() + "\naxiom unchecked : True\n")
            self.rewrite(
                target,
                lambda value: value["installed_sha256"].update(
                    {path.name: extraction.checkpoint.digest(path.read_bytes())}
                ),
            )
            with self.assertRaises(ValueError):
                extraction.check_source(destination=target)

    def test_incomplete_source_roster(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.installed(directory)
            self.rewrite(
                target,
                lambda value: value["source_preparation"]["unchanged_sha256"].popitem(),
            )
            with self.assertRaises(ValueError):
                extraction.check_source(destination=target)

    def test_shared_source(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.installed(directory)

            def update(value):
                value["normalization"]["Funs.lean"]["omitted_shared_groups"][0][
                    "source"
                ] += "\naxiom unchecked : True\n"

            self.rewrite(target, update)
            with self.assertRaises(ValueError):
                extraction.check_source(destination=target)

    def test_extra_metadata_claim(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.installed(directory)
            self.rewrite(
                target, lambda value: value.update({"complete_native_security": True})
            )
            with self.assertRaises(ValueError):
                extraction.check_source(destination=target)

    def test_combined_modes(self):
        result = subprocess.run(
            [
                sys.executable,
                str(Path(extraction.__file__)),
                "--write",
                "--check-source",
            ],
            capture_output=True,
            text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not allowed with argument", result.stderr)


if __name__ == "__main__":
    unittest.main()
