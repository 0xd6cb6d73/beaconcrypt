#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed regression controls for actual outer-send source extraction."""

from __future__ import annotations

import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_adapter_record_send as extraction
import prepare_adapter_record_send as preparation


class Controls(unittest.TestCase):
    def test_actual_source_is_localized_only_at_selected_consumption(self):
        source = (ROOT / preparation.SOURCE).read_text()
        prepared, proof = preparation.transform(source)
        self.assertEqual(
            prepared, source.replace(preparation.BORROW, preparation.LOCAL, 1)
        )
        self.assertEqual(proof["law"], "AdapterRecordSendBorrow.aead_resume")
        self.assertEqual(preparation.transform(source)[1], proof)

    def test_body_and_primitive_order_drift_are_rejected(self):
        source = (ROOT / preparation.SOURCE).read_text()
        changes = [
            (
                "let response = ratchet_hkdf(pending.request());",
                "let response = execute_write_request(pending.request());",
            ),
            (
                "let detached = execute_seal_request(aead.request());",
                "let detached = execute_seal_request(aead.request());\n\tlet _extra = ratchet_hkdf(pending.request());",
            ),
            ("return (kernel, None),", "(kernel, None),"),
            ("commitment.transcript_mut()", "commitment.transcript()"),
            (
                "let (kernel, output) = writer.finish(written);",
                "let (kernel, output) = writer.finish(None);",
            ),
        ]
        start = source.index(preparation.MARKER)
        prefix, selected = source[:start], source[start:]
        for before, after in changes:
            with self.subTest(before=before):
                self.assertIn(before, selected)
                with self.assertRaises(ValueError):
                    preparation.transform(prefix + selected.replace(before, after, 1))

    def test_fixture_changed_files_extra_files_and_symlinks_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix="bc-send-controls-") as temporary:
            fixture = Path(temporary) / "source"
            proof = preparation.prepare(ROOT, fixture)
            target = fixture / preparation.SOURCE
            original = target.read_bytes()
            target.write_bytes(original + b"\n// changed fixture\n")
            with self.assertRaises(ValueError):
                preparation.check_fixture(fixture, proof)
            target.write_bytes(original)
            extra = fixture / "extra.rs"
            extra.write_text("extra")
            with self.assertRaises(ValueError):
                preparation.check_fixture(fixture, proof)
            extra.unlink()
            extra.symlink_to(target)
            with self.assertRaises(ValueError):
                preparation.check_fixture(fixture, proof)
            extra.unlink()
            preparation.check_fixture(fixture, proof)

    def test_generated_body_and_warning_drift_are_rejected(self):
        for name in ("Types.lean", "Funs.lean"):
            installed = (extraction.DESTINATION / name).read_bytes()
            raw = extraction.denormalize(installed, name)
            self.assertEqual(extraction.normalize(raw, name), installed)
            for changed in (
                raw + b"\n-- body changed\n",
                raw.replace(b"linter.hashCommand false", b"linter.hashCommand true"),
            ):
                with self.assertRaises(ValueError):
                    extraction.normalize(changed, name)
        body = (extraction.DESTINATION / "Funs.lean").read_bytes()
        for changed in (
            body.replace(b"let response", b"let extra", 1),
            body.replace(
                b"ratchet.execute_seal_request asr",
                b"ratchet.execute_write_request asr",
                1,
            ),
            body.replace(b"writer written", b"writer core.option.Option.None", 1),
            body.replace(b"warningAsError true", b"warningAsError false", 1),
            body.replace(
                b"variable [beaconcrypt_record_send.ratchet.Operations]", b"", 1
            ),
        ):
            self.assertNotEqual(changed, body)
            with self.assertRaises(ValueError):
                extraction.denormalize(changed, "Funs.lean")

    def test_external_signature_and_model_drift_are_rejected(self):
        evidence = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_text()
        )
        templates = {
            name: value["source"].encode()
            for name, value in evidence["templates"].items()
        }
        extraction.validate_templates(templates)
        broken = copy.deepcopy(templates)
        broken["FunsExternal_Template.lean"] += b"\n-- unreviewed primitive\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(broken)
        with tempfile.TemporaryDirectory(prefix="bc-send-model-controls-") as temporary:
            destination = Path(temporary)
            for name in extraction.MODELS:
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            path = destination / "FunsExternal.lean"
            path.write_bytes(
                path.read_bytes().replace(b"operations.hash", b"operations.writer", 1)
            )
            with self.assertRaises(ValueError):
                extraction.validate_models(ROOT, destination)

    def test_combined_modes_cannot_mutate_installed_output(self):
        before = {
            name: (extraction.DESTINATION / name).read_bytes()
            for name in extraction.INSTALLED
        }
        result = subprocess.run(
            [sys.executable, str(Path(extraction.__file__)), "--write", "--check"],
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn(b"not allowed with argument", result.stderr)
        self.assertEqual(
            before,
            {
                name: (extraction.DESTINATION / name).read_bytes()
                for name in extraction.INSTALLED
            },
        )


if __name__ == "__main__":
    unittest.main()
