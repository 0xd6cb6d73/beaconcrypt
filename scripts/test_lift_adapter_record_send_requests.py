#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject source/control-flow, leaf-roster and installed-output drift in send lifting."""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = next(
    parent
    for parent in Path(__file__).resolve().parents
    if (parent / "Cargo.toml").is_file() and (parent / "beaconcrypt-core").is_dir()
)
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
import lift_adapter_record_send_requests as lift


class Controls(unittest.TestCase):
    def source(self):
        return (ROOT / lift.SOURCE).read_bytes()

    def test_exact_source_and_provenance_headers(self):
        expected = lift.transform(self.source())
        self.assertIn(hashlib.sha256(self.source()).hexdigest().encode(), expected)
        self.assertIn(
            hashlib.sha256(Path(lift.__file__).read_bytes()).hexdigest().encode(),
            expected,
        )
        self.assertEqual((ROOT / lift.DESTINATION).read_bytes(), expected)
        self.assertNotIn(b"set_option linter.", expected)
        self.assertIn(b"warningAsError true", expected)

    def test_source_branch_order_and_primitive_changes_fail(self):
        source = self.source()
        for before, after in (
            (b"ratchet.ratchet_hkdf srkr", b"ratchet.execute_seal_request srkr"),
            (b"let response", b"let extra"),
            (
                b"ratchet.execute_commitment_hash ct",
                b"ratchet.execute_commitment_hash ct\n        let duplicate := ratchet.execute_commitment_hash ct",
            ),
            (
                b"ok (kernel1, core.option.Option.None)",
                b"ok (kernel, core.option.Option.None)",
            ),
            (b"writer written", b"writer core.option.Option.None"),
            (b"let pending2 := transcript_mut_back ct1", b"let pending2 := pending1"),
        ):
            with self.subTest(before=before):
                self.assertIn(before, source)
                with self.assertRaises(ValueError):
                    lift.transform(source.replace(before, after, 1))

    def test_missing_pure_lift_and_effect_lift_fail(self):
        for needle in (
            "beaconcrypt_core.record_effects.begin_record_send",
            "ratchet.ratchet_hkdf",
        ):
            changed = tuple(row for row in lift.REPLACEMENTS if row[0] != needle)
            with (
                self.subTest(needle=needle),
                mock.patch.object(lift, "REPLACEMENTS", changed),
            ):
                with self.assertRaisesRegex(ValueError, "unlifted source"):
                    lift.transform(self.source())

    def test_wrong_occurrence_count_fails(self):
        changed = tuple(
            (
                before,
                after,
                count + 1 if before == "ratchet.execute_commitment_hash" else count,
            )
            for before, after, count in lift.REPLACEMENTS
        )
        with mock.patch.object(lift, "REPLACEMENTS", changed):
            with self.assertRaisesRegex(ValueError, "multiplicity"):
                lift.transform(self.source())

    def test_combined_modes_cannot_modify_generated_output(self):
        target = ROOT / lift.DESTINATION
        before = target.read_bytes()
        result = subprocess.run(
            [sys.executable, str(Path(lift.__file__)), "--check", "--write"],
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn(b"not allowed with argument", result.stderr)
        self.assertEqual(target.read_bytes(), before)

    def test_check_rejects_changed_output_without_writing(self):
        with tempfile.TemporaryDirectory(prefix="bc-send-lift-controls-") as temporary:
            root = Path(temporary)
            script = root / "scripts" / Path(lift.__file__).name
            script.parent.mkdir()
            script.write_bytes(Path(lift.__file__).read_bytes())
            source = root / lift.SOURCE
            source.parent.mkdir(parents=True)
            source.write_bytes(self.source())
            target = root / lift.DESTINATION
            target.parent.mkdir(parents=True, exist_ok=True)
            changed = lift.transform(self.source()).replace(
                b"Lifted.asSlice body", b"pure body", 1
            )
            self.assertNotEqual(changed, lift.transform(self.source()))
            target.write_bytes(changed)
            result = subprocess.run(
                [sys.executable, str(script), "--check"],
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 2)
            self.assertIn(b"outer send request body differs", result.stderr)
            self.assertEqual(target.read_bytes(), changed)


if __name__ == "__main__":
    unittest.main()
