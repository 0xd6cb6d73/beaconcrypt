#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for source-writer request lifting."""

import hashlib
import subprocess
import sys
import unittest
from unittest.mock import patch
import lift_adapter_wire_requests as lift


class WriterRequestLifting(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (lift.ROOT / lift.SOURCE).read_bytes()

    def rejected(self, before, after):
        before = before.encode() if isinstance(before, str) else before
        after = after.encode() if isinstance(after, str) else after
        self.assertIn(before, self.source)
        with self.assertRaises(ValueError):
            lift.transform(self.source.replace(before, after, 1))

    def test_checked_output(self):
        self.assertEqual(
            lift.transform(self.source), (lift.ROOT / lift.DESTINATION).read_bytes()
        )

    def test_exclusive_modes(self):
        destination = lift.ROOT / lift.DESTINATION
        before = destination.read_bytes()
        result = subprocess.run(
            [
                sys.executable,
                str(lift.ROOT / "scripts/lift_adapter_wire_requests.py"),
                "--write",
                "--check",
            ],
            capture_output=True,
        )
        self.assertEqual(result.returncode, 2)
        self.assertEqual(destination.read_bytes(), before)

    def test_changed_entry(self):
        self.rejected("def wire.encode_record", "def wire.other")

    def test_duplicate_body(self):
        with self.assertRaises(ValueError):
            lift.transform(self.source + self.source)

    def test_changed_reservation(self):
        self.rejected(
            "alloc.vec.Vec.try_reserve_exact", "alloc.vec.Vec.unreviewed_reserve"
        )

    def test_changed_zero_failure(self):
        self.rejected("written = 0#usize", "written = 1#usize")

    def test_changed_returned_vector(self):
        self.rejected("let output3 := deref_mut_back s1", "let output3 := output1")

    def test_discarded_returned_vector(self):
        self.rejected("Clone output1 capacity", "Clone output capacity")

    def test_changed_serializer_argument(self):
        self.rejected("call_once serialize s", "call_once serialize s1")

    def test_changed_truncate(self):
        self.rejected("Vec.truncate output3 written", "Vec.truncate output3 capacity")

    def test_changed_residual(self):
        self.rejected("ControlFlow.Break residual", "ControlFlow.Continue residual")

    def test_missing_leaf_after_fingerprint_update(self):
        changed = self.source.replace(b"Vec.truncate", b"Vec.unreviewed_truncate", 1)
        text = changed.decode()
        body = (
            "def wire.encode_record\n"
            + text.split("def wire.encode_record\n", 1)[1]
            .split("\nend beaconcrypt", 1)[0]
            .rstrip()
            + "\n"
        )
        with patch.object(
            lift, "REVIEWED_BODY_SHA256", hashlib.sha256(body.encode()).hexdigest()
        ):
            with self.assertRaisesRegex(ValueError, "leaf multiplicity changed"):
                lift.transform(changed)

    def test_strict_warnings(self):
        generated = lift.transform(self.source).decode()
        self.assertEqual(generated.count("set_option warningAsError true"), 1)
        self.assertNotIn("set_option linter", generated)


if __name__ == "__main__":
    unittest.main()
