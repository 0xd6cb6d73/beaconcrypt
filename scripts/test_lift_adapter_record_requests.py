#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the extracted receive-body request transformation."""

import unittest
from unittest.mock import patch
import hashlib
import subprocess
import sys

import lift_adapter_record_requests as lift


class RequestLiftingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (lift.ROOT / lift.SOURCE).read_bytes()

    def test_fresh_transformation_matches_checked_in_body(self):
        self.assertEqual(
            lift.transform(self.source), (lift.ROOT / lift.DESTINATION).read_bytes()
        )

    def test_check_and_write_are_mutually_exclusive_and_leave_output_unchanged(self):
        destination = lift.ROOT / lift.DESTINATION
        before = destination.read_bytes()
        result = subprocess.run(
            [
                sys.executable,
                str(lift.ROOT / "scripts/lift_adapter_record_requests.py"),
                "--check",
                "--write",
            ],
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertEqual(destination.read_bytes(), before)

    def rejected(self, before, after):
        before = before.encode() if isinstance(before, str) else before
        after = after.encode() if isinstance(after, str) else after
        self.assertIn(before, self.source)
        with self.assertRaises(ValueError):
            lift.transform(self.source.replace(before, after, 1))

    def test_changed_loop_declaration(self):
        self.rejected(
            b"def ratchet.execute_record_receive_loop.body", b"def ratchet.other.body"
        )

    def test_dropped_rejection_branch(self):
        self.rejected(
            b"ok (done (kernel, core.option.Option.None))", b"ok (cont effect)"
        )

    def test_extra_repeated_kdf_call(self):
        self.rejected(
            "let response ← ratchet.ratchet_hkdf srkr",
            "let response ← ratchet.ratchet_hkdf srkr\n    let extra ← ratchet.ratchet_hkdf srkr",
        )

    def test_changed_call_order(self):
        self.rejected(
            "let s ← lift (Array.to_slice actual1)\n        let pending2 := transcript_mut_back ct1",
            "let pending2 := transcript_mut_back ct1\n        let s ← lift (Array.to_slice actual1)",
        )

    def test_extra_unrecognized_primitive(self):
        self.rejected(
            "let response ← ratchet.ratchet_hkdf srkr",
            "let response ← ratchet.unreviewed_primitive srkr",
        )

    def test_dropped_optional_hash_failure(self):
        self.rejected(
            b"| core.option.Option.None =>", b"| core.option.Option.Some _ =>"
        )

    def test_changed_hash_borrow_continuation(self):
        self.rejected(
            b"let pending2 := transcript_mut_back ct1", b"let pending2 := pending"
        )

    def test_changed_comparison_arguments(self):
        self.rejected(
            b"beaconcrypt_crypto.utils.memcmp s s1",
            b"beaconcrypt_crypto.utils.memcmp s s",
        )

    def test_dropped_aead_finish(self):
        self.rejected(
            b"beaconcrypt_core.record_effects.RecordReceiveAead.finish pending",
            b"beaconcrypt_core.record_effects.RecordReceiveAead.request pending",
        )

    def test_changed_returned_kernel(self):
        self.rejected(
            b"ok (done (kernel, o1))", b"ok (done (kernel, core.option.Option.None))"
        )

    def test_duplicated_body(self):
        with self.assertRaises(ValueError):
            lift.transform(self.source + self.source)

    def test_missing_lift_rejected_after_reviewed_fingerprint_update(self):
        changed = self.source.replace(
            b"lift (Array.to_slice actual1)", b"lift (Array.to_slice a)", 1
        )
        text = changed.decode()
        body = (
            lift.START.removeprefix("@[rust_loop_body]\n")
            + text.split(lift.START, 1)[1].split(lift.STOP, 1)[0].rstrip()
            + "\n"
        )
        with patch.object(
            lift, "REVIEWED_BODY_SHA256", hashlib.sha256(body.encode()).hexdigest()
        ):
            with self.assertRaisesRegex(ValueError, "changed multiplicity"):
                lift.transform(changed)


if __name__ == "__main__":
    unittest.main()
