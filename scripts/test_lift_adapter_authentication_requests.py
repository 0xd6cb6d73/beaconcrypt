#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for source-authentication request lifting."""

import hashlib
import subprocess
import sys
import unittest
from unittest.mock import patch

import lift_adapter_authentication_requests as lift


class AuthenticationRequestLiftingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (lift.ROOT / lift.SOURCE).read_bytes()

    def rejected(self, before, after):
        before = before.encode() if isinstance(before, str) else before
        after = after.encode() if isinstance(after, str) else after
        self.assertIn(before, self.source)
        with self.assertRaises(ValueError):
            lift.transform(self.source.replace(before, after, 1))

    def test_fresh_transformation_matches_reviewed_output(self):
        self.assertEqual(
            lift.transform(self.source), (lift.ROOT / lift.DESTINATION).read_bytes()
        )

    def test_check_and_write_are_exclusive_and_do_not_mutate(self):
        before = (lift.ROOT / lift.DESTINATION).read_bytes()
        result = subprocess.run(
            [
                sys.executable,
                str(lift.ROOT / "scripts/lift_adapter_authentication_requests.py"),
                "--check",
                "--write",
            ],
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 2)
        self.assertEqual((lift.ROOT / lift.DESTINATION).read_bytes(), before)

    def test_changed_entry_declaration(self):
        self.rejected(b"def auth.authenticate_response", b"def auth.other_response")

    def test_duplicated_body(self):
        with self.assertRaises(ValueError):
            lift.transform(self.source + self.source)

    def test_hash_primitive_changed(self):
        self.rejected(b"auth.execute_hash hr", b"auth.unreviewed_hash hr")

    def test_verification_primitive_changed(self):
        self.rejected(b"auth.verify_requested mvr", b"auth.unreviewed_verify mvr")

    def test_primitive_order_swapped(self):
        changed = self.source.replace(
            b"auth.execute_hash hr", b"auth.verify_requested hr", 1
        )
        changed = changed.replace(
            b"auth.verify_requested mvr", b"auth.execute_hash mvr", 1
        )
        with self.assertRaises(ValueError):
            lift.transform(changed)

    def test_extra_primitive_call(self):
        self.rejected(
            "let digest ← auth.execute_hash hr",
            "let ignored ← auth.execute_hash hr\n    let digest ← auth.execute_hash hr",
        )

    def test_dropped_packet(self):
        self.rejected(
            b"begin_response_authentication pending packet",
            b"begin_response_authentication pending .None",
        )

    def test_changed_retained_pending(self):
        self.rejected(
            b"ResponseHash.resume val digest", b"ResponseHash.resume hashStage digest"
        )

    def test_discarded_optional_hash_reply(self):
        self.rejected(
            b"ResponseHash.resume val digest", b"ResponseHash.resume val .None"
        )

    def test_discarded_verification_verdict(self):
        self.rejected(b"        verified\n", b"        true\n")

    def test_changed_residual_exit(self):
        self.rejected(b"ControlFlow.Break residual", b"ControlFlow.Continue residual")

    def test_missing_residual_leaf_even_after_fingerprint_update(self):
        changed = self.source.replace(
            b"CoreOpsTry_traitFromResidualResultInfallibleE.from_residual",
            b"CoreOpsTry_traitFromResidualResultInfallibleE.unreviewed_residual",
            1,
        )
        text = changed.decode()
        body = (
            lift.START
            + text.split(lift.START, 1)[1].split(lift.STOP, 1)[0].rstrip()
            + "\n"
        )
        with patch.object(
            lift, "REVIEWED_BODY_SHA256", hashlib.sha256(body.encode()).hexdigest()
        ):
            with self.assertRaisesRegex(
                ValueError, "residual return leaf changed multiplicity"
            ):
                lift.transform(changed)

    def test_generated_warning_policy_is_strict(self):
        generated = lift.transform(self.source).decode()
        self.assertEqual(generated.count("set_option warningAsError true"), 1)
        self.assertNotIn("set_option linter", generated)


if __name__ == "__main__":
    unittest.main()
