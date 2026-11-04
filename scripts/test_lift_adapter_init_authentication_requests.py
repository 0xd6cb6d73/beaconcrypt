#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for both source Init authentication bodies."""

import hashlib
import unittest
from unittest.mock import patch
import lift_adapter_init_authentication_requests as lift


class InitRequestLifting(unittest.TestCase):
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

    def test_duplicate_source(self):
        with self.assertRaises(ValueError):
            lift.transform(self.source + self.source)

    def test_changed_ed_parse(self):
        self.rejected("PublicKey.from_bytes s1", "PublicKey.from_bytes s")

    def test_changed_ed_open(self):
        self.rejected("crypto_sign.verify s val", "crypto_sign.verify s1 val")

    def test_dropped_parse_rejection(self):
        self.rejected("ControlFlow.Break residual", "ControlFlow.Continue residual")

    def test_changed_hash_leaf(self):
        self.rejected("auth.execute_hash hr", "auth.unreviewed_hash hr")

    def test_changed_verification(self):
        self.rejected("        verified", "        true")

    def test_changed_opened_view(self):
        self.rejected("Std.U8) opened", "Std.U8) .None")

    def test_changed_resume(self):
        self.rejected("InitHash.resume pending hash", "InitHash.resume pending .None")

    def test_changed_retained_state(self):
        self.rejected("ok (cont effect1)", "ok (cont effect)")

    def test_changed_terminal(self):
        self.rejected(
            "done (core.option.Option.Some authenticated)",
            "done core.option.Option.None",
        )

    def test_missing_leaf_even_after_reviewed_hash_update(self):
        changed = self.source.replace(
            b"auth.execute_hash hr", b"auth.unreviewed_hash hr", 1
        )
        selected = []
        for label, start, stop, digest in lift.SELECTED:
            text = changed.decode()
            body = start + text.split(start, 1)[1].split(stop, 1)[0].rstrip() + "\n"
            selected.append(
                (label, start, stop, hashlib.sha256(body.encode()).hexdigest())
            )
        with patch.object(lift, "SELECTED", selected):
            with self.assertRaisesRegex(ValueError, "leaf multiplicity changed"):
                lift.transform(changed)

    def test_strict_warning_policy(self):
        generated = lift.transform(self.source).decode()
        self.assertEqual(generated.count("set_option warningAsError true"), 1)
        self.assertNotIn("set_option linter", generated)


if __name__ == "__main__":
    unittest.main()
