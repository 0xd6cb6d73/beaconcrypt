#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the two ordinary SDK borrow localizations."""

import unittest
from pathlib import Path
import prepare_adapter_public_ordinary as preparation

ROOT = Path(__file__).resolve().parents[1]


class PreparationTests(unittest.TestCase):
    def test_exact_two_localizations(self):
        original = (ROOT / preparation.SOURCE).read_text()
        prepared = preparation.transform(original)
        restored = prepared.replace(
            preparation.LOCALIZED, preparation.ORIGINAL, 1
        ).replace(preparation.BORROWED_MATCH, preparation.BORROWED_TRY, 1)
        self.assertEqual(restored, original)
        self.assertIn("Some(remote) => Some(remote.ratchet_mut())", prepared)
        self.assertIn(
            "encrypt_message_with_ratchet(b, k, sender, &ad, ratchet)", prepared
        )

    def test_changed_getter_rejected(self):
        original = (ROOT / preparation.SOURCE).read_text()
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            preparation.transform(
                original.replace(
                    ".map(EstablishedRemote::ratchet_mut)",
                    ".map(EstablishedRemote::ratchet)",
                )
            )

    def test_changed_child_operand_rejected(self):
        original = (ROOT / preparation.SOURCE).read_text()
        with self.assertRaisesRegex(ValueError, "continuation"):
            preparation.transform(
                original.replace(
                    preparation.BORROWED_TRY,
                    preparation.BORROWED_TRY.replace("sender, &ad", "k, &ad"),
                )
            )

    def test_duplicate_accessor_rejected(self):
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            preparation.transform(
                preparation.ORIGINAL + preparation.ORIGINAL + preparation.BORROWED_TRY
            )


if __name__ == "__main__":
    unittest.main()
