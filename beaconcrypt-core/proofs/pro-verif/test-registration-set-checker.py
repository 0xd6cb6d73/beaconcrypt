#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject misleading or incomplete admission-verification receipts."""

import importlib.util
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location(
    "registration_set_checker", Path(__file__).with_name("check-registration-set.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.query = CHECKER.PRIMARY[0]
        self.result = self.query + " is true."
        self.output = (
            "RESULT "
            + self.result
            + "\nVerification summary:\nQuery "
            + self.result
            + "\n"
        )

    def check(self, output):
        CHECKER.check_output(output, [self.query], ["true"], 0)

    def test_complete(self):
        self.check(self.output)

    def test_missing_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("RESULT " + self.result + "\n", ""))

    def test_changed_event_argument(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("attempt_1", "other_attempt"))

    def test_changed_polarity(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("is true.", "is false."))

    def test_summary_disagrees(self):
        with self.assertRaises(ValueError):
            self.check(
                self.output.replace(
                    "Query " + self.result, "Query " + self.query + " is false."
                )
            )

    def test_extra_primary(self):
        with self.assertRaises(ValueError):
            self.check("RESULT " + self.result + "\n" + self.output)

    def test_missing_reconstructed_trace(self):
        query = CHECKER.REACHABLE[0]
        output = f"RESULT {query} is false.\nVerification summary:\nQuery {query} is false.\n"
        with self.assertRaises(ValueError):
            CHECKER.check_output(output, [query], ["false"], 1)
        CHECKER.check_output(
            "A trace has been found.\n" + output, [query], ["false"], 1
        )

    def test_unknown_is_not_true(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("is true.", "cannot be proved."))

    def test_source_mapping_order(self):
        CHECKER.check_source_order()

    def test_control_anchor_not_duplicated(self):
        with self.assertRaises(ValueError):
            CHECKER.exact_replace("guard guard", "guard", "changed")


if __name__ == "__main__":
    unittest.main()
