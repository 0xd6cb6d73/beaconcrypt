#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression tests for exact Beacon queries, alpha names and actual traces."""

import importlib.util
from pathlib import Path
import re
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "beacon_checker", HERE / "check-registration-beacon.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def output(queries, verdicts, traces=0):
    results = [
        query + (" cannot be proved." if verdict == "unknown" else f" is {verdict}.")
        for query, verdict in zip(queries, verdicts, strict=True)
    ]
    return "\n".join(
        [
            *("RESULT " + result for result in results),
            *("A trace has been found." for _ in range(traces)),
            "Verification summary:",
            *("Query " + result for result in results),
        ]
    )


class ExactBeaconGate(unittest.TestCase):
    def setUp(self):
        self.text = output(CHECKER.PRIMARY, CHECKER.VERDICTS)

    def check(self, text):
        CHECKER.check_output(text, CHECKER.PRIMARY, CHECKER.VERDICTS, 0)

    def test_valid_baseline(self):
        self.check(self.text)

    def test_alpha_names(self):
        renamed = re.sub(r"\b(owner|attempt)_2\b", r"\1_973", self.text)
        self.assertNotEqual(renamed, self.text)
        self.check(renamed)

    def test_repeated_variable_cannot_split(self):
        altered = self.text.replace(
            "RegistrationBeaconAttempt(owner_2", "RegistrationBeaconAttempt(owner_984"
        )
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_distinct_variables_cannot_merge(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("prior,raw_1", "attempt_2,raw_1"))

    def test_constructor_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("hkdf_second_32", "hkdf_first_32"))

    def test_target_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("first_sequence", "general_zero_sequence"))

    def test_cache_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("receive_cache_empty", "receive_cache_entry"))

    def test_missing_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[1])

    def test_duplicated_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[0] + "\n" + self.text)

    def test_missing_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("Verification summary:", ""))

    def test_duplicated_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text + "\nVerification summary:\n")

    def test_changed_summary(self):
        first, last = self.text.split("Verification summary:")
        with self.assertRaises(ValueError):
            self.check(
                first
                + "Verification summary:"
                + last.replace(" is true.", " is false.", 1)
            )

    def test_unknown_cannot_be_relabelled(self):
        for verdict in ["true", "false"]:
            with self.subTest(verdict=verdict), self.assertRaises(ValueError):
                self.check(self.text.replace(" cannot be proved.", f" is {verdict}."))

    def test_proof_cannot_be_unknown(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace(" is true.", " cannot be proved.", 1))

    def test_actual_traces_required(self):
        verdicts = CHECKER.control_cases()[0][2]
        text = output(CHECKER.TAIL, verdicts, verdicts.count("false"))
        CHECKER.check_output(text, CHECKER.TAIL, verdicts, verdicts.count("false"))
        for changed in [
            text.replace(
                "A trace has been found.",
                "A trace has been found, assuming a hypothesis:",
            ),
            text + "\nA trace has been found.\n",
        ]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                CHECKER.check_output(
                    changed, CHECKER.TAIL, verdicts, verdicts.count("false")
                )

    def test_warning_and_error_rejected(self):
        for notice in ["Warning: changed theory", "Error: bad model"]:
            with self.subTest(notice=notice), self.assertRaises(ValueError):
                self.check(notice + "\n" + self.text)

    def test_exact_mutation_anchor(self):
        for text in ["absent", "token token"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                CHECKER.BASE.exact_replace(text, "token", "replacement")

    def test_single_preparation_has_exact_two_anchors(self):
        original = (HERE / "registration-beacon-control.pv").read_text()
        changed = CHECKER.single_preparation(original)
        self.assertEqual(changed.count("RegistrationBeaconControlRetry("), 1)
        with self.assertRaises(ValueError):
            CHECKER.single_preparation(changed)

    def test_reviewed_source_and_plan_anchors(self):
        CHECKER.check_source_order()


if __name__ == "__main__":
    unittest.main()
