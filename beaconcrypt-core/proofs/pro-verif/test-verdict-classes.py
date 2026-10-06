#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for complete, honest verdict classification; no ProVerif."""

import copy
import importlib.util
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "classes", HERE / "check-verdict-classes.py"
)
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class ClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = CHECK.INVENTORY.expected_verdicts()
        cls.rows = CHECK.read_rows(HERE / "verdict-classes.tsv")

    def check(self, rows):
        CHECK.validate(rows, self.expected)
        CHECK.validate_scope(rows)

    def test_complete(self):
        self.check(self.rows)
        self.assertEqual(
            sum(e.checker == "check-general-registration.py" for e in self.expected),
            2444,
        )

    def test_missing_or_duplicate_verdict(self):
        for rows in (self.rows[:-1], self.rows + [self.rows[0]]):
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_changed_formula_status_position_and_class(self):
        for field, value in (
            ("formula_sha256", "0" * 64),
            ("status", "false"),
            ("position", "10000"),
            ("class", "unreviewed"),
        ):
            rows = copy.deepcopy(self.rows)
            rows[0][field] = value
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_unknown_never_becomes_evidence_or_attack(self):
        for cls in (
            "security",
            "limitation",
            "negative-control",
            "witness",
            "definitional",
        ):
            rows = copy.deepcopy(self.rows)
            next(row for row in rows if row["status"] == "unknown")["class"] = cls
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_fixture_promotion_rejected(self):
        for target, position in (
            ("hkdf-prefix-conformance", "1"),
            ("failed-receive-compromise", "7"),
            ("failed-receive-compromise", "8"),
        ):
            rows = copy.deepcopy(self.rows)
            row = next(
                row
                for row in rows
                if row["target"] == target and row["position"] == position
            )
            row["class"] = "security" if row["status"] == "true" else "witness"
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_every_fs_profile_required(self):
        for target in (
            "b2s-C2",
            "b2s-C2-chosen-fs",
            "b2s-UKSr",
            "b2s-C4",
            "b2s-PINREAD",
        ):
            rows = [row for row in self.rows if row["target"] != target]
            self.assertLess(len(rows), len(self.rows))
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_fs_bound_or_hook_drift_rejected(self):
        for field, value in (("scope", "bounded Kr=0"), ("class", "definitional")):
            rows = copy.deepcopy(self.rows)
            next(row for row in rows if row["target"] == "b2s-C2")[field] = value
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_secondary_verdict_is_not_optional(self):
        rows = [
            row
            for row in self.rows
            if not (
                row["checker"] == "check-kem-controller-auth.py"
                and row["target"] == "exposed"
                and row["position"] == "8"
            )
        ]
        with self.assertRaises(ValueError):
            self.check(rows)

    def test_unreachable_origins_do_not_count_as_security(self):
        for target in (
            "target-2-query-1",
            "target-51-query-10-cached-50",
            "target-1-query-10",
            "target-1-query-14",
            "target-52-query-11",
        ):
            rows = copy.deepcopy(self.rows)
            next(row for row in rows if row["target"] == target)["class"] = "security"
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_operational_and_open_ctx_rows_are_required(self):
        for target in (
            "pending-CROSS",
            "pending-REVERSE",
            "pending-LINEAR",
            "pending-C-REUSE",
            "CTX-open",
            "CTX-open-no-commitment",
        ):
            rows = [row for row in self.rows if row["target"] != target]
            self.assertEqual(len(rows), len(self.rows) - 1)
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_operational_or_control_scope_cannot_be_promoted(self):
        for target in (
            "pending-CROSS",
            "pending-REVERSE",
            "pending-LINEAR",
            "pending-C-REUSE",
            "CTX-open",
            "CTX-open-no-commitment",
        ):
            for field, value in (
                ("class", "security"),
                ("scope", "arbitrary production schedules"),
            ):
                rows = copy.deepcopy(self.rows)
                next(row for row in rows if row["target"] == target)[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_strong_secrecy_and_all_four_controls_are_required(self):
        for target in (
            "SS-b2s",
            "SS-s2b",
            "SS-b2s-leak",
            "SS-b2s-ungated",
            "SS-s2b-leak",
            "SS-s2b-ungated",
        ):
            rows = [row for row in self.rows if row["target"] != target]
            self.assertEqual(len(rows), len(self.rows) - 1)
            with self.assertRaises(ValueError):
                self.check(rows)

    def test_strong_secrecy_process_bound_interface_and_classes_are_pinned(self):
        for target in (
            "SS-b2s",
            "SS-s2b",
            "SS-b2s-leak",
            "SS-b2s-ungated",
            "SS-s2b-leak",
            "SS-s2b-ungated",
        ):
            original = next(row for row in self.rows if row["target"] == target)
            for field, value in (
                ("scope", original["scope"].replace("K_r = 1", "K_r = 3")),
                ("scope", original["scope"].replace("process=", "unreviewed-process=")),
                (
                    "scope",
                    original["scope"].replace("Some/None bits", "optional plaintext"),
                ),
                ("class", "definitional"),
            ):
                self.assertNotEqual(original[field], value)
                rows = copy.deepcopy(self.rows)
                next(row for row in rows if row["target"] == target)[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_registration_provenance_scope_and_complete_roster(self):
        driver = CHECK.INVENTORY.module("check-registration-provenance")
        for target in driver.TARGETS:
            rows = [row for row in self.rows if row["target"] != target.name]
            self.assertEqual(len(rows), len(self.rows) - 1)
            with self.assertRaises(ValueError):
                self.check(rows)
            for field, value in (
                ("class", "definitional"),
                ("scope", "full protocol security without scope conditions"),
            ):
                rows = copy.deepcopy(self.rows)
                next(row for row in rows if row["target"] == target.name)[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)


if __name__ == "__main__":
    unittest.main()
