#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for complete, honest verdict classification; no ProVerif."""

import copy
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

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

    def test_awk_inventory_uses_short_commands_and_live_probe_file(self):
        run = CHECK.INVENTORY.subprocess.run
        probes = set()
        scenarios = set()

        def checked_run(args, **kwargs):
            if args[0] != "awk":
                return run(args, **kwargs)
            self.assertLess(len(CHECK.INVENTORY.subprocess.list2cmdline(args)), 32767)
            self.assertEqual(args[:2], ["awk", "-v"])
            self.assertEqual(args[-2], "-f")
            path = Path(args[-1])
            self.assertTrue(path.is_file(), "AWK source must exist during execution")
            if path.name != "check-results.awk":
                probes.add(path)
                scenarios.add(args[2])
                probe = path.read_text(encoding="utf-8")
                self.assertGreater(len(probe), 32767)
                self.assertIn("function reject(message) {}", probe)
                self.assertIn(
                    "function require_exact(wanted, label, query_index, found) { print wanted }",
                    probe,
                )
            return run(args, **kwargs)

        with mock.patch.object(CHECK.INVENTORY.subprocess, "run", checked_run):
            expected = CHECK.INVENTORY.expected_verdicts()
        CHECK.validate(self.rows, expected)
        self.assertEqual(len(probes), 1)
        self.assertGreater(len(scenarios), 1)
        self.assertTrue(all(not path.exists() for path in probes))

    def test_inventory_without_posix_solver_modules(self):
        with mock.patch.dict(sys.modules, {"resource": None, "fcntl": None}):
            expected = CHECK.INVENTORY.expected_verdicts()
        self.assertEqual(expected, self.expected)
        CHECK.validate(self.rows, expected)
        CHECK.validate_scope(self.rows)

    def test_legacy_source_scope_cannot_be_promoted(self):
        for name in CHECK.LEGACY_SOURCE_CHECKERS:
            with self.subTest(checker=name):
                rows = copy.deepcopy(self.rows)
                row = next(row for row in rows if row["checker"] == name + ".py")
                self.assertTrue(row["scope"].startswith(CHECK.LEGACY_SOURCE_SCOPE))
                row["scope"] = row["scope"].removeprefix(CHECK.LEGACY_SOURCE_SCOPE)
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_legacy_checkers_require_explicit_projection_marker(self):
        marker = (
            "(* @beaconcrypt-fidelity-v1 legacy_profiles.scope="
            "classical_projection:MLDSA_guards_not_globally_lifted *)"
        )
        original = (HERE / "production-transcript-interface.pvl").read_text()
        self.assertEqual(original.count(marker), 1)
        names = CHECK.LEGACY_SOURCE_CHECKERS | {"check-free-schedule"}
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for name in names:
                driver = CHECK.INVENTORY.module(name)
                for changed in (
                    original.replace(marker, ""),
                    original.replace(marker, "(* full ML-DSA source proof *)"),
                    original + "\n" + marker,
                ):
                    (directory / "production-transcript-interface.pvl").write_text(
                        changed
                    )
                    with (
                        self.subTest(checker=name),
                        self.assertRaisesRegex(
                            ValueError, "reviewed classical-projection scope"
                        ),
                    ):
                        driver.validate_targets(directory=directory)

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

    def test_delayed_origin_exact_scope_and_all_secondary_results(self):
        driver = CHECK.INVENTORY.module("check-delayed-response")
        for target in driver.TARGETS:
            selected = [row for row in self.rows if row["target"] == target.name]
            self.assertEqual(len(selected), len(target.results))
            for original in selected:
                rows = [row for row in self.rows if row is not original]
                with self.assertRaises(ValueError):
                    self.check(rows)
                for field, value in (
                    ("class", "definitional"),
                    ("scope", "unconditional full protocol authentication"),
                ):
                    rows = copy.deepcopy(self.rows)
                    next(
                        row
                        for row in rows
                        if row["target"] == target.name
                        and row["position"] == original["position"]
                    )[field] = value
                    with self.assertRaises(ValueError):
                        self.check(rows)

    def test_exact_far_scopes_are_not_global_or_reply_oracles(self):
        driver = CHECK.INVENTORY.module("check-exact-far")
        for target in driver.TARGETS:
            for field, value in (
                ("class", "definitional"),
                ("scope", "all sessions and actual plaintext replies"),
            ):
                rows = copy.deepcopy(self.rows)
                next(
                    row
                    for row in rows
                    if row["checker"] == "check-exact-far.py"
                    and row["target"] == target.name
                )[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_record_origin_scope_roster_and_witness_bound_are_explicit(self):
        driver = CHECK.INVENTORY.module("check-record-origin")
        for target in driver.TARGETS:
            selected = [
                row
                for row in self.rows
                if row["checker"] == "check-record-origin.py"
                and row["target"] == target.name
            ]
            self.assertEqual(len(selected), 1)
            with self.assertRaises(ValueError):
                self.check([row for row in self.rows if row is not selected[0]])
            for field, value in (
                ("class", "definitional"),
                (
                    "scope",
                    "solver-proved injectivity for every unbounded protocol record",
                ),
            ):
                rows = copy.deepcopy(self.rows)
                next(
                    row
                    for row in rows
                    if row["checker"] == "check-record-origin.py"
                    and row["target"] == target.name
                )[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_tasking_origin_scope_roster_and_witness_bound_are_explicit(self):
        driver = CHECK.INVENTORY.module("check-tasking-origin")
        for target in driver.TARGETS:
            selected = [
                row
                for row in self.rows
                if row["checker"] == "check-tasking-origin.py"
                and row["target"] == target.name
            ]
            self.assertEqual(len(selected), 1)
            with self.assertRaises(ValueError):
                self.check([row for row in self.rows if row is not selected[0]])
            for field, value in (
                ("class", "definitional"),
                (
                    "scope",
                    "unrestricted plaintext secrecy and unbounded tasking origin",
                ),
            ):
                rows = copy.deepcopy(self.rows)
                next(
                    row
                    for row in rows
                    if row["checker"] == "check-tasking-origin.py"
                    and row["target"] == target.name
                )[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_application_secrecy_scope_and_roster_are_explicit(self):
        driver = CHECK.INVENTORY.module("check-application-secrecy")
        for target in driver.TARGETS:
            selected = [
                row
                for row in self.rows
                if row["checker"] == "check-application-secrecy.py"
                and row["target"] == target.name
            ]
            self.assertEqual(len(selected), 1)
            with self.assertRaises(ValueError):
                self.check([row for row in self.rows if row is not selected[0]])
            for field, value in (
                ("class", "definitional"),
                (
                    "scope",
                    "unrestricted public-plaintext confidentiality and strong secrecy",
                ),
            ):
                rows = copy.deepcopy(self.rows)
                next(
                    row
                    for row in rows
                    if row["checker"] == "check-application-secrecy.py"
                    and row["target"] == target.name
                )[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)

    def test_exact_interface_strong_scope_and_roster_are_explicit(self):
        driver = CHECK.INVENTORY.module("check-exact-interface-strong")
        for target in driver.TARGETS:
            selected = [
                row
                for row in self.rows
                if row["checker"] == "check-exact-interface-strong.py"
                and row["target"] == target.name
            ]
            self.assertEqual(len(selected), 1)
            with self.assertRaises(ValueError):
                self.check([row for row in self.rows if row is not selected[0]])
            for field, value in (
                ("class", "definitional"),
                (
                    "scope",
                    "global public-plaintext equivalence for unbounded schedules and every identity",
                ),
            ):
                rows = copy.deepcopy(self.rows)
                next(
                    row
                    for row in rows
                    if row["checker"] == "check-exact-interface-strong.py"
                    and row["target"] == target.name
                )[field] = value
                with self.assertRaises(ValueError):
                    self.check(rows)


class MldsaClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = CHECK.INVENTORY.fixture_expectations(
            "check-mldsa-registration-auth"
        )
        cls.rows = [
            row
            for row in CHECK.read_rows(HERE / "verdict-classes.tsv")
            if row["checker"] == "check-mldsa-registration-auth.py"
        ]

    def check(self, rows):
        CHECK.validate(rows, self.expected)
        CHECK.validate_mldsa_scope(rows)

    def test_complete_assumed_interface_roster(self):
        self.assertEqual(len(self.rows), 14)
        self.check(self.rows)
        self.assertEqual(sum(row["class"] == "security" for row in self.rows), 2)

    def test_every_new_verdict_is_required(self):
        for index in range(len(self.rows)):
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.check(self.rows[:index] + self.rows[index + 1 :])

    def test_fixture_and_owned_key_scope_cannot_be_promoted(self):
        for index, row in enumerate(self.rows):
            if row["class"] == "security":
                continue
            changed = copy.deepcopy(self.rows)
            changed[index]["class"] = "security"
            with (
                self.subTest(target=row["target"], position=row["position"]),
                self.assertRaises(ValueError),
            ):
                self.check(changed)

    def test_provenance_cannot_be_relabelled_or_generalized(self):
        for index in (0, 1):
            for field, value in [
                ("class", "definitional"),
                ("scope", "unconditional post-quantum protocol security"),
            ]:
                changed = copy.deepcopy(self.rows)
                changed[index][field] = value
                with (
                    self.subTest(index=index, field=field),
                    self.assertRaises(ValueError),
                ):
                    self.check(changed)

    def test_assumed_primitive_and_no_enrollment_qualifications_are_pinned(self):
        for phrase in [
            "unrevealed",
            "without enrollment",
            "unforgeability",
            "no computational/QPT",
        ]:
            changed = copy.deepcopy(self.rows)
            changed[0]["scope"] = changed[0]["scope"].replace(phrase, "")
            with self.subTest(phrase=phrase), self.assertRaises(ValueError):
                self.check(changed)

    def test_response_signature_exclusion_is_pinned(self):
        changed = copy.deepcopy(self.rows)
        changed[1]["scope"] = changed[1]["scope"].replace(
            "excluding signature bytes", "including signature bytes"
        )
        with self.assertRaises(ValueError):
            self.check(changed)

    def test_control_status_formula_and_identity_are_pinned(self):
        for field, value in [
            ("status", "true"),
            ("formula_sha256", "0" * 64),
            ("target", "without-both-verifiers"),
        ]:
            changed = copy.deepcopy(self.rows)
            changed[-1][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.check(changed)


class MldsaJointClassificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.expected = CHECK.INVENTORY.fixture_expectations("check-mldsa-joint-session")
        cls.rows = [
            row
            for row in CHECK.read_rows(HERE / "verdict-classes.tsv")
            if row["checker"] == "check-mldsa-joint-session.py"
        ]

    def check(self, rows):
        CHECK.validate(rows, self.expected)
        CHECK.validate_mldsa_joint_scope(rows)

    def test_complete_bounded_joint_roster(self):
        self.assertEqual(len(self.rows), 19)
        self.check(self.rows)
        for cls, count in [
            ("security", 8),
            ("witness", 4),
            ("limitation", 2),
            ("negative-control", 5),
        ]:
            self.assertEqual(sum(row["class"] == cls for row in self.rows), count)

    def test_every_joint_verdict_is_required(self):
        for index in range(len(self.rows)):
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.check(self.rows[:index] + self.rows[index + 1 :])

    def test_owned_key_capability_and_execution_rows_cannot_be_security(self):
        for index, row in enumerate(self.rows):
            if row["class"] == "security":
                continue
            changed = copy.deepcopy(self.rows)
            changed[index]["class"] = "security"
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.check(changed)

    def test_joint_security_cannot_be_relabelled_or_generalized(self):
        for index in range(8):
            for field, value in [
                ("class", "definitional"),
                ("scope", "unconditional full-protocol quantum security"),
            ]:
                changed = copy.deepcopy(self.rows)
                changed[index][field] = value
                with (
                    self.subTest(index=index, field=field),
                    self.assertRaises(ValueError),
                ):
                    self.check(changed)

    def test_assumptions_and_protected_payload_policy_are_mandatory(self):
        for phrase in [
            "unrevealed",
            "without enrollment",
            "only after admission",
            "unforgeability",
            "ML-KEM public-key binding assumed beyond generic IND-CCA",
            "public Ed25519/X25519 recovery",
            "no computational/QPT",
            "public per-invocation assigned labels abstract concrete counter allocation order",
        ]:
            changed = copy.deepcopy(self.rows)
            changed[0]["scope"] = changed[0]["scope"].replace(phrase, "")
            with self.subTest(phrase=phrase), self.assertRaises(ValueError):
                self.check(changed)

    def test_directional_bounds_and_actual_replay_identity_are_mandatory(self):
        for old, new in [
            ("two generic Server attempts", "arbitrary Server attempts"),
            ("one server record sequence2", "all server records"),
            ("one receive attempt per endpoint", "arbitrary receive schedules"),
            (
                "Ed identity plus one-time key, excluding ML keys",
                "Ed identity plus ML key",
            ),
        ]:
            changed = copy.deepcopy(self.rows)
            changed[0]["scope"] = changed[0]["scope"].replace(old, new)
            with self.subTest(old=old), self.assertRaises(ValueError):
                self.check(changed)

    def test_replay_witness_is_not_an_injective_replay_theorem(self):
        changed = copy.deepcopy(self.rows)
        changed[12]["scope"] = changed[12]["scope"].replace(
            "passive private observation matches insertion and rejection of the same actual registration ID in distinct Server invocations, with the rejecting invocation consuming the matching token released after insertion; no arbitrary replay-schedule theorem",
            "arbitrary registration and record replay is prevented injectively",
        )
        with self.assertRaises(ValueError):
            self.check(changed)

    def test_quantum_library_and_response_signature_exclusion_are_mandatory(self):
        for index, old, new in [
            (0, "quantum-capabilities.pvl", ""),
            (1, "excluding ML signature bytes", "including ML signature bytes"),
        ]:
            changed = copy.deepcopy(self.rows)
            changed[index]["scope"] = changed[index]["scope"].replace(old, new)
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.check(changed)

    def test_control_formula_status_and_identity_are_exact(self):
        for field, value in [
            ("status", "unknown"),
            ("formula_sha256", "0" * 64),
            ("target", "without-both-verifiers"),
        ]:
            changed = copy.deepcopy(self.rows)
            changed[-1][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.check(changed)


if __name__ == "__main__":
    unittest.main()
