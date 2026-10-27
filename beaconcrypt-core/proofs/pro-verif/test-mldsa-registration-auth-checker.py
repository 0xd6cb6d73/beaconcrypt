#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject changed assumed-interface formulas, evidence and reviewed models."""

import importlib.util
from pathlib import Path
import re
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "mldsa_checker", HERE / "check-mldsa-registration-auth.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def output(queries=CHECKER.PRIMARY, verdicts=CHECKER.VERDICTS):
    lines = [q + " is " + v + "." for q, v in zip(queries, verdicts, strict=True)]
    return "\n".join(
        [
            *("RESULT " + line for line in lines),
            *("A trace has been found." for _ in range(verdicts.count("false"))),
            "Verification summary:",
            *("Query " + line for line in lines),
        ]
    )


class ExactMldsaGate(unittest.TestCase):
    def setUp(self):
        self.text = output()

    def check(self, text):
        CHECKER.check_output(
            text, CHECKER.PRIMARY, CHECKER.VERDICTS, CHECKER.VERDICTS.count("false")
        )

    def test_complete_paired_evidence(self):
        self.check(self.text)

    def test_alpha_suffixes_preserve_formula(self):
        renamed = re.sub(
            r"\b(agent_ml|server_ml|init_hash|classical_init|response)\b",
            r"\1_937",
            self.text,
        )
        self.check(renamed)

    def test_repeated_variable_cannot_split(self):
        with self.assertRaises(ValueError):
            self.check(
                self.text.replace(
                    "MldsaInitSigned(agent_ml,", "MldsaInitSigned(agent_ml_3,"
                )
            )

    def test_distinct_variables_cannot_merge(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("agent_ml,server_ml", "agent_ml,agent_ml"))

    def test_event_and_bound_hash_cannot_change(self):
        for changed in [
            self.text.replace("MldsaResponseSigned", "MldsaResponseAccepted"),
            self.text.replace("init_hash", "unbound_hash"),
        ]:
            with self.subTest(changed=changed[:130]), self.assertRaises(ValueError):
                self.check(changed)

    def test_missing_or_duplicate_primary_rejected(self):
        first, rest = self.text.split("\n", 1)
        for changed in [rest, first + "\n" + self.text]:
            with self.subTest(changed=changed[:130]), self.assertRaises(ValueError):
                self.check(changed)

    def test_summary_is_required_and_unique(self):
        for changed in [
            self.text.replace("Verification summary:", ""),
            self.text + "\nVerification summary:",
        ]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                self.check(changed)

    def test_summary_and_primary_must_both_have_exact_verdict(self):
        before, after = self.text.split("Verification summary:")
        for changed in [
            before.replace(" is true.", " is false.", 1)
            + "Verification summary:"
            + after,
            before
            + "Verification summary:"
            + after.replace(" is true.", " is false.", 1),
        ]:
            with self.subTest(changed=changed[:130]), self.assertRaises(ValueError):
                self.check(changed)

    def test_unknown_cannot_pass(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace(" is true.", " cannot be proved.", 1))

    def test_witness_needs_reconstructed_trace(self):
        for changed in [
            self.text.replace("A trace has been found.", "", 1),
            "A trace has been found.\n" + self.text,
            self.text.replace(
                "A trace has been found.",
                "A trace has been found, assuming a hypothesis:",
                1,
            ),
        ]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                self.check(changed)

    def test_trace_after_summary_is_rejected(self):
        changed = self.text.replace("A trace has been found.\n", "", 1)
        with self.assertRaises(ValueError):
            self.check(changed + "\nA trace has been found.")

    def test_warning_or_error_is_not_evidence(self):
        for notice in [
            "Warning: modified theory",
            "Error: invalid model",
            "Fatal: failure",
            "Timeout: expired",
        ]:
            with self.subTest(notice=notice), self.assertRaises(ValueError):
                self.check(notice + "\n" + self.text)

    def test_control_requires_exact_false_formula_and_trace(self):
        query = (CHECKER.PRIMARY[0],)
        text = output(query, ("false",))
        CHECKER.check_output(text, query, ("false",), 1)
        for changed in [
            text.replace(" is false.", " is true."),
            text.replace("A trace has been found.", ""),
        ]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                CHECKER.check_output(changed, query, ("false",), 1)

    def test_reviewed_token_hashes_are_current(self):
        CHECKER.validate_models()

    def test_removed_verifier_or_transcript_field_requires_review(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            for name in CHECKER.MODEL_FILES:
                (directory / name).write_text((HERE / name).read_text())
            model = directory / "mldsa-registration-auth.pvl"
            original = model.read_text()
            for _, _, old, new in CHECKER.CONTROLS:
                model.write_text(CHECKER.exact_replace(original, old, new))
                with self.assertRaises(ValueError):
                    CHECKER.validate_models(directory)
            model.write_text(original)
            auth = directory / "mldsa-auth.pvl"
            auth.write_text(
                auth.read_text().replace(
                    "mldsa_length_prefixed(raw_ctu)", "mldsa_zero()"
                )
            )
            with self.assertRaises(ValueError):
                CHECKER.validate_models(directory)

    def test_control_anchor_must_be_unique(self):
        for text in ["absent", "anchor anchor"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                CHECKER.exact_replace(text, "anchor", "replacement")

    def test_each_control_preserves_other_verifier(self):
        original = (HERE / "mldsa-registration-auth.pvl").read_text()
        for name, _, old, new in CHECKER.CONTROLS:
            changed = CHECKER.exact_replace(original, old, new)
            self.assertNotEqual(original, changed)
            for other, _, anchor, _ in CHECKER.CONTROLS:
                self.assertEqual(changed.count(anchor), int(other != name))


if __name__ == "__main__":
    unittest.main()
