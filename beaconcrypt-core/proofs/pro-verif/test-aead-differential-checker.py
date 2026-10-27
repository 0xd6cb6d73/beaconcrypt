#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for the open CTX model and strict result classifier."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "ctx_differential_checker", Path(__file__).with_name("check-aead-differential.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class DifferentialChecks(unittest.TestCase):
    def test_manifest_has_no_security_claim(self):
        CHECKER.validate_targets()
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS], ["definitional", "differential"]
        )

    def mutate(self, filename, old, new):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for name in (*CHECKER.LIBRARIES, *(t.query for t in CHECKER.TARGETS)):
                shutil.copy(CHECKER.HERE / name, directory / name)
            path = directory / filename
            text = path.read_text()
            self.assertEqual(text.count(old), 1)
            path.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(directory=directory)

    def test_missing_right_context_check(self):
        self.mutate(
            "fs-aead-differential.pvl",
            "  if commitment = ctx_commitment(right_key, right_nonce, right_ad, tag, frame_sequence, sender) then\n",
            "",
        )

    def test_closed_honest_only_inputs(self):
        self.mutate(
            "fs-aead-differential.pvl", "free c: channel.", "free c: channel [private]."
        )

    def test_bypass_second_open(self):
        self.mutate(
            "fs-aead-differential.pvl",
            "let FsAeadWithoutCtx() =",
            "let FsAeadWithoutCtx() = event FsAeadDifferentContextsOpened();",
        )

    def test_changed_weak_opening(self):
        self.mutate(
            "aead-commitment-negative-control.pvl",
            ") = right_plaintext.",
            ") = left_plaintext.",
        )

    def test_query_selects_wrong_process(self):
        self.mutate(
            "fs-aead-differential-ctx.pv",
            "process FsAeadWithCtx()",
            "process FsAeadWithoutCtx()",
        )

    def test_classification_cannot_be_promoted(self):
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(
                (replace(CHECKER.TARGETS[0], cls="security"), CHECKER.TARGETS[1])
            )

    def test_manifest_cannot_drop_control(self):
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(CHECKER.TARGETS[:1])

    def test_exact_result_and_trace_requirements(self):
        for target in CHECKER.TARGETS:
            trace = "A trace has been found.\n" * target.expected_traces()
            output = f"RESULT {target.result}\n{trace}Verification summary:\nQuery {target.result}\n"
            CHECKER.FS.check_output(output, target)
            for bad in (
                output.replace("RESULT ", ""),
                output.replace("Verification summary:", ""),
                output.replace(" is true.", " cannot be proved.").replace(
                    " is false.", " cannot be proved."
                ),
                output + "Warning: unexpectedly broadened model\n",
                (
                    output.replace("A trace has been found.\n", "")
                    if trace
                    else output.replace(
                        "Verification summary:",
                        "A trace has been found.\nVerification summary:",
                    )
                ),
            ):
                with self.assertRaises(ValueError):
                    CHECKER.FS.check_output(bad, target)


if __name__ == "__main__":
    unittest.main()
