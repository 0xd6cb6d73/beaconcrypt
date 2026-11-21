#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the actual fixed-two seal join request lift."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("lift_adapter_seal_join_requests.py")
SPEC = importlib.util.spec_from_file_location("seal_join_lift", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
LIFT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LIFT)


class SealJoinLiftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (LIFT.ROOT / LIFT.SOURCE).read_bytes()

    def rejects(self, before, after, message="source seal join body changed"):
        self.assertIn(before, self.source)
        with self.assertRaisesRegex(ValueError, message):
            LIFT.transform(self.source.replace(before, after, 1))

    def test_reviewed_source_and_output_provenance(self):
        output = LIFT.transform(self.source).decode()
        self.assertEqual(output.count("def join\n"), 1)
        self.assertIn(hashlib.sha256(self.source).hexdigest(), output)
        self.assertIn(hashlib.sha256(SCRIPT.read_bytes()).hexdigest(), output)
        self.assertIn("set_option warningAsError true", output)
        self.assertIn("[Monad m] [LiftRust m] [Operations E m]", output)
        self.assertIn("Operations.reserve (E := E) output val1", output)

    def test_exact_leaf_multiplicities(self):
        output = LIFT.transform(self.source).decode()
        expected = {
            "index": 2,
            "len": 2,
            "checkedAdd": 2,
            "branch": 3,
            "fromResidual": 3,
            "new": 1,
            "resultOk": 1,
            "extend": 2,
        }
        for name, count in expected.items():
            self.assertEqual(
                len(re.findall(r"\bLifted\." + name + r"\b", output)), count
            )
        self.assertEqual(output.count("Operations.reserve (E := E)"), 1)
        self.assertNotIn("alloc.vec.Vec.try_reserve_exact", output)

    def test_initial_checked_length(self):
        self.rejects(b"checked_add 0#usize i", b"checked_add i i")

    def test_accumulated_checked_length(self):
        self.rejects(b"checked_add val i1", b"checked_add 0#usize i1")

    def test_part_index_order(self):
        self.rejects(
            b"Array.index_usize parts 1#usize", b"Array.index_usize parts 0#usize"
        )

    def test_reservation_uses_checked_total(self):
        self.rejects(b"try_reserve_exact output val1", b"try_reserve_exact output val")

    def test_extra_reservation(self):
        self.rejects(
            "let (r, output1) ← alloc.vec.Vec.try_reserve_exact output val1".encode(),
            "let (r, output1) ← alloc.vec.Vec.try_reserve_exact output val1\n      let _ ← alloc.vec.Vec.try_reserve_exact output1 val1".encode(),
        )

    def test_missing_reservation(self):
        self.rejects(
            b"alloc.vec.Vec.try_reserve_exact output val1",
            b"ok (core.result.Result.Ok (), output)",
        )

    def test_reservation_error_conversion(self):
        self.rejects(b"core.result.Result.ok r", b"ok (core.option.Option.Some ())")

    def test_reservation_error_branch(self):
        self.rejects(
            b"core.ops.control_flow.ControlFlow.Break residual",
            b"core.ops.control_flow.ControlFlow.Break ignored",
        )

    def test_first_extend_uses_reserved_vector(self):
        self.rejects(
            b"core.U8.Insts.CoreCloneClone output1\n            s",
            b"core.U8.Insts.CoreCloneClone output\n            s",
        )

    def test_second_extend_uses_first_returned_vector(self):
        self.rejects(
            b"core.U8.Insts.CoreCloneClone output2\n            s1",
            b"core.U8.Insts.CoreCloneClone output1\n            s1",
        )

    def test_extend_part_order(self):
        self.rejects(
            b"core.U8.Insts.CoreCloneClone output1\n            s",
            b"core.U8.Insts.CoreCloneClone output1\n            s1",
        )

    def test_success_keeps_final_vector(self):
        self.rejects(
            b"ok (core.option.Option.Some output3)",
            b"ok (core.option.Option.Some output1)",
        )

    def test_missing_declaration(self):
        self.rejects(
            b"def ratchet._proof_join_seal_two\n",
            b"def ratchet.changed\n",
            "declaration roster changed",
        )

    def test_extra_declaration(self):
        with self.assertRaisesRegex(ValueError, "declaration roster changed"):
            LIFT.transform(self.source + b"\ndef unexpected : Nat := 0\n")

    def test_duplicate_declaration(self):
        with self.assertRaisesRegex(ValueError, "declaration roster changed"):
            LIFT.transform(self.source + b"\ndef ratchet._proof_join_seal_two\n")

    def test_whole_source_header(self):
        self.rejects(
            b"set_option warningAsError true",
            b"set_option warningAsError false",
            "whole file changed",
        )

    def test_unchecked_source_obligation(self):
        with self.assertRaisesRegex(ValueError, "unchecked source file"):
            LIFT.transform(self.source + b"\naxiom fabricated : True\n")

    def test_leaf_multiplicity(self):
        wrong = list(LIFT.REPLACEMENTS)
        before, after, count = wrong[1]
        wrong[1] = before, after, count + 1
        with patch.object(LIFT, "REPLACEMENTS", wrong):
            with self.assertRaisesRegex(ValueError, "leaf multiplicity changed"):
                LIFT.transform(self.source)

    def test_unlifted_standard_operation(self):
        wrong = [
            item for item in LIFT.REPLACEMENTS if item[0] != "core.result.Result.ok"
        ]
        with patch.object(LIFT, "REPLACEMENTS", wrong):
            with self.assertRaisesRegex(ValueError, "unlifted seal join operation"):
                LIFT.transform(self.source)

    def test_residual_multiplicity(self):
        with patch.object(LIFT, "RESIDUAL", re.compile("never_matches")):
            with self.assertRaisesRegex(ValueError, "residual branch roster changed"):
                LIFT.transform(self.source)

    def test_complete_generated_output_is_checked_without_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "lift.lean"
            malformed = LIFT.transform(self.source) + b"\naxiom fabricated : True\n"
            output.write_bytes(malformed)
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "--check", "--output", str(output)],
                capture_output=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), malformed)

    def test_output_operand_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "lift.lean"
            malformed = LIFT.transform(self.source).replace(
                b"Lifted.checkedAdd val i1", b"Lifted.checkedAdd i1 i1"
            )
            self.assertNotEqual(malformed, LIFT.transform(self.source))
            output.write_bytes(malformed)
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "--check", "--output", str(output)],
                capture_output=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), malformed)

    def test_combined_modes_keep_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "unchanged.lean"
            output.write_bytes(b"sentinel\n")
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    "--write",
                    "--check",
                    "--output",
                    str(output),
                ],
                capture_output=True,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), b"sentinel\n")


if __name__ == "__main__":
    unittest.main()
