#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the actual fixed-three-part writer request lift."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("lift_adapter_record_helper_requests.py")
SPEC = importlib.util.spec_from_file_location("record_helper_lift", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
LIFT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LIFT)


class RecordHelperLiftTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (LIFT.ROOT / LIFT.SOURCE).read_bytes()

    def rejects(self, before, after, message="source record helper changed"):
        self.assertIn(before, self.source)
        with self.assertRaisesRegex(ValueError, message):
            LIFT.transform(self.source.replace(before, after, 1))

    def test_actual_reviewed_source_and_provenance(self):
        output = LIFT.transform(self.source).decode()
        self.assertIn("def raw\n", output)
        self.assertIn("def frame\n", output)
        self.assertIn(hashlib.sha256(self.source).hexdigest(), output)
        self.assertIn(hashlib.sha256(SCRIPT.read_bytes()).hexdigest(), output)
        self.assertIn("set_option warningAsError true", output)
        self.assertNotIn("alloc.vec.Vec.try_reserve_exact", output)
        self.assertIn("Operations.reserve (E := E) output val2", output)
        self.assertIn("Lifted.writeFrame (E := E) val3 sequence sender parts", output)

    def test_raw_length_check_cannot_be_removed(self):
        self.rejects(b"checked_add 0#usize i", b"checked_add i i")

    def test_part_call_order_cannot_change(self):
        self.rejects(
            b"Array.index_usize parts 1#usize", b"Array.index_usize parts 2#usize"
        )

    def test_extra_reservation_cannot_be_added(self):
        self.rejects(
            b"let (r, output1) \xe2\x86\x90 alloc.vec.Vec.try_reserve_exact output val2",
            b"let (r, output1) \xe2\x86\x90 alloc.vec.Vec.try_reserve_exact output val2\n"
            b"        let _ \xe2\x86\x90 alloc.vec.Vec.try_reserve_exact output1 val2",
        )

    def test_success_branch_cannot_be_replaced(self):
        self.rejects(
            b"ok (core.option.Option.Some output4)",
            b"ok (core.option.Option.None : core.option.Option (alloc.vec.Vec Std.U8))",
        )

    def test_reservation_failure_branch_cannot_be_omitted(self):
        self.rejects(
            b"        | core.ops.control_flow.ControlFlow.Break residual =>\n"
            b"          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual\n"
            b"            (alloc.vec.Vec Std.U8) residual",
            b"        | core.ops.control_flow.ControlFlow.Break _ =>\n"
            b"          ok (core.option.Option.Some output1)",
        )

    def test_frame_capacity_call_cannot_change(self):
        self.rejects(
            b"encoded_frame_len sequence sender val2",
            b"encoded_frame_len sender sequence val2",
        )

    def test_missing_declaration_is_rejected(self):
        self.rejects(
            b"def wire._proof_encode_frame_three\n",
            b"def wire.changed_frame\n",
            "declaration roster changed",
        )

    def test_duplicate_declaration_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "declaration roster changed"):
            LIFT.transform(self.source + b"\ndef ratchet._proof_join_record_three\n")

    def test_unlifted_std_operation_is_rejected(self):
        raw = [
            item
            for item in LIFT.REPLACEMENTS["raw"]
            if item[0] != "core.result.Result.ok"
        ]
        with patch.dict(LIFT.REPLACEMENTS, {"raw": raw}):
            with self.assertRaisesRegex(ValueError, "unlifted record helper operation"):
                LIFT.transform(self.source)

    def test_leaf_multiplicity_is_checked(self):
        wrong = list(LIFT.REPLACEMENTS["raw"])
        before, after, count = wrong[0]
        wrong[0] = before, after, count + 1
        with patch.dict(LIFT.REPLACEMENTS, {"raw": wrong}):
            with self.assertRaisesRegex(ValueError, "leaf multiplicity changed"):
                LIFT.transform(self.source)

    def test_unchecked_source_declaration_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unchecked source file"):
            LIFT.transform(self.source + b"\naxiom fabricated : True\n")

    def test_output_drift_and_appended_axiom_are_rejected_without_writing(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "lift.lean"
            malformed = LIFT.transform(self.source) + b"\naxiom fabricated : True\n"
            output.write_bytes(malformed)
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "--check", "--output", str(output)],
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), malformed)

    def test_combined_modes_cannot_mutate_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "unchanged.lean"
            output.write_bytes(b"sentinel\n")
            result = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    "--check",
                    "--write",
                    "--output",
                    str(output),
                ],
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), b"sentinel\n")


if __name__ == "__main__":
    unittest.main()
