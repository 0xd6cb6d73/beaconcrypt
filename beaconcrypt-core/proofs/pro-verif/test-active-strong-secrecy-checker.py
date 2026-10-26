#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail closed on changed source derivatives, test eligibility and verdicts."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "active_checker", Path(__file__).with_name("check-active-strong-secrecy.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ActiveTests(unittest.TestCase):
    def test_manifest(self):
        CHECKER.validate_targets()
        self.assertEqual(len(CHECKER.TARGETS), 6)
        self.assertEqual(sum(not t.control for t in CHECKER.TARGETS), 2)
        self.assertEqual({t.bound for t in CHECKER.TARGETS}, {1})

    def mutate(self, filename, old, new):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for pattern in ("fs-strong-*", "fs-records-*.pvl"):
                for path in CHECKER.HERE.glob(pattern):
                    shutil.copy(path, directory / path.name)
            target = directory / filename
            source = target.read_text()
            self.assertIn(old, source)
            target.write_text(source.replace(old, new, 1))
            with self.assertRaises(ValueError):
                CHECKER.check_derivatives(directory)

    def test_changed_reply_and_source_boundaries(self):
        changes = (
            (
                "fs-strong-b2s-receive.pvl",
                "out(c, fs_strong_reply(call_label, frame, true));",
                "",
            ),
            (
                "fs-strong-b2s-receive.pvl",
                "out(c, fs_strong_reply(call_label, frame, false));",
                "",
            ),
            (
                "fs-strong-s2b-receive.pvl",
                "out(c,fs_strong_reply(call_label, frame, true));",
                "",
            ),
            (
                "fs-strong-s2b-receive.pvl",
                "out(c,fs_strong_reply(call_label, frame, false));",
                "",
            ),
            (
                "fs-strong-b2s.pvl",
                "fs_strong_reply(call_label, response, false)",
                "fs_strong_reply(call_label, response, true)",
            ),
            (
                "fs-strong-s2b.pvl",
                "fs_strong_reply(call_label, response, false)",
                "fs_strong_reply(call_label, response, true)",
            ),
            ("fs-strong-b2s.pvl", "if frame_t = 1 then", "if frame_t = 2 then"),
            ("fs-strong-s2b.pvl", "if frame_t = 1 then", "if frame_t = 2 then"),
            ("fs-strong-b2s.pvl", "fs_root_dh2(dh2, dh3)", "fs_root_dh2(dh3, dh3)"),
            ("fs-strong-s2b.pvl", "dh4,", "dh3,"),
            ("fs-strong-b2s-receive.pvl", "fs_b2s_failed_r(r, 1)", "1"),
            ("fs-strong-s2b-receive.pvl", "fs_s2b_failed_r(r, 2)", "2"),
        )
        for change in changes:
            with self.subTest(change=change):
                self.mutate(*change)

    def test_changed_eligibility_and_challenges(self):
        changes = (
            (
                "fs-strong-b2s-sends.pvl",
                "server_identity = ed_public(SERVER_IDENTITY_SECRET)",
                "true",
            ),
            ("fs-strong-b2s-sends.pvl", "choice[left_2, right_2]", "left_2"),
            (
                "fs-strong-s2b-taskings.pvl",
                "in(fs_strong_partner,(=assigned_key_id,=root));",
                "",
            ),
            (
                "fs-strong-s2b.pvl",
                "out(fs_strong_partner,(assigned_key_id,root))",
                "out(fs_strong_partner,(assigned_key_id,associated_data))",
            ),
            ("fs-strong-s2b-interface.pvl", "[private]", ""),
            ("fs-strong-s2b-taskings.pvl", "choice[left,right]", "left"),
            ("fs-strong-b2s.pv", "FsRecordsB2sMainAnyPin", "FsRecordsB2sMain"),
            ("fs-strong-common.pvl", "x25519_public(y)", "x25519_public(x)"),
        )
        for change in changes:
            with self.subTest(change=change):
                self.mutate(*change)

    def test_changed_control(self):
        self.mutate("fs-strong-control-b2s-leak.pvl", "out(c, record_1);", "")
        self.mutate("fs-strong-control-s2b-leak.pvl", "out(c, tasking_2);", "")

    def test_control_secret_and_query_are_fixed(self):
        for direction in ("b2s", "s2b"):
            self.mutate(f"fs-strong-control-{direction}.pv", " && attacker(m)", "")
            for kind in ("leak", "ungated"):
                self.mutate(
                    f"fs-strong-control-{direction}-{kind}.pvl",
                    "new fs_strong_control_secret: bitstring;",
                    "let fs_strong_control_secret = left in",
                )
                source = (
                    CHECKER.HERE / f"fs-strong-control-{direction}-{kind}.pvl"
                ).read_text()
                self.assertNotIn("choice[", source)

    def test_later_finish_cannot_continue_or_partner(self):
        source = (CHECKER.HERE / "fs-strong-s2b.pvl").read_text()
        self.assertNotIn("fs_strong_s2b_later", source)
        self.assertNotIn("FsBeaconFinishOpenedLater", source)
        self.assertIn("if frame_t = 1 then", source)

    def test_call_labels_are_retained(self):
        for direction in ("b2s", "s2b"):
            self.mutate(
                f"fs-strong-{direction}-receive.pvl",
                "fs_strong_reply(call_label, frame,",
                "fs_strong_reply(frame, frame,",
            )
            self.mutate(
                f"fs-strong-{direction}.pvl",
                "fs_strong_reply(call_label, response,",
                "fs_strong_reply(response, response,",
            )
            self.mutate(
                f"fs-strong-{direction}-receive.pvl",
                "(call_label: bitstring, frame: bitstring)",
                "frame: bitstring",
            )

    def test_baseline_source_change(self):
        self.mutate("fs-records-b2s.pvl", "if frame_t = 1 then", "if frame_t = 2 then")
        self.mutate(
            "fs-records-s2b.pvl",
            "later_plaintext_2 = open_frame",
            "later_plaintext_2 = wrong_open_frame",
        )
        self.mutate("fs-records-s2b-gate.pvl", ") = 0.", ") = out(c, later_plaintext).")

    @staticmethod
    def receipt(target):
        trace = "A trace has been found.\n" if target.control else ""
        return (
            trace
            + "RESULT "
            + target.result
            + "\nVerification summary:\n"
            + ("Query " if target.control else "")
            + target.result
            + "\n"
        )

    def test_exact_equivalence_receipts(self):
        for target in CHECKER.TARGETS:
            CHECKER.check_output(self.receipt(target), target)

    def test_unknown_unconfirmed_and_extra_results(self):
        target = CHECKER.TARGETS[0]
        valid = self.receipt(target)
        for bad in (
            valid.replace("is true.", "cannot be proved."),
            valid.replace("is true.", "is false."),
            valid.replace("Observational equivalence", "Diff-equivalence"),
            valid.replace("Verification summary:", ""),
            valid + "Verification summary:\n",
            "A trace has been found.\n" + valid,
            "I could not confirm the trace.\n" + valid,
            "Warning: axiom omitted\n" + valid,
            "RESULT Observational equivalence is true.\n" + valid,
        ):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                CHECKER.check_output(bad, target)

    def test_control_requires_false_and_confirmed_trace(self):
        target = next(t for t in CHECKER.TARGETS if t.control)
        valid = self.receipt(target)
        for bad in (
            valid.replace("A trace has been found.\n", ""),
            valid.replace(
                "A trace has been found.",
                "A trace has been found, assuming the following hypothesis:",
            ),
            valid.replace("is false.", "cannot be proved."),
            "A trace has been found.\n" + valid,
        ):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                CHECKER.check_output(bad, target)

    def test_manifest_is_not_weakened(self):
        original = CHECKER.TARGETS[0]
        for changed in (
            replace(original, bound=0),
            replace(original, bound=2),
            replace(original, control="leak"),
            replace(original, direction="unknown"),
        ):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets((changed, *CHECKER.TARGETS[1:]))
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(CHECKER.TARGETS[:-1])


if __name__ == "__main__":
    unittest.main()
