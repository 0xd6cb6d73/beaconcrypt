#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject misleading or incomplete free-schedule (fs) ProVerif receipts."""

import contextlib
import dataclasses
import importlib.util
import io
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "free_schedule_checker", Path(__file__).with_name("check-free-schedule.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def target(name):
    return next(target for target in CHECKER.TARGETS if target.name == name)


def receipt(target, traces=None):
    traces = target.expected_traces() if traces is None else traces
    primary = "".join(f"RESULT {line}\n" for line in target.results)
    return (
        "Process 0 (that is, the initial process):\n"
        + "A trace has been found.\n" * traces
        + primary
        + "--------------------------------------------------------------\n"
        + "Verification summary:\n\n"
        + f"Query {target.results[0]}\n\n"
        + "--------------------------------------------------------------\n"
    )


class ReceiptTests(unittest.TestCase):
    def test_every_target_accepts_its_exact_receipt(self):
        for each in CHECKER.TARGETS:
            CHECKER.check_output(receipt(each), each)

    def test_security_true_is_not_false(self):
        each = target("A1")
        with self.assertRaises(ValueError):
            CHECKER.check_output(receipt(each).replace("is true.", "is false."), each)

    def test_cannot_be_proved_is_rejected(self):
        for name in ("A1", "R3", "R4", "C-NOCHECK"):
            each = target(name)
            text = (
                receipt(each)
                .replace(" is true.", " cannot be proved.")
                .replace(" is false.", " cannot be proved.")
            )
            with self.assertRaises(ValueError):
                CHECKER.check_output(text, each)

    def test_unconfirmed_trace_is_rejected(self):
        each = target("R4")
        text = receipt(each).replace(
            "A trace has been found.\n",
            "A trace has been found.\nI could not confirm that the previous trace falsifies the query.\n",
        )
        with self.assertRaises(ValueError):
            CHECKER.check_output(text, each)

    def test_unknown_and_inconclusive_are_rejected(self):
        each = target("R1")
        for verdict in (" is unknown.", " is inconclusive."):
            with self.assertRaises(ValueError):
                CHECKER.check_output(receipt(each).replace(" is true.", verdict), each)

    def test_missing_primary(self):
        each = target("R1")
        text = receipt(each).replace("RESULT " + each.results[0] + "\n", "")
        with self.assertRaises(ValueError):
            CHECKER.check_output(text, each)

    def test_extra_primary(self):
        each = target("R1")
        with self.assertRaises(ValueError):
            CHECKER.check_output(
                "RESULT " + each.results[0] + "\n" + receipt(each), each
            )

    def test_changed_event_argument(self):
        each = target("A2")
        with self.assertRaises(ValueError):
            CHECKER.check_output(receipt(each).replace("s2,", "s,"), each)

    def test_summary_disagrees(self):
        each = target("R1'")
        text = receipt(each).replace(
            "Query " + each.results[0], "Query " + each.results[0][:-9] + " is false."
        )
        with self.assertRaises(ValueError):
            CHECKER.check_output(text, each)

    def test_missing_summary(self):
        each = target("R2")
        with self.assertRaises(ValueError):
            CHECKER.check_output(
                receipt(each).replace("Verification summary:", ""), each
            )

    def test_false_result_needs_a_trace(self):
        for name in ("R3", "R4", "R5", "W1", "C-NOCHECK", "C-UKS"):
            each = target(name)
            with self.assertRaises(ValueError):
                CHECKER.check_output(receipt(each, traces=0), each)
            with self.assertRaises(ValueError):
                CHECKER.check_output(receipt(each, traces=2), each)

    def test_true_result_has_no_trace(self):
        each = target("S3-beacon")
        with self.assertRaises(ValueError):
            CHECKER.check_output(receipt(each, traces=1), each)

    def test_injective_control_needs_both_lines(self):
        each = target("C-UKS")
        self.assertEqual(len(each.results), 2)
        text = receipt(each).replace("RESULT " + each.results[1] + "\n", "")
        with self.assertRaises(ValueError):
            CHECKER.check_output(text, each)
        text = receipt(each).replace(
            each.results[1], each.results[1].replace("is false.)", "is true.)")
        )
        with self.assertRaises(ValueError):
            CHECKER.check_output(text, each)

    def test_errors_and_warnings_are_rejected(self):
        each = target("W2")
        for line in (
            "Error: something\n",
            "Warning: something\n",
            'File "x.pvl", line 3, characters 1-2:\nWarning: identifier x rebound.\n',
            "  Warning: indented\n",
            "Another warning: a new class\n",
            "Termination  warning: not the ProVerif prefix\n",
        ):
            with self.assertRaises(ValueError):
                CHECKER.check_output(line + receipt(each), each)

    def test_termination_warnings_are_accepted(self):
        lines = (
            "Termination warning: attacker(x) && mess(c[],x) -> attacker(app_prefix)\n"
            "Selecting 2\n"
            "Termination warning: Selecting an hypothesis matching the conclusion.\n"
            "In case of non-termination, try a noselect declaration implying the following one:\n"
        )
        for name in ("s2b-A2", "s2b-S1", "s2b-C5c", "R4", "b2s-C2", "b2s-S2"):
            each = target(name)
            CHECKER.check_output(lines + receipt(each), each)

    def test_record_targets_need_their_exact_lines(self):
        for name in (
            "s2b-C1",
            "s2b-C5b",
            "s2b-C-RETAIN-C1",
            "s2b-C-NOGATE",
            "b2s-C2",
            "b2s-C5c",
            "b2s-UKSr",
            "b2s-C-UKS",
        ):
            each = target(name)
            CHECKER.check_output(receipt(each), each)
            if each.scenario == CHECKER.RECORDS_B2S:
                text = receipt(each).replace("beacon_to_server", "server_to_beacon")
            else:
                text = receipt(each).replace("root_2", "root_1")
            self.assertNotEqual(text, receipt(each))
            with self.assertRaises(ValueError):
                CHECKER.check_output(text, each)

    def test_record_controls_need_both_lines(self):
        for name in ("s2b-C-RETAIN-C1", "s2b-C-NOGATE"):
            each = target(name)
            self.assertEqual(len(each.results), 2)
            text = receipt(each).replace("RESULT " + each.results[1] + "\n", "")
            with self.assertRaises(ValueError):
                CHECKER.check_output(text, each)

    def test_b2s_controls_reuse_their_targets(self):
        # Each b2s control runs the query of the claim it controls, with the opposite
        # verdict and a trace.
        for control, claim in (
            ("b2s-C-UKS", "b2s-UKSr"),
            ("b2s-C-RETAIN", "b2s-C3"),
            ("b2s-C-STALE", "b2s-C3"),
        ):
            each, security = target(control), target(claim)
            self.assertEqual(each.query, security.query)
            self.assertEqual(
                each.results, (security.results[0][: -len("true.")] + "false.",)
            )
            self.assertEqual(each.expected_traces(), 1)

    def test_inverted_control_is_true_without_a_trace(self):
        each = target("s2b-C-FAILMUT")
        self.assertTrue(each.inverted)
        self.assertEqual(each.expected_traces(), 0)
        CHECKER.check_output(receipt(each), each)
        with self.assertRaises(ValueError):
            CHECKER.check_output(receipt(each, traces=1), each)
        with self.assertRaises(ValueError):
            CHECKER.check_output(receipt(each).replace("is true.", "is false."), each)
        witness = target("s2b-C5b")
        self.assertEqual(witness.query, each.query)
        self.assertEqual(
            witness.results[0][: -len("is false.")], each.results[0][: -len("is true.")]
        )


class ManifestTests(unittest.TestCase):
    def test_manifest_is_consistent(self):
        CHECKER.validate_targets()

    def test_classes_and_bounds(self):
        counts = {scenario: {} for scenario in CHECKER.SCENARIOS}
        for each in CHECKER.TARGETS:
            classes = counts[each.scenario]
            classes[each.cls] = classes.get(each.cls, 0) + 1
            if each.cls == "security":
                self.assertEqual(each.bound, 3)
        self.assertEqual(
            counts[CHECKER.REGISTRATION],
            {
                "security": 6,
                "definitional": 1,
                "witness": 5,
                "control": 2,
                "limitation": 1,
            },
        )
        self.assertEqual(
            counts[CHECKER.RECORDS_S2B],
            {
                "security": 6,
                "witness": 5,
                "control": 5,
            },
        )
        self.assertEqual(
            counts[CHECKER.RECORDS_B2S],
            {
                "security": 8,
                "definitional": 1,
                "witness": 6,
                "control": 3,
            },
        )

    def test_security_claims_count_each_query_once(self):
        # Evidence is counted per claim, one per scenario and query file: b2s C2 runs as
        # two security targets with one query file and counts once.
        claims = CHECKER.security_claims(CHECKER.TARGETS)
        per_scenario = {
            scenario: sum(1 for each in claims if each[0] == scenario)
            for scenario in CHECKER.SCENARIOS
        }
        self.assertEqual(
            per_scenario,
            {
                CHECKER.REGISTRATION: 6,
                CHECKER.RECORDS_S2B: 6,
                CHECKER.RECORDS_B2S: 7,
            },
        )
        self.assertEqual(
            CHECKER.security_claims((target("b2s-C2"), target("b2s-C2-chosen-fs"))),
            {(CHECKER.RECORDS_B2S, "fs-records-b2s-c2.pv")},
        )
        self.assertEqual(
            CHECKER.security_claims(
                (target("R2"), target("b2s-C3-finish"), target("b2s-C-RETAIN"))
            ),
            set(),
        )

    def test_b2s_c3_counts_only_the_server_receive(self):
        # The security target C3 fixes the direction to Beacon-to-Server; the Beacon's
        # finish, which holds by construction in b2s, is the definitional check
        # C3-finish and is never counted.
        security, finish = target("b2s-C3"), target("b2s-C3-finish")
        self.assertEqual(security.cls, "security")
        self.assertEqual(finish.cls, "definitional")
        self.assertIn("FsReceived(beacon_to_server,", security.results[0])
        self.assertNotIn("server_to_beacon", security.results[0])
        self.assertIn("FsReceived(server_to_beacon,", finish.results[0])
        self.assertNotIn("beacon_to_server", finish.results[0])
        self.assertEqual(
            security.results[0].replace("beacon_to_server", "server_to_beacon"),
            finish.results[0],
        )
        text = (CHECKER.HERE / security.query).read_text()
        self.assertIn("FsReceived(beacon_to_server(),", text)
        self.assertNotIn("FsReceived(d,", text)

    def test_loader_order(self):
        for each in CHECKER.TARGETS:
            libraries = each.libraries()
            self.assertEqual(libraries[:4], CHECKER.COMMON_LOADER)
            self.assertEqual(libraries.count("crypto.pvl"), 1)
            if each.scenario == CHECKER.REGISTRATION:
                self.assertEqual(
                    libraries[-2:],
                    ("fs-registration.pvl", f"fs-registration-k{each.bound}.pvl"),
                )
            elif each.scenario == CHECKER.RECORDS_S2B:
                self.assertEqual(len(libraries), 10)
                self.assertEqual(
                    libraries[-3:],
                    (
                        "fs-records-s2b-receive.pvl",
                        f"fs-records-s2b-kr{each.bound}.pvl",
                        "fs-records-s2b.pvl",
                    ),
                )
            else:
                form = "-failstop" if each.failstop else ""
                self.assertEqual(len(libraries), 10)
                self.assertEqual(
                    libraries[-3:],
                    (
                        "fs-records-b2s-receive.pvl",
                        f"fs-records-b2s-kr{each.bound}{form}.pvl",
                        "fs-records-b2s.pvl",
                    ),
                )

    def test_record_bounds(self):
        bounds = {
            each.name: each.bound
            for each in CHECKER.TARGETS
            if each.scenario == CHECKER.RECORDS_S2B and each.cls != "security"
        }
        self.assertEqual(
            bounds,
            {
                "s2b-A3": 1,
                "s2b-C5a": 2,
                "s2b-C5b": 2,
                "s2b-C5c": 1,
                "s2b-S4": 1,
                "s2b-C-RETAIN-C1": 3,
                "s2b-C-RETAIN-C3": 3,
                "s2b-C-NOGATE": 1,
                "s2b-C-STALE": 3,
                "s2b-C-FAILMUT": 2,
            },
        )
        self.assertEqual(target("s2b-C-FAILMUT").bound, target("s2b-C5b").bound)
        bounds = {
            each.name: each.bound
            for each in CHECKER.TARGETS
            if each.scenario == CHECKER.RECORDS_B2S and each.cls != "security"
        }
        self.assertEqual(
            bounds,
            {
                "b2s-C3-finish": 1,
                "b2s-C5a": 2,
                "b2s-C5b": 2,
                "b2s-C5c": 2,
                "b2s-S4": 1,
                "b2s-FAR": 1,
                "b2s-PINREAD": 1,
                "b2s-C-UKS": 1,
                "b2s-C-RETAIN": 3,
                "b2s-C-STALE": 3,
            },
        )

    def test_record_forms(self):
        chosen = {
            each.name
            for each in CHECKER.TARGETS
            if each.scenario == CHECKER.RECORDS_S2B and CHECKER.CHOSEN in each.hooks
        }
        self.assertEqual(chosen, {"s2b-A1", "s2b-A2", "s2b-C1", "s2b-C3", "s2b-C4"})
        inverted = {each.name for each in CHECKER.TARGETS if each.inverted}
        self.assertEqual(inverted, {"s2b-C-FAILMUT"})
        chosen = {
            each.name
            for each in CHECKER.TARGETS
            if each.scenario == CHECKER.RECORDS_B2S
            and CHECKER.SENDS_CHOSEN in each.hooks
        }
        self.assertEqual(
            chosen,
            {
                "b2s-A1",
                "b2s-A2",
                "b2s-C2-chosen-fs",
                "b2s-C3",
                "b2s-C4",
                "b2s-C3-finish",
            },
        )
        failstop = {each.name for each in CHECKER.TARGETS if each.failstop}
        self.assertEqual(failstop, {"b2s-C2-chosen-fs", "b2s-C4"})
        # C2 also runs, with fresh plaintexts, in the failure-interleaving form (G0
        # option B keeps C2 and C3 there).
        self.assertEqual(target("b2s-C2").query, target("b2s-C2-chosen-fs").query)
        self.assertEqual(target("b2s-C2").results, target("b2s-C2-chosen-fs").results)
        self.assertFalse(target("b2s-C2").failstop)
        self.assertIn(CHECKER.SENDS, target("b2s-C2").hooks)
        self.assertFalse(target("b2s-C3").failstop)

    def mutated(self, name, **changes):
        targets = tuple(
            dataclasses.replace(each, **changes) if each.name == name else each
            for each in CHECKER.TARGETS
        )
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(targets)

    def test_security_bound_cannot_drop(self):
        self.mutated("A1", bound=2)

    def test_security_cannot_load_a_mutant(self):
        self.mutated("R1", hooks=(CHECKER.NOCHECK, CHECKER.BINDING))
        self.mutated("s2b-C1", hooks=(CHECKER.RETAIN, CHECKER.GATE, CHECKER.CHOSEN))
        self.mutated(
            "b2s-C2", hooks=(CHECKER.B2S_RETAIN, CHECKER.BINDING, CHECKER.SENDS_CHOSEN)
        )
        self.mutated("b2s-UKSr", hooks=(CHECKER.B2S_WINDOW, CHECKER.UKS, CHECKER.SENDS))

    def test_two_mutants_are_rejected(self):
        self.mutated("A1", hooks=(CHECKER.NOCHECK, CHECKER.UKS))
        self.mutated("R3", hooks=(CHECKER.NOCHECK, CHECKER.UKS))
        self.mutated("C-UKS", hooks=(CHECKER.NOCHECK, CHECKER.UKS))
        self.mutated("s2b-C1", hooks=(CHECKER.RETAIN, CHECKER.NOGATE, CHECKER.CHOSEN))
        self.mutated("s2b-A1", hooks=(CHECKER.STALE, CHECKER.NOGATE, CHECKER.CHOSEN))
        self.mutated(
            "s2b-C5b", hooks=(CHECKER.FAILMUT, CHECKER.NOGATE, CHECKER.TASKINGS)
        )
        self.mutated(
            "s2b-C-NOGATE", hooks=(CHECKER.RETAIN, CHECKER.NOGATE, CHECKER.TASKINGS)
        )
        self.mutated(
            "b2s-C3", hooks=(CHECKER.B2S_STALE, CHECKER.UKS, CHECKER.SENDS_CHOSEN)
        )
        self.mutated(
            "b2s-C-UKS", hooks=(CHECKER.B2S_RETAIN, CHECKER.UKS, CHECKER.SENDS)
        )

    def test_witness_cannot_load_a_mutant(self):
        self.mutated("W1", hooks=(CHECKER.NOCHECK, CHECKER.BINDING))
        self.mutated("s2b-C5c", hooks=(CHECKER.RETAIN, CHECKER.GATE, CHECKER.TASKINGS))
        self.mutated("b2s-C5c", hooks=(CHECKER.B2S_WINDOW, CHECKER.UKS, CHECKER.SENDS))

    def test_control_needs_its_mutant(self):
        self.mutated("C-UKS", hooks=(CHECKER.CONSUMED, CHECKER.BINDING))
        self.mutated(
            "s2b-C-STALE", hooks=(CHECKER.WINDOW, CHECKER.GATE, CHECKER.TASKINGS)
        )
        self.mutated(
            "s2b-C-NOGATE", hooks=(CHECKER.RETAIN, CHECKER.NOGATE, CHECKER.TASKINGS)
        )
        self.mutated(
            "b2s-C-UKS", hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS)
        )
        self.mutated(
            "b2s-C-RETAIN", hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS)
        )

    def test_hooks_must_fit_the_scenario(self):
        self.mutated("s2b-A3", hooks=(CHECKER.CONSUMED, CHECKER.GATE, CHECKER.TASKINGS))
        self.mutated("R2", hooks=(CHECKER.CONSUMED, CHECKER.BINDING, CHECKER.TASKINGS))
        self.mutated("s2b-A3", scenario="fs-records-b2s")
        self.mutated("b2s-S4", hooks=(CHECKER.WINDOW, CHECKER.GATE, CHECKER.TASKINGS))
        self.mutated(
            "b2s-C-STALE", hooks=(CHECKER.STALE, CHECKER.BINDING, CHECKER.SENDS)
        )
        self.mutated("b2s-S4", scenario="fs-records-s2b")

    def test_record_security_bound_cannot_drop(self):
        self.mutated("s2b-C3", bound=2)
        self.mutated("s2b-C5b", bound=4)
        self.mutated("b2s-UKSr", bound=2)
        self.mutated("b2s-C2", bound=1)
        self.mutated("b2s-C5a", bound=4)

    def test_failstop_only_extends_listed_security_results(self):
        self.mutated("b2s-C3", failstop=True)
        self.mutated("b2s-C3-finish", failstop=True)
        self.mutated("b2s-C5a", failstop=True)
        self.mutated("b2s-C-RETAIN", failstop=True)
        self.mutated(
            "b2s-C2-chosen-fs",
            hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS),
        )
        self.mutated("b2s-C2-chosen-fs", bound=2)
        self.mutated("b2s-C4", cls="witness")
        self.mutated("s2b-C1", failstop=True)
        self.mutated("A1", failstop=True)

    def test_failstop_query_cannot_mention_rejections(self):
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory)
            for path in CHECKER.HERE.glob("*.pv*"):
                shutil.copy(path, copy / path.name)
            (copy / "extraction").mkdir()
            shutil.copy(
                CHECKER.HERE / "extraction/lib.pvl", copy / "extraction/lib.pvl"
            )
            CHECKER.validate_targets(CHECKER.TARGETS, copy)
            query = copy / "fs-records-b2s-c4.pv"
            query.write_text(
                query.read_text().replace(
                    "process FsRecordsB2sMainAnyPin()",
                    "(* FsReceiveRejected *)\nprocess FsRecordsB2sMainAnyPin()",
                )
            )
            with self.assertRaises(ValueError) as caught:
                CHECKER.validate_targets(CHECKER.TARGETS, copy)
            self.assertIn("FsReceiveRejected", str(caught.exception))

    def test_secrecy_cannot_use_chosen_plaintexts(self):
        self.mutated("s2b-S1", hooks=(CHECKER.WINDOW, CHECKER.GATE, CHECKER.CHOSEN))
        self.mutated("s2b-S4", hooks=(CHECKER.WINDOW, CHECKER.GATE, CHECKER.CHOSEN))
        self.mutated(
            "b2s-S2", hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS_CHOSEN)
        )
        self.mutated(
            "b2s-UKSr",
            hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS_CHOSEN),
        )
        self.mutated(
            "b2s-C-UKS", hooks=(CHECKER.B2S_WINDOW, CHECKER.UKS, CHECKER.SENDS_CHOSEN)
        )
        self.mutated(
            "b2s-PINREAD",
            hooks=(CHECKER.B2S_WINDOW, CHECKER.BINDING, CHECKER.SENDS_CHOSEN),
        )

    def test_only_controls_are_inverted(self):
        self.mutated("s2b-C5b", inverted=True)
        self.mutated("s2b-C-FAILMUT", inverted=False)

    def test_query_of_another_scenario(self):
        self.mutated("s2b-A2", query="fs-registration-a2.pv")
        self.mutated("b2s-A2", query="fs-records-s2b-a2.pv")

    def test_unknown_class(self):
        self.mutated("R2", cls="evidence")

    def test_polarity_must_match_class(self):
        self.mutated("R3", cls="security")
        self.mutated("A2", cls="witness")

    def test_cannot_expect_inconclusive(self):
        self.mutated("R4", results=(CHECKER.R4 + " cannot be proved.",))

    def test_missing_query_file(self):
        self.mutated("W3", query="fs-registration-missing.pv")

    def test_every_query_file_is_used(self):
        with tempfile.TemporaryDirectory() as directory:
            copy = Path(directory)
            for path in CHECKER.HERE.glob("*.pv*"):
                shutil.copy(path, copy / path.name)
            (copy / "extraction").mkdir()
            shutil.copy(
                CHECKER.HERE / "extraction/lib.pvl", copy / "extraction/lib.pvl"
            )
            CHECKER.validate_targets(CHECKER.TARGETS, copy)
            for unused in (
                "fs-registration-unused.pv",
                "fs-records-s2b-unused.pv",
                "fs-records-b2s-unused.pv",
            ):
                (copy / unused).write_text("process 0\n")
                with self.assertRaises(ValueError):
                    CHECKER.validate_targets(CHECKER.TARGETS, copy)
                (copy / unused).unlink()

    def test_duplicate_name(self):
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(CHECKER.TARGETS + (CHECKER.TARGETS[0],))

    def test_every_target_has_its_own_log(self):
        names = [CHECKER.log_name(each) for each in CHECKER.TARGETS]
        self.assertEqual(len(set(names)), len(names))
        self.assertEqual(CHECKER.log_name(target("R1'")), "R1prime.log")
        self.assertEqual(CHECKER.log_name(target("R1")), "R1.log")
        clash = dataclasses.replace(target("R1"), name="R1-")
        with self.assertRaises(ValueError) as caught:
            CHECKER.validate_targets(CHECKER.TARGETS + (clash,))
        self.assertIn("share a log file", str(caught.exception))


class ProcessTests(unittest.TestCase):
    """Exercise the runner with a stand-in executable instead of ProVerif."""

    def fake(self, directory, body):
        path = Path(directory) / "fake-proverif"
        path.write_text(f"#!{sys.executable}\n{body}\n")
        path.chmod(path.stat().st_mode | stat.S_IXUSR)
        return str(path)

    def test_exact_receipt_passes(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory, f"import sys\nsys.stdout.write({receipt(each)!r})"
            )
            seconds, peak = CHECKER.check_target(fake, each, Path(directory), 60, 0)
            self.assertGreaterEqual(seconds, 0)
            self.assertGreater(peak, 0)

    def test_wrong_receipt_fails(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            text = receipt(each).replace("is false.", "is true.")
            fake = self.fake(directory, f"import sys\nsys.stdout.write({text!r})")
            with self.assertRaises(ValueError):
                CHECKER.check_target(fake, each, Path(directory), 60, 0)

    def test_nonzero_exit_fails(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory,
                f"import sys\nsys.stdout.write({receipt(each)!r})\nsys.exit(2)",
            )
            with self.assertRaises(ValueError):
                CHECKER.check_target(fake, each, Path(directory), 60, 0)

    def test_timeout_fails(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(directory, "import time\ntime.sleep(30)")
            with self.assertRaises(ValueError) as caught:
                CHECKER.check_target(fake, each, Path(directory), 1, 0)
            self.assertIn("timeout", str(caught.exception))

    def test_address_space_cap_applies(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory,
                "import resource, sys\n"
                "soft, hard = resource.getrlimit(resource.RLIMIT_AS)\n"
                "sys.exit(3) if soft != 1048576 * 1024 or hard != soft else None\n"
                f"sys.stdout.write({receipt(each)!r})",
            )
            CHECKER.check_target(fake, each, Path(directory), 60, 1048576)
            with self.assertRaises(ValueError) as caught:
                CHECKER.check_target(fake, each, Path(directory), 60, 0)
            self.assertIn("exited 3", str(caught.exception))

    def test_failed_targets_keep_the_named_log(self):
        each = target("R3")
        wrong = receipt(each).replace("is false.", "is true.")
        for name, body in (
            ("exit", f"import sys\nsys.stdout.write({receipt(each)!r})\nsys.exit(2)"),
            ("receipt", f"import sys\nsys.stdout.write({wrong!r})"),
            (
                "timeout",
                "import sys, time\nprint('started', flush=True)\ntime.sleep(30)",
            ),
        ):
            with self.subTest(name), tempfile.TemporaryDirectory() as directory:
                fake = self.fake(directory, body)
                scratch = Path(directory) / "scratch"
                scratch.mkdir()
                errors = io.StringIO()
                with contextlib.redirect_stdout(io.StringIO()):
                    with contextlib.redirect_stderr(errors):
                        with self.assertRaises(SystemExit) as caught:
                            CHECKER.run_logged(
                                fake, (each,), None, 1, 0, None, scratch=scratch
                            )
                logs = list(scratch.glob("beaconcrypt-fs-logs-*/R3.log"))
                self.assertEqual(len(logs), 1)
                self.assertIn(f"({logs[0]})", str(caught.exception))
                self.assertIn(f"logs kept in {logs[0].parent}", errors.getvalue())
                self.assertTrue(logs[0].read_text())

    def test_successful_run_removes_its_temporary_logs(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory, f"import sys\nsys.stdout.write({receipt(each)!r})"
            )
            scratch = Path(directory) / "scratch"
            scratch.mkdir()
            with contextlib.redirect_stdout(io.StringIO()):
                CHECKER.run_logged(fake, (each,), None, 60, 0, None, scratch=scratch)
            self.assertEqual(list(scratch.iterdir()), [])

    def test_summary_counts_security_targets_and_claims(self):
        # Two security targets with one query file are one claim; a definitional check is
        # never counted as evidence.
        chosen = ("b2s-C2", "b2s-C2-chosen-fs", "b2s-C3-finish")
        receipts = {target(name).query: receipt(target(name)) for name in chosen}
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory,
                "import sys\n"
                f"receipts = {receipts!r}\n"
                "sys.stdout.write(receipts[sys.argv[-1].rsplit('/', 1)[-1]])",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                CHECKER.run_logged(
                    fake,
                    tuple(target(name) for name in chosen),
                    Path(directory) / "logs",
                    60,
                    0,
                    None,
                )
        summary = output.getvalue().splitlines()[-1]
        self.assertIn("fs ProVerif targets: 3 exact results in ", summary)
        self.assertIn(
            "counted as evidence: 2 security targets, 1 distinct security claims",
            summary,
        )

    def test_log_dir_keeps_every_log(self):
        each = target("R3")
        with tempfile.TemporaryDirectory() as directory:
            fake = self.fake(
                directory, f"import sys\nsys.stdout.write({receipt(each)!r})"
            )
            logs = Path(directory) / "logs"
            with contextlib.redirect_stdout(io.StringIO()):
                CHECKER.run_logged(fake, (each,), logs, 60, 0, None)
            self.assertEqual((logs / "R3.log").read_text(), receipt(each))

    def test_command_loads_every_library_once(self):
        each = target("C-NOCHECK")
        arguments = CHECKER.command("proverif", each)
        libraries = [
            Path(arguments[i + 1]).name
            for i, arg in enumerate(arguments)
            if arg == "-lib"
        ]
        self.assertEqual(
            libraries,
            [
                "production-transcript-interface.pvl",
                "crypto.pvl",
                "lib.pvl",
                "fs-common.pvl",
                "fs-control-nocheck.pvl",
                "fs-registration-binding.pvl",
                "fs-registration.pvl",
                "fs-registration-k2.pvl",
            ],
        )
        self.assertEqual(Path(arguments[-1]).name, "fs-registration-r1.pv")

    def test_record_command_loads_its_mutant(self):
        each = target("s2b-C-NOGATE")
        arguments = CHECKER.command("proverif", each)
        libraries = [
            Path(arguments[i + 1]).name
            for i, arg in enumerate(arguments)
            if arg == "-lib"
        ]
        self.assertEqual(
            libraries,
            [
                "production-transcript-interface.pvl",
                "crypto.pvl",
                "lib.pvl",
                "fs-common.pvl",
                "fs-records-s2b-window.pvl",
                "fs-control-nogate.pvl",
                "fs-records-s2b-taskings.pvl",
                "fs-records-s2b-receive.pvl",
                "fs-records-s2b-kr1.pvl",
                "fs-records-s2b.pvl",
            ],
        )
        self.assertEqual(Path(arguments[-1]).name, "fs-records-s2b-a1.pv")

    def test_b2s_command_loads_the_binding_mutant(self):
        each = target("b2s-C-UKS")
        arguments = CHECKER.command("proverif", each)
        libraries = [
            Path(arguments[i + 1]).name
            for i, arg in enumerate(arguments)
            if arg == "-lib"
        ]
        self.assertEqual(
            libraries,
            [
                "production-transcript-interface.pvl",
                "crypto.pvl",
                "lib.pvl",
                "fs-common.pvl",
                "fs-records-b2s-window.pvl",
                "fs-control-uks.pvl",
                "fs-records-b2s-sends.pvl",
                "fs-records-b2s-receive.pvl",
                "fs-records-b2s-kr1.pvl",
                "fs-records-b2s.pvl",
            ],
        )
        self.assertEqual(Path(arguments[-1]).name, "fs-records-b2s-uksr.pv")

    def test_b2s_failstop_command_loads_the_failstop_bound(self):
        each = target("b2s-C2-chosen-fs")
        arguments = CHECKER.command("proverif", each)
        libraries = [
            Path(arguments[i + 1]).name
            for i, arg in enumerate(arguments)
            if arg == "-lib"
        ]
        self.assertEqual(
            libraries[4:],
            [
                "fs-records-b2s-window.pvl",
                "fs-registration-binding.pvl",
                "fs-records-b2s-sends-chosen.pvl",
                "fs-records-b2s-receive.pvl",
                "fs-records-b2s-kr3-failstop.pvl",
                "fs-records-b2s.pvl",
            ],
        )
        self.assertEqual(Path(arguments[-1]).name, "fs-records-b2s-c2.pv")

    def test_scenario_selection(self):
        for scenario in CHECKER.SCENARIOS:
            listed = subprocess.run(
                [
                    sys.executable,
                    str(CHECKER.HERE / "check-free-schedule.py"),
                    "--list",
                    "--scenario",
                    scenario,
                ],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.splitlines()
            names = [line.split("\t")[0] for line in listed]
            self.assertEqual(
                names,
                [each.name for each in CHECKER.TARGETS if each.scenario == scenario],
            )


if __name__ == "__main__":
    unittest.main()
