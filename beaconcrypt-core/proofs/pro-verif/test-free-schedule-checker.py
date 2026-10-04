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
        for line in ("Error: something\n", "Warning: something\n"):
            with self.assertRaises(ValueError):
                CHECKER.check_output(line + receipt(each), each)


class ManifestTests(unittest.TestCase):
    def test_manifest_is_consistent(self):
        CHECKER.validate_targets()

    def test_classes_and_bounds(self):
        counts = {}
        for each in CHECKER.TARGETS:
            counts[each.cls] = counts.get(each.cls, 0) + 1
            if each.cls == "security":
                self.assertEqual(each.bound, 3)
        self.assertEqual(
            counts,
            {
                "security": 6,
                "definitional": 1,
                "witness": 5,
                "control": 2,
                "limitation": 1,
            },
        )

    def test_loader_order(self):
        for each in CHECKER.TARGETS:
            libraries = each.libraries()
            self.assertEqual(libraries[:4], CHECKER.COMMON_LOADER)
            self.assertEqual(libraries.count("crypto.pvl"), 1)
            self.assertEqual(
                libraries[-2:],
                ("fs-registration.pvl", f"fs-registration-k{each.bound}.pvl"),
            )

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
        self.mutated("R1", consumed=CHECKER.NOCHECK)

    def test_control_needs_its_mutant(self):
        self.mutated("C-UKS", binding=CHECKER.BINDING)

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
            (copy / "fs-registration-unused.pv").write_text("process 0\n")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(CHECKER.TARGETS, copy)

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


if __name__ == "__main__":
    unittest.main()
