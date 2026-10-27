#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative regressions for target-preserving application observations and gates."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "application_checker", Path(__file__).with_name("check-application-secrecy.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ApplicationSecrecyChecks(unittest.TestCase):
    def mutate(self, name, old, new, count=1, comparison=True):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for source in CHECKER.TOKEN_SHA256:
                p = directory / source
                p.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE / source, p)
            p = directory / name
            t = p.read_text()
            self.assertEqual(t.count(old), count)
            p.write_text(t.replace(old, new, 1))
            with self.assertRaises(ValueError):
                if comparison:
                    CHECKER.MODELS.validate(directory)
                else:
                    CHECKER.validate_targets(directory=directory)

    def test_exact_four_targets_and_bounds(self):
        CHECKER.validate_targets()
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS],
            ["security", "security", "negative-control", "negative-control"],
        )
        self.assertEqual([t.bound for t in CHECKER.TARGETS], [3] * 4)
        self.assertEqual(
            [t.direction for t in CHECKER.TARGETS], ["b2s", "s2b", "b2s", "s2b"]
        )
        self.assertEqual([t.expected_traces() for t in CHECKER.TARGETS], [0, 0, 1, 1])

    def test_public_receive_payload_stays_private(self):
        for direction, low in [("b2s", "l2"), ("s2b", "s2b")]:
            self.mutate(
                "application-secrecy-" + direction + "-receive.pvl",
                low + "_some(" + low + "_received())",
                low + "_some(plaintext)",
                3,
            )

    def test_optional_success_and_failure_remain_observable(self):
        self.mutate(
            "application-secrecy-b2s-receive.pvl",
            "l2_some(l2_received())",
            "l2_none()",
            3,
        )
        self.mutate(
            "application-secrecy-s2b-receive.pvl",
            "out(c,s2b_reply(call,s2b_none()));",
            "0;",
            6,
        )

    def test_receive_evaluation_and_cached_consumption_are_exact(self):
        self.mutate(
            "application-secrecy-s2b-receive.pvl",
            "open_frame(m1,ad,fs_seq(2),sender,frame)",
            "open_frame(m2,ad,fs_seq(2),sender,frame)",
            2,
        )
        self.mutate(
            "application-secrecy-s2b-receive.pvl", "far,r,false)", "far,r,true)"
        )

    def test_marker_requires_successful_fresh_publication(self):
        self.mutate(
            "application-secrecy-b2s-sends.pvl",
            "event L2FreshPublished",
            "event L2Published",
            2,
        )
        self.mutate(
            "application-secrecy-b2s-sends.pvl",
            "if fail_seal then (out(c,l2_reply(call,l2_none())); 0)",
            "if fail_seal then (event L2FreshPublished(beacon_to_server(),s,b,kid,root,2,plaintext); out(c,l2_reply(call,l2_none())); 0)",
            2,
        )

    def test_chosen_branch_does_not_get_fresh_marker(self):
        self.mutate(
            "application-secrecy-s2b-sends.pvl",
            "if use_chosen then (let plaintext=chosen in",
            "if use_chosen then (let plaintext=chosen in event S2bFreshPublished(server_to_beacon(),s,b,kid,root,3,plaintext);",
            2,
        )

    def test_actual_sender_and_event_ids_are_distinct(self):
        self.mutate(
            "application-secrecy-s2b-sends.pvl",
            ",sender,plaintext)",
            ",kid,plaintext)",
            4,
        )
        self.mutate(
            "application-secrecy-b2s-sends.pvl",
            "beacon_to_server(),s,b,kid,root,2,plaintext); event L2FreshPublished",
            "beacon_to_server(),s,b,fs_kid(1),root,2,plaintext); event L2FreshPublished",
        )

    def test_precision_and_name_dependency_delta_is_pinned(self):
        for direction in ["b2s", "s2b"]:
            self.mutate(
                "application-secrecy-" + direction + ".pvl",
                "raw:bitstring,accept_call:bitstring)) [precise];",
                "raw:bitstring,accept_call:bitstring));",
            )
        self.mutate(
            "application-secrecy-b2s-sends.pvl",
            "new fresh:bitstring;",
            "new fresh[]:bitstring;",
            2,
        )

    def test_selected_root_and_receive_bound_remain_protected(self):
        self.mutate(
            "application-secrecy-s2b.pvl", "if identity <> selected_identity", "if true"
        )
        self.mutate(
            "record-origin-kr3.pvl",
            "L2Recv3,L2RecvStop",
            "L2Recv3,L2Recv3",
            comparison=False,
        )

    def test_leak_controls_are_exact(self):
        for direction in ["b2s", "s2b"]:
            self.mutate(
                "application-secrecy-" + direction + "-leak-sends.pvl",
                " out(c,plaintext);",
                "",
                2,
            )
        self.mutate(
            "application-secrecy-b2s-leak.pv", "&& attacker(m)", "&& attacker(root)"
        )

    def test_roster_classes_bound_and_libraries_fail_closed(self):
        for index, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(
                    CHECKER.TARGETS[:index] + CHECKER.TARGETS[index + 1 :]
                )
            for change in [
                dict(cls="definitional"),
                dict(bound=2),
                dict(direction="s2b" if target.direction == "b2s" else "b2s"),
                dict(leak=not target.leak),
            ]:
                changed = list(CHECKER.TARGETS)
                changed[index] = replace(target, **change)
                with self.assertRaises(ValueError):
                    CHECKER.validate_targets(changed)

    def test_source_change_requires_review(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            for name in CHECKER.SOURCE_SHA256:
                p = root / name
                p.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE.parents[2] / name, p)
            p = root / "beaconcrypt/src/beacon.rs"
            p.write_text(p.read_text() + "\n// changed source\n")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(source_root=root)

    def test_exact_verdicts_and_confirmed_traces(self):
        for target in CHECKER.TARGETS:
            trace = "A trace has been found.\n" * target.expected_traces()
            output = (
                "RESULT "
                + target.results[0]
                + "\n"
                + trace
                + "Verification summary:\nQuery "
                + target.results[0]
                + "\n"
            )
            CHECKER.FS.check_output(output, target)
            variants = [
                output.replace("RESULT ", "", 1),
                output.replace("Verification summary:", ""),
                output.replace(" is true.", " cannot be proved.").replace(
                    " is false.", " cannot be proved."
                ),
                output + "Warning: changed process\n",
                (
                    output.replace(trace, "", 1)
                    if trace
                    else output.replace(
                        "Verification summary:",
                        "A trace has been found.\nVerification summary:",
                    )
                ),
            ]
            for bad in variants:
                with self.assertRaises(ValueError):
                    CHECKER.FS.check_output(bad, target)


if __name__ == "__main__":
    unittest.main()
