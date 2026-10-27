#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regressions for the exact-ID near origin projection and strict verifier gate."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "tasking_origin_checker", Path(__file__).with_name("check-tasking-origin.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class TaskingOriginChecks(unittest.TestCase):
    def fixture(self, directory):
        for name in CHECKER.TOKEN_SHA256:
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(CHECKER.HERE / name, target)

    def mutate(self, filename, old, new, *, comparison_only=False, expected_count=1):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            self.fixture(directory)
            path = directory / filename
            text = path.read_text()
            self.assertEqual(text.count(old), expected_count)
            path.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                if comparison_only:
                    CHECKER.MODELS.validate(directory)
                else:
                    CHECKER.validate_targets(directory=directory)

    def test_exact_manifest_and_retained_registration(self):
        CHECKER.validate_targets()
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS],
            ["security", "security", "security", "negative-control", "witness"],
        )
        self.assertEqual([t.bound for t in CHECKER.TARGETS], [3, 3, 3, 3, 2])
        self.assertEqual(sum(len(t.results) for t in CHECKER.TARGETS), 5)
        self.assertEqual(CHECKER.MODELS.replay_cases(), 80)

    def test_lexical_token_identity(self):
        self.assertEqual(
            CHECKER.digest("fun f()."), CHECKER.digest("(* comment *) fun f ( ) .")
        )
        for left, right in (
            ("fun name", "funname"),
            ('"a b"', '"ab"'),
            ('"(* a *)"', '""'),
            ("x ==> y", "x = = > y"),
        ):
            self.assertNotEqual(CHECKER.digest(left), CHECKER.digest(right))

    def test_unbounded_accepts_and_one_use_pending_are_retained(self):
        self.mutate("tasking-origin.pvl", " !in(c,a1_accept(", " in(c,a1_accept(")
        self.mutate("tasking-origin.pvl", " in(c, a1_build(", " !in(c, a1_build(")

    def test_binding_ids_and_routing_are_exact(self):
        for old, new in (
            (" && builder_id = accepted_id", ""),
            ("if frame_sender = server_key_id then", "if true then"),
            (
                "key_id_encoding(assigned)) in\n   let frame",
                "key_id_encoding(fs_kid(1))) in\n   let frame",
            ),
        ):
            self.mutate("tasking-origin.pvl", old, new, comparison_only=True)
        self.mutate(
            "tasking-origin-receive.pvl",
            "fs_seq(t:nat),=sender",
            "fs_seq(t:nat),unchecked_sender:key_id",
        )

    def test_disclosure_boundary_and_public_handle_do_not_drift(self):
        self.mutate(
            "tasking-origin.pvl",
            "if identity <> selected_identity",
            "if true",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin.pvl",
            "a1_some(token)",
            "a1_some((token,root))",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin.pvl",
            "ratchet_next(ratchet_next(ratchet_next(server_to_beacon_chain(root))))));",
            "ratchet_next(server_to_beacon_chain(root))));",
            comparison_only=True,
        )

    def test_single_receiver_starts_after_sequence_one(self):
        self.mutate(
            "tasking-origin.pvl",
            " A1Beacon(selected_identity_secret,",
            " !A1Beacon(selected_identity_secret,",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin.pvl",
            "server_to_beacon_chain(root)))),1,false)",
            "server_to_beacon_chain(root)))),0,false)",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin-sends.pvl",
            ",sender,plaintext)",
            ",kid,plaintext)",
            comparison_only=True,
            expected_count=4,
        )

    def test_complete_finish_and_plaintext_are_preserved(self):
        self.mutate(
            "tasking-origin.pvl",
            "if frame_sequence = fs_seq(1) then",
            "if true then",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin.pvl",
            "a1_some(application_payload)",
            "a1_some(response)",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin-receive.pvl",
            "Next(owner,s,b,sender,kid,root,ad,m1,m2,far,r,false)",
            "Next(owner,s,b,sender,kid,root,ad,m1,m2,far,r,true)",
        )

    def test_query_and_control_require_exact_origin(self):
        self.mutate(
            "tasking-origin-auth.pv", "==> event(S2bPublished", "==> event(FsSent"
        )
        self.mutate(
            "tasking-origin-leak-control.pv",
            "process S2bMain(true)",
            "process S2bMain(false)",
            comparison_only=True,
        )

    def test_receive_bounds_and_ghost_erasure_are_exact(self):
        self.mutate(
            "tasking-origin-kr3.pvl",
            "S2bRecv3,S2bRecvStop",
            "S2bRecv3,S2bRecv3",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin-kr2.pvl",
            "S2bRecv2,S2bRecvStop",
            "S2bRecv2,S2bRecv2",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin-cache-receive.pvl",
            "event S2bCachedAccepted(s,b,kid,root,plaintext);",
            "event S2bCachedAccepted(s,b,kid,root,frame);",
            comparison_only=True,
        )
        self.mutate(
            "tasking-origin-cache-sends.pvl",
            "event S2bPublished(server_to_beacon(),s,b,kid,root,2,plaintext);",
            "event FsSent(server_to_beacon(),s,b,kid,root,2,plaintext);",
            comparison_only=True,
            expected_count=2,
        )

    def test_failed_seal_does_not_publish(self):
        self.mutate(
            "tasking-origin-sends.pvl",
            "if fail_seal then (out(c,s2b_reply(call,s2b_none())); S2bSend3(owner,s,b,sender,kid,root,ad,ratchet_next(chain)))",
            "if fail_seal then (event S2bPublished(server_to_beacon(),s,b,kid,root,2,plaintext); out(c,s2b_reply(call,s2b_none())); S2bSend3(owner,s,b,sender,kid,root,ad,ratchet_next(chain)))",
            expected_count=2,
        )

    def test_replay_audit_rejects_retained_consumed_key(self):
        original = CHECKER.MODELS.local_transition

        def bad(r, cached, target, valid, opened):
            nr, nc, accepted = original(r, cached, target, valid, opened)
            return (
                (nr, True, accepted)
                if r == 3 and cached and target == 2 and accepted
                else (nr, nc, accepted)
            )

        try:
            CHECKER.MODELS.local_transition = bad
            with self.assertRaises(ValueError):
                CHECKER.MODELS.replay_cases()
        finally:
            CHECKER.MODELS.local_transition = original

    def test_complete_roster_and_classes(self):
        for i, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(CHECKER.TARGETS[:i] + CHECKER.TARGETS[i + 1 :])
            changed = list(CHECKER.TARGETS)
            changed[i] = replace(target, cls="definitional")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(changed)
            changed[i] = replace(target, bound=2 if target.bound == 3 else 3)
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(changed)

    def test_source_boundary_requires_new_review(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            for name in CHECKER.SOURCE_SHA256:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE.parents[2] / name, root / name)
            with (root / "beaconcrypt/src/server.rs").open("a") as stream:
                stream.write("\n// source projection changed\n")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(source_root=root)

    def test_exact_results_and_counterexample_traces(self):
        for target in CHECKER.TARGETS:
            trace = "A trace has been found.\n" * target.expected_traces()
            output = (
                "".join("RESULT " + result + "\n" for result in target.results)
                + trace
                + "Verification summary:\n"
                + "Query "
                + target.results[0]
                + "\n"
            )
            CHECKER.FS.check_output(output, target)
            for bad in (
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
            ):
                with self.assertRaises(ValueError):
                    CHECKER.FS.check_output(bad, target)


if __name__ == "__main__":
    unittest.main()
