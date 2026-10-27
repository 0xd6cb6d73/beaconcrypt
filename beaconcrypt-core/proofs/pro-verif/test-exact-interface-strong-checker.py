#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative regressions for the paired interface, observation and exact gates."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "exact_strong_checker", Path(__file__).with_name("check-exact-interface-strong.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ExactInterfaceStrongChecks(unittest.TestCase):
    def mutate(self, name, old, new, count=1, comparison=True):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for source in CHECKER.TOKEN_SHA256:
                p = directory / source
                p.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE / source, p)
            p = directory / name
            text = p.read_text()
            self.assertEqual(text.count(old), count)
            p.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                if comparison:
                    CHECKER.MODELS.validate(directory)
                else:
                    CHECKER.validate_targets(directory=directory)

    def test_complete_eight_target_roster(self):
        CHECKER.validate_targets()
        self.assertEqual([t.bound for t in CHECKER.TARGETS], [3] * 8)
        self.assertEqual(
            [t.kind for t in CHECKER.TARGETS],
            [k for k in ["equivalence", "origin", "leak", "ungated"] for _ in range(2)],
        )
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS],
            ["security"] * 4 + ["negative-control"] * 4,
        )
        self.assertEqual(
            [t.expected_traces() for t in CHECKER.TARGETS], [0] * 4 + [1] * 4
        )

    def test_selected_eligibility_is_exact_signing_identity(self):
        self.mutate(
            "exact-interface-strong-b2s-sends.pvl",
            "if s=ed_public(SERVER_IDENTITY_SECRET)",
            "if true",
            2,
        )
        self.mutate(
            "exact-interface-strong-s2b-sends.pvl",
            "if b=selected_identity",
            "if true",
            2,
        )
        self.mutate(
            "exact-interface-strong-s2b.pvl",
            "root,selected_identity)",
            "root,identity)",
        )

    def test_two_caller_alternatives_and_ordinary_branch(self):
        for direction in ["b2s", "s2b"]:
            filename = "exact-interface-strong-" + direction + "-sends.pvl"
            self.mutate(filename, "choice[left,right]", "left", 2)
            self.mutate(
                filename,
                "if use_chosen then (let plaintext=left in",
                "if use_chosen then (let plaintext=right in",
                2,
            )
            self.mutate(filename, "else left in", "else right in", 2)

    def test_public_reply_bits_and_private_plaintext(self):
        for direction, low in [("b2s", "l2"), ("s2b", "s2b")]:
            filename = "exact-interface-strong-" + direction + "-receive.pvl"
            self.mutate(
                filename,
                low + "_some(" + low + "_received())",
                low + "_some(plaintext)",
                3,
            )
            self.mutate(
                filename, "out(c," + low + "_reply(call," + low + "_none()));", "0;", 6
            )

    def test_actual_raw_open_cache_consumption_and_rollback(self):
        filename = "exact-interface-strong-s2b-receive.pvl"
        self.mutate(
            filename,
            "open_frame(m1,ad,fs_seq(2),sender,frame)",
            "open_frame(m2,ad,fs_seq(2),sender,frame)",
            2,
        )
        self.mutate(filename, "far,r,false)", "far,r,true)")
        self.mutate(
            filename,
            "s2b_none())); Next(owner,s,b,sender,kid,root,ad,m1,m2,far,r,cached)",
            "s2b_none())); Next(owner,s,b,sender,kid,root,ad,m1,m2,far,r,false)",
            6,
        )

    def test_failed_send_advances_and_never_publishes(self):
        filename = "exact-interface-strong-s2b-sends.pvl"
        self.mutate(
            filename,
            "ratchet_next(chain),selected_identity)",
            "chain,selected_identity)",
            4,
        )
        self.mutate(
            filename,
            "if fail_seal then (out(c,s2b_reply(call,s2b_none())); 0)",
            "if fail_seal then (out(c,s2b_reply(call,s2b_some(plaintext))); 0)",
            2,
        )

    def test_worker_owner_and_both_real_ids(self):
        self.mutate(
            "exact-interface-strong-s2b-sends.pvl",
            "s2b_send(=owner,",
            "s2b_send(owner_supplied:bitstring,",
            2,
        )
        self.mutate(
            "exact-interface-strong-b2s-receive.pvl",
            "l2_receive(=owner,",
            "l2_receive(owner_supplied:bitstring,",
        )
        self.mutate(
            "exact-interface-strong-s2b-sends.pvl",
            ",sender,plaintext)",
            ",kid,plaintext)",
            4,
        )
        self.mutate(
            "exact-interface-strong-s2b.pvl",
            "builder_id = accepted_id",
            "builder_id = assigned",
        )

    def test_pending_one_use_and_failure_guards(self):
        filename = "exact-interface-strong-s2b.pvl"
        self.mutate(filename, " in(c, a1_build(=token,", " !in(c, a1_build(=token,")
        self.mutate(filename, "&& fail_build = false", "&& true")
        self.mutate(
            filename, "builder_identity = ed_public(SERVER_IDENTITY_SECRET)", "true"
        )

    def test_disclosed_chains_and_root_condition(self):
        filename = "exact-interface-strong-s2b.pvl"
        self.mutate(filename, "if identity <> selected_identity", "if true")
        self.mutate(
            filename,
            "ratchet_next(ratchet_next(ratchet_next(server_to_beacon_chain(root))))",
            "server_to_beacon_chain(root)",
            2,
        )

    def test_full_response_root_origin_and_occurrence_sites(self):
        for direction in ["b2s", "s2b"]:
            self.mutate(
                "exact-interface-strong-" + direction + "-origin.pvl",
                "event ExactStrongFinishedResponse(server_identity,beacon_identity,response,root);",
                "event ExactStrongFinishedResponse(server_identity,beacon_identity,response,application_payload);",
            )
            self.mutate(
                "exact-interface-strong-" + direction + "-origin.pvl",
                "event ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET),identity,response,root);",
                "",
            )
            self.mutate(
                "exact-interface-strong-" + direction + "-origin.pv",
                "response,root))",
                "response,response))",
                2,
            )

    def test_fresh_reachability_controls_and_eligibility_removal(self):
        for direction in ["b2s", "s2b"]:
            self.mutate(
                "exact-interface-strong-" + direction + "-leak-sends.pvl",
                " out(c,plaintext);",
                "",
                2,
            )
            self.mutate(
                "exact-interface-strong-" + direction + "-ungated-sends.pvl",
                "let eligible=true",
                "let eligible=false",
                2,
            )
            self.mutate(
                "exact-interface-strong-" + direction + "-leak.pv",
                "attacker(m)",
                "attacker(SERVER_IDENTITY_SECRET)",
            )

    def test_analysis_annotations_and_fresh_draw_order(self):
        filename = "exact-interface-strong-registration.pvl"
        self.mutate(
            filename,
            "new ephemeral_secret[]: bitstring;",
            "new ephemeral_secret: bitstring;",
        )
        self.mutate(
            filename, "new kem_coins[]: bitstring;", "new kem_coins: bitstring;"
        )
        for direction in ["b2s", "s2b"]:
            self.mutate(
                "exact-interface-strong-" + direction + "-sends.pvl",
                " [precise]",
                "",
                2,
            )
            self.mutate(
                "exact-interface-strong-" + direction + ".pv",
                "nounif x:bitstring,y:bitstring; attacker(choice[x25519_public(x),x25519_public(y)]).",
                "",
            )

    def test_roster_classes_bound_kind_and_source_fail_closed(self):
        for index, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(
                    CHECKER.TARGETS[:index] + CHECKER.TARGETS[index + 1 :]
                )
            for change in [
                dict(cls="definitional"),
                dict(bound=2),
                dict(kind="unknown"),
                dict(result="Observational equivalence cannot be proved."),
            ]:
                changed = list(CHECKER.TARGETS)
                changed[index] = replace(target, **change)
                with self.assertRaises(ValueError):
                    CHECKER.validate_targets(changed)
        self.mutate(
            "record-origin-kr3.pvl",
            "L2Recv3,L2RecvStop",
            "L2Recv3,L2Recv3",
            comparison=False,
        )
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            for name in CHECKER.SOURCE_SHA256:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE.parents[2] / name, path)
            path = root / "beaconcrypt/src/server.rs"
            path.write_text(path.read_text() + "\n// changed source\n")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(source_root=root)

    def test_exact_verdict_and_trace_classes(self):
        for target in CHECKER.TARGETS:
            trace = "A trace has been found.\n" * target.expected_traces()
            summary = (
                target.result
                if target.kind == "equivalence"
                else "Query " + target.result
            )
            output = (
                "RESULT "
                + target.result
                + "\n"
                + trace
                + "Verification summary:\n"
                + summary
                + "\n"
            )
            CHECKER.check_output(output, target)
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
                    CHECKER.check_output(bad, target)


if __name__ == "__main__":
    unittest.main()
