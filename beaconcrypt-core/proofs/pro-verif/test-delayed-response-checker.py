#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regressions for the delayed origin projection and exact verifier gate."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "delayed_response_checker", Path(__file__).with_name("check-delayed-response.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class DelayedResponseChecks(unittest.TestCase):
    def fixture(self, directory):
        for name in CHECKER.TOKEN_SHA256:
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(CHECKER.HERE / name, target)

    def mutate(self, filename, old, new, *, comparison_only=False):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            self.fixture(directory)
            path = directory / filename
            text = path.read_text()
            self.assertEqual(text.count(old), 1)
            path.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                if comparison_only:
                    CHECKER.MODELS.validate(directory)
                else:
                    CHECKER.validate_targets(directory=directory)

    def test_exact_manifest_and_retained_finish(self):
        CHECKER.validate_targets()
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS],
            ["security"] * 2
            + ["witness", "differential-control", "negative-control"]
            + ["differential-control", "negative-control"],
        )
        self.assertEqual(sum(len(t.results) for t in CHECKER.TARGETS), 9)

    def test_assigned_id_counterfactual_changes_only_the_two_ad_fields(self):
        for filename in ("delayed-response-wrong-binding.pvl", "delayed-response.pvl"):
            with self.subTest(filename):
                source = (CHECKER.HERE / filename).read_text()
                derived = CHECKER.MODELS.ad_omits_assigned_id(source)
                constant = CHECKER.MODELS.COUNTERFACTUAL_ASSIGNED
                self.assertEqual(
                    derived.replace(constant + ") in", "assigned) in", 1)
                    .replace(constant + "\n  ) in", "assigned_key_id\n  ) in", 1)
                    .replace(
                        "(* Counterfactual control only: the transcript AD omits the assigned ID. *)\n"
                        f"const {constant}: key_id.\n",
                        "",
                    ),
                    source,
                )
                with self.assertRaises(ValueError):
                    CHECKER.MODELS.ad_omits_assigned_id(derived)
                with self.assertRaises(ValueError):
                    CHECKER.MODELS.ad_omits_assigned_id(
                        source.replace(
                            "ciphertext,assigned) in", "ciphertext,root) in", 1
                        )
                    )

    def test_counterfactual_pair_differs_only_in_the_binding_check(self):
        targets = {target.name: target for target in CHECKER.TARGETS}
        positive = targets["A1-delayed-ad-omits-assigned-id"]
        negative = targets["A1-C-binding-ad-omits-assigned-id"]
        self.assertEqual(
            positive.libraries()[-1], CHECKER.MODELS.COUNTERFACTUAL_BINDING_LIBRARY
        )
        self.assertEqual(
            negative.libraries()[-1], CHECKER.MODELS.COUNTERFACTUAL_LIBRARY
        )
        self.assertEqual(positive.libraries()[:-1], negative.libraries()[:-1])
        self.assertEqual(positive.query, targets["A1-delayed"].query)
        self.assertEqual(positive.results, targets["A1-delayed"].results)
        self.assertEqual(positive.process, targets["A1-delayed"].process)
        self.assertEqual(
            negative.results[0].replace(" is false.", " is true."), positive.results[0]
        )

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
        self.mutate("delayed-response.pvl", " !in(c,a1_accept(", " in(c,a1_accept(")
        self.mutate("delayed-response.pvl", " in(c, a1_build(", " !in(c, a1_build(")

    def test_binding_and_actual_builder_id_cannot_be_erased(self):
        self.mutate("delayed-response.pvl", " && builder_id = accepted_id", "")
        self.mutate(
            "delayed-response.pvl",
            "event FsServerCommitted(builder,",
            "event FsServerCommitted(token,",
        )
        self.mutate(
            "delayed-response.pvl",
            "key_id_encoding(assigned)) in\n   let frame",
            "key_id_encoding(fs_kid(1))) in\n   let frame",
        )

    def test_disclosure_boundary_and_public_handle_do_not_drift(self):
        self.mutate(
            "delayed-response.pvl",
            "out(c,(ratchet_next(server_to_beacon_chain(root)),beacon_to_server_chain(root)))",
            "out(c,(server_to_beacon_chain(root),beacon_to_server_chain(root)))",
        )
        self.mutate("delayed-response.pvl", "a1_some(token)", "a1_some((token,root))")

    def test_complete_finish_comparator_rejects_guard_and_plaintext_changes(self):
        self.mutate(
            "delayed-response.pvl",
            "if frame_sequence = fs_seq(1) then",
            "if true then",
            comparison_only=True,
        )
        self.mutate(
            "delayed-response.pvl",
            "a1_some(application_payload)",
            "a1_some(response)",
            comparison_only=True,
        )

    def test_control_changes_only_binding_guard(self):
        self.mutate(
            "delayed-response-wrong-binding.pvl",
            "if frame_sequence = fs_seq(1) then",
            "if true then",
            comparison_only=True,
        )

    def test_query_keeps_full_origin_and_injectivity(self):
        self.mutate(
            "delayed-response-a1.pv",
            "inj-event(FsBeaconEstablished",
            "event(FsBeaconEstablished",
            comparison_only=True,
        )

    def test_complete_roster_and_classes(self):
        for i, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(CHECKER.TARGETS[:i] + CHECKER.TARGETS[i + 1 :])
            changed = list(CHECKER.TARGETS)
            changed[i] = replace(target, cls="definitional")
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
