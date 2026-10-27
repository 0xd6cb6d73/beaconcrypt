#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for the provenance interface, rule audit and exact verdicts."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "registration_provenance_checker",
    Path(__file__).with_name("check-registration-provenance.py"),
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ProvenanceChecks(unittest.TestCase):
    def fixture(self, directory):
        for name in set(CHECKER.THEORY.FILES) | set(CHECKER.TOKEN_SHA256):
            target = directory / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(CHECKER.HERE / name, target)

    def mutate(self, filename, old, new, *, theory_only=False):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            self.fixture(directory)
            path = directory / filename
            text = path.read_text()
            self.assertEqual(text.count(old), 1)
            path.write_text(text.replace(old, new, 1))
            with self.assertRaises(ValueError):
                if theory_only:
                    CHECKER.THEORY.audit(directory)
                else:
                    CHECKER.validate_targets(directory=directory)

    def test_complete_manifest_and_rule_inventory(self):
        CHECKER.validate_targets()
        result = CHECKER.THEORY.audit()
        self.assertEqual(len(result["reductions"]), 28)
        self.assertEqual(len(result["data_constructors"]), 44)
        self.assertEqual(
            [t.cls for t in CHECKER.TARGETS],
            ["security"] * 3 + ["witness"] + ["negative-control"] * 2,
        )

    def test_publication_must_be_single_use(self):
        self.mutate(
            "registration-provenance.pvl",
            " | ProvPublishRound(owner_handle, owner_seed)\n",
            " | !ProvPublishRound(owner_handle, owner_seed)\n",
        )

    def test_exact_source_purpose_tag(self):
        self.mutate(
            "registration-provenance.pvl",
            "sign(tag_x25519_one_time(publication_one_time), publish_seed)",
            "sign(tag_x25519_prekey(publication_one_time), publish_seed)",
        )

    def test_dh_reply_must_not_disclose_identity(self):
        self.mutate(
            "registration-provenance.pvl",
            "prov_reply(dh_call, dh_server_result)",
            "prov_reply(dh_call, dh_seed)",
        )

    def test_observer_keeps_actual_validation(self):
        self.mutate(
            "registration-provenance.pvl",
            "= registration_set_verify(observe_raw) in (",
            "= unreviewed_verify(observe_raw) in (",
        )

    def test_no_honest_target_premise_added_to_query(self):
        self.mutate(
            "registration-provenance-a2.pv",
            " event(ProvAccepted(",
            " event(ProvAllocated(candidate_key)) && event(ProvAccepted(",
        )

    def test_roster_and_classes_cannot_drift(self):
        for i, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(CHECKER.TARGETS[:i] + CHECKER.TARGETS[i + 1 :])
            changed = list(CHECKER.TARGETS)
            changed[i] = replace(target, cls="definitional")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(changed)

    def test_reduction_cannot_unprotect_identity(self):
        self.mutate(
            "crypto.pvl",
            "fun ed_public(bitstring): bitstring.",
            "fun ed_public(bitstring): bitstring.\nreduc forall key: bitstring; unsafe_reveal(ed_public(key)) = key.",
            theory_only=True,
        )

    def test_barrier_cannot_gain_data_projection(self):
        self.mutate(
            "crypto.pvl",
            "fun sign(bitstring, bitstring): bitstring.",
            "fun sign(bitstring, bitstring): bitstring [data].",
            theory_only=True,
        )

    def test_reduction_cannot_create_signature(self):
        self.mutate(
            "crypto.pvl",
            "fun sign(bitstring, bitstring): bitstring.",
            "fun sign(bitstring, bitstring): bitstring.\nreduc forall key: bitstring; unsafe_sign(key) = sign(key,key).",
            theory_only=True,
        )

    def test_equations_require_separate_analysis(self):
        self.mutate(
            "crypto.pvl",
            "fun ed_public(bitstring): bitstring.",
            "fun ed_public(bitstring): bitstring.\nequation forall key: bitstring; ed_public(key) = key.",
            theory_only=True,
        )

    def test_source_boundary_drift_requires_review(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            for name in CHECKER.SOURCE_SHA256:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE.parents[2] / name, root / name)
            with (root / "beaconcrypt/src/beacon.rs").open("a") as stream:
                stream.write(
                    "\n// changed source requires a new correspondence review\n"
                )
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(source_root=root)

    def test_exact_results_and_control_traces(self):
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
                output + "Warning: unreviewed process\n",
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
