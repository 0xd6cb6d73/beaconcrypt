#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression tests for exact Beacon queries, alpha names and actual traces."""

import importlib.util
from pathlib import Path
import re
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "beacon_checker", HERE / "check-registration-beacon.py"
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


def output(queries, verdicts, traces=0):
    results = [
        query + (" cannot be proved." if verdict == "unknown" else f" is {verdict}.")
        for query, verdict in zip(queries, verdicts, strict=True)
    ]
    return "\n".join(
        [
            *("RESULT " + result for result in results),
            *("A trace has been found." for _ in range(traces)),
            "Verification summary:",
            *("Query " + result for result in results),
        ]
    )


class ExactBeaconGate(unittest.TestCase):
    def setUp(self):
        self.text = output(CHECKER.PRIMARY, CHECKER.VERDICTS)

    def check(self, text):
        CHECKER.check_output(text, CHECKER.PRIMARY, CHECKER.VERDICTS, 0)

    def test_valid_baseline(self):
        self.check(self.text)

    def test_alpha_names(self):
        renamed = re.sub(r"\b(owner|attempt)_2\b", r"\1_973", self.text)
        self.assertNotEqual(renamed, self.text)
        self.check(renamed)

    def test_repeated_variable_cannot_split(self):
        altered = self.text.replace(
            "RegistrationBeaconAttempt(owner_2", "RegistrationBeaconAttempt(owner_984"
        )
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_distinct_variables_cannot_merge(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("prior,raw_1", "attempt_2,raw_1"))

    def test_constructor_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("hkdf_second_32", "hkdf_first_32"))

    def test_target_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("first_sequence", "general_zero_sequence"))

    def test_cache_cannot_change(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("receive_cache_empty", "receive_cache_entry"))

    def test_missing_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[1])

    def test_duplicated_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[0] + "\n" + self.text)

    def test_missing_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("Verification summary:", ""))

    def test_duplicated_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text + "\nVerification summary:\n")

    def test_changed_summary(self):
        first, last = self.text.split("Verification summary:")
        with self.assertRaises(ValueError):
            self.check(
                first
                + "Verification summary:"
                + last.replace(" is true.", " is false.", 1)
            )

    def test_unknown_cannot_be_relabelled(self):
        for verdict in ["true", "false"]:
            with self.subTest(verdict=verdict), self.assertRaises(ValueError):
                self.check(self.text.replace(" cannot be proved.", f" is {verdict}."))

    def test_proof_cannot_be_unknown(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace(" is true.", " cannot be proved.", 1))

    def test_actual_traces_required(self):
        verdicts = CHECKER.control_cases()[0][2]
        text = output(CHECKER.TAIL, verdicts, verdicts.count("false"))
        CHECKER.check_output(text, CHECKER.TAIL, verdicts, verdicts.count("false"))
        for changed in [
            text.replace(
                "A trace has been found.",
                "A trace has been found, assuming a hypothesis:",
            ),
            text + "\nA trace has been found.\n",
        ]:
            with self.subTest(changed=changed[-80:]), self.assertRaises(ValueError):
                CHECKER.check_output(
                    changed, CHECKER.TAIL, verdicts, verdicts.count("false")
                )

    def test_warning_and_error_rejected(self):
        for notice in ["Warning: changed theory", "Error: bad model"]:
            with self.subTest(notice=notice), self.assertRaises(ValueError):
                self.check(notice + "\n" + self.text)

    def test_exact_mutation_anchor(self):
        for text in ["absent", "token token"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                CHECKER.BASE.exact_replace(text, "token", "replacement")

    def test_single_preparation_has_exact_two_anchors(self):
        original = (HERE / "registration-beacon-control.pv").read_text()
        changed = CHECKER.single_preparation(original)
        self.assertEqual(changed.count("RegistrationBeaconControlRetry("), 1)
        with self.assertRaises(ValueError):
            CHECKER.single_preparation(changed)

    def test_reviewed_source_and_plan_anchors(self):
        CHECKER.check_source_order()


class InterpretedBeaconSourceGate(unittest.TestCase):
    def mutate_source(self, relative, old, new):
        path = CHECKER.HERE.parents[2] / relative
        original = Path.read_text
        source = original(path)
        self.assertEqual(source.count(old), 1)
        changed = source.replace(old, new, 1)

        def read_text(candidate, *args, **kwargs):
            return (
                changed if candidate == path else original(candidate, *args, **kwargs)
            )

        with patch.object(Path, "read_text", read_text), self.assertRaises(ValueError):
            CHECKER.check_source_order()

    def test_initial_open_metadata_is_the_actual_record_result(self):
        self.mutate_source(
            "beaconcrypt-core/src/record.rs",
            "let seq = self.opening.sequence();",
            "let seq = 0;",
        )

    def test_private_one_time_handle_is_not_replaced_with_the_prekey(self):
        self.mutate_source(
            "beaconcrypt/src/beacon.rs",
            "beacon_one_time: Some(&onetime_key.secret_key),",
            "beacon_one_time: Some(&prekey.secret_key),",
        )

    def test_initial_application_suffix_is_nonempty(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "opened.plaintext.len() <= crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE",
            "opened.plaintext.len() < crate::pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE",
        )

    def test_first_sequence_gate_is_preserved(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "kernel,\n\t\t\t1,\n\t\t\tself.agreement.application_ciphertext,",
            "kernel,\n\t\t\t2,\n\t\t\tself.agreement.application_ciphertext,",
        )

    def test_post_dh_pin_rejection_is_not_moved_before_dh(self):
        old = "let pinned = binding.server_pin().binding();"
        self.mutate_source(
            "beaconcrypt-core/src/agreement.rs",
            old,
            old
            + "\n\tif response.identity_key != pinned.identity_public_key { return AgreementEffect::Rejected(Some(pqxdh::beacon_abort_init(control))); }",
        )

    def test_native_terminal_state_comes_from_the_pending_capability(self):
        self.mutate_source(
            "beaconcrypt/src/beacon.rs",
            "BeaconState::InitSent { pending, .. } => pending.aborted_state(),",
            "BeaconState::InitSent { pending, .. } => verified_pqxdh::BeaconAborted::new(0),",
        )

    def test_initial_open_sender_is_the_pinned_server(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "self.agreement.binding.associated_data(),\n\t\t\tself.agreement.candidate.server_key_id(),",
            "self.agreement.binding.associated_data(),\n\t\t\t0,",
        )

    def test_opened_sender_comes_from_the_record_capability(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "self.agreement.candidate,\n\t\t\topened.key_id,",
            "self.agreement.candidate,\n\t\t\t0,",
        )

    def test_commitment_hash_failure_cannot_admit_aead(self):
        self.mutate_source(
            "beaconcrypt/src/beacon.rs",
            "None => false,",
            "None => true,",
        )

    def test_commitment_comparison_uses_the_supplied_record_bytes(self):
        self.mutate_source(
            "beaconcrypt/src/beacon.rs",
            "memcmp(&commitment, pending.supplied_commitment())",
            "memcmp(&commitment, &commitment)",
        )

    def test_actual_aead_plaintext_is_the_only_completion_reply(self):
        self.mutate_source(
            "beaconcrypt/src/beacon.rs",
            "pending.finish(plaintext.as_deref())",
            "pending.finish(Some(&[0; 9]))",
        )

    def test_rejected_record_effect_aborts_the_retained_candidate(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "beacon_abort_candidate(agreement.candidate)",
            "BeaconAborted::new(0)",
        )


if __name__ == "__main__":
    unittest.main()
