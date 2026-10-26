#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject misleading or incomplete admission-verification receipts."""

import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "registration_set_checker", Path(__file__).with_name("check-registration-set.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.query = CHECKER.PRIMARY[0]
        self.result = self.query + " is true."
        self.output = (
            "RESULT "
            + self.result
            + "\nVerification summary:\nQuery "
            + self.result
            + "\n"
        )

    def check(self, output):
        CHECKER.check_output(output, [self.query], ["true"], 0)

    def test_complete(self):
        self.check(self.output)

    def test_missing_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("RESULT " + self.result + "\n", ""))

    def test_changed_event_argument(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("attempt_1", "other_attempt"))

    def test_changed_polarity(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("is true.", "is false."))

    def test_summary_disagrees(self):
        with self.assertRaises(ValueError):
            self.check(
                self.output.replace(
                    "Query " + self.result, "Query " + self.query + " is false."
                )
            )

    def test_extra_primary(self):
        with self.assertRaises(ValueError):
            self.check("RESULT " + self.result + "\n" + self.output)

    def test_missing_reconstructed_trace(self):
        query = CHECKER.REACHABLE[0]
        output = f"RESULT {query} is false.\nVerification summary:\nQuery {query} is false.\n"
        with self.assertRaises(ValueError):
            CHECKER.check_output(output, [query], ["false"], 1)
        CHECKER.check_output(
            "A trace has been found.\n" + output, [query], ["false"], 1
        )

    def test_unknown_is_not_true(self):
        with self.assertRaises(ValueError):
            self.check(self.output.replace("is true.", "cannot be proved."))

    def test_source_mapping_order(self):
        CHECKER.check_source_order()

    def test_control_anchor_not_duplicated(self):
        with self.assertRaises(ValueError):
            CHECKER.exact_replace("guard guard", "guard", "changed")


class InterpretedAdmissionSourceGate(unittest.TestCase):
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

    def test_request_field_projection_cannot_swap_signed_roles(self):
        self.mutate_source(
            "beaconcrypt/src/server.rs",
            "registration.pre_key,\n\t\t\tregistration.one_time_key,",
            "registration.one_time_key,\n\t\t\tregistration.pre_key,",
        )

    def test_private_one_time_handle_is_selected_for_the_last_dh(self):
        self.mutate_source(
            "beaconcrypt/src/pqxdh.rs",
            "DhSecretRole::BeaconOneTime => keys.beacon_one_time.map(|key| key.as_bytes())",
            "DhSecretRole::BeaconOneTime => keys.beacon_prekey.map(|key| key.as_bytes())",
        )

    def test_root_kdf_uses_the_retained_domain(self):
        self.mutate_source(
            "beaconcrypt/src/pqxdh.rs",
            "expand(32, Some(request.info), &prk)",
            "expand(32, Some(verified_pqxdh::SYM_RATCHET_INFO), &prk)",
        )

    def test_root_reply_is_the_actual_primitive_output(self):
        self.mutate_source(
            "beaconcrypt/src/pqxdh.rs",
            "expanded.as_slice().try_into().ok()",
            "Some([0; 32])",
        )

    def test_consumed_root_input_is_cleared_before_publication(self):
        self.mutate_source(
            "beaconcrypt-core/src/agreement.rs",
            "pending.root_key_input_mut().clear()",
            "()",
        )

    def test_ed_checks_start_with_the_existing_pq_verification(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "stage: SignedKeyStage::PqKey,",
            "stage: SignedKeyStage::PreKey,",
        )

    def test_signature_interpreter_uses_the_exact_request_context(self):
        self.mutate_source(
            "beaconcrypt/src/auth.rs",
            "request.input,\n\t\t&request.context,",
            "request.input,\n\t\t&[0; 32],",
        )

    def test_record_sealing_uses_the_exact_associated_data(self):
        self.mutate_source(
            "beaconcrypt/src/ratchet.rs",
            "encrypt_detached(\n\t\tplaintext,\n\t\tSome(request.associated_data.as_slice()),",
            "encrypt_detached(\n\t\tplaintext,\n\t\tNone,",
        )

    def test_record_opening_uses_the_exact_associated_data(self):
        self.mutate_source(
            "beaconcrypt/src/ratchet.rs",
            "decrypt(\n\t\trequest.ciphertext,\n\t\tSome(request.associated_data.as_slice()),",
            "decrypt(\n\t\trequest.ciphertext,\n\t\tNone,",
        )

    def test_commitment_is_hashed_before_its_secret_transcript_is_erased(self):
        self.mutate_source(
            "beaconcrypt/src/ratchet.rs",
            "crypto_generichash::generichash(transcript.as_bytes(), None, COMMITMENT_SIZE).ok();\n\ttranscript.as_mut_bytes().zeroize();",
            "{ transcript.as_mut_bytes().zeroize(); crypto_generichash::generichash(transcript.as_bytes(), None, COMMITMENT_SIZE).ok() };",
        )

    def test_record_write_parts_cannot_swap_tag_and_commitment(self):
        self.mutate_source(
            "beaconcrypt-core/src/record_effects.rs",
            "self.tag.as_slice(),\n\t\t\tself.commitment.as_slice(),",
            "self.commitment.as_slice(),\n\t\t\tself.tag.as_slice(),",
        )

    def test_commitment_gate_remains_before_aead(self):
        self.mutate_source(
            "beaconcrypt-core/src/record.rs",
            "if !commitment_matches {",
            "if false && !commitment_matches {",
        )

    def test_record_rejection_finishes_with_the_actual_none_reply(self):
        self.mutate_source(
            "beaconcrypt-core/src/record_effects.rs",
            "pending.finish(None)",
            "pending.finish(Some(()))",
        )

    def test_whole_record_callback_cannot_return(self):
        self.mutate_source(
            "beaconcrypt-core/src/registration.rs",
            "pub struct CompletedBeacon<'a> {",
            "pub struct InitialOpened;\npub struct CompletedBeacon<'a> {",
        )


if __name__ == "__main__":
    unittest.main()
