#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression tests for exact query verdicts and real versus assumed traces."""

import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "response_checker", HERE / "check-registration-response.py"
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


class ExactResponseGate(unittest.TestCase):
    def setUp(self):
        self.queries = CHECKER.PRIMARY
        self.verdicts = ["true"] * 8
        self.text = output(self.queries, self.verdicts)

    def check(self, text):
        CHECKER.ADMISSION.check_output(text, self.queries, self.verdicts, 0)

    def test_valid_baseline(self):
        self.check(self.text)

    def test_missing_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[1])

    def test_duplicated_primary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.split("\n", 1)[0] + "\n" + self.text)

    def test_changed_query(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("before_1 + 1", "before_1 + 2"))

    def test_changed_primary_verdict(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace(" is true.", " cannot be proved.", 1))

    def test_changed_summary(self):
        first, last = self.text.split("Verification summary:")
        with self.assertRaises(ValueError):
            self.check(
                first
                + "Verification summary:"
                + last.replace(" is true.", " is false.", 1)
            )

    def test_missing_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text.replace("Verification summary:", ""))

    def test_duplicated_summary(self):
        with self.assertRaises(ValueError):
            self.check(self.text + "\nVerification summary:\n")

    def test_unknown_is_not_a_proof(self):
        with self.assertRaises(ValueError):
            self.check(output(self.queries, ["unknown"] * 8))

    def test_known_sensitivity_unknown(self):
        verdicts = ["unknown" if i in {1, 5} else "true" for i in range(8)]
        CHECKER.ADMISSION.check_output(
            output(self.queries, verdicts), self.queries, verdicts, 0
        )

    def test_finite_tail_requires_actual_traces(self):
        text = output(CHECKER.TAIL, ["false", "false", "true"], 2)
        CHECKER.ADMISSION.check_output(
            text, CHECKER.TAIL, ["false", "false", "true"], 2
        )
        with self.assertRaises(ValueError):
            CHECKER.ADMISSION.check_output(
                text.replace(
                    "A trace has been found.",
                    "A trace has been found, assuming the following hypothesis:",
                ),
                CHECKER.TAIL,
                ["false", "false", "true"],
                2,
            )

    def test_warning_cannot_pass(self):
        with self.assertRaises(ValueError):
            self.check("Warning: unexpected approximation\n" + self.text)


class NativeResponseSourceGate(unittest.TestCase):
    """Textual source controls retain the classical tail's explicit scope."""

    def test_current_signed_source(self):
        CHECKER.check_source_order()

    def mutate_source(self, old, new, relative="beaconcrypt/src/server.rs"):
        path = CHECKER.HERE.parents[2] / relative
        original = Path.read_text
        source = original(path)
        self.assertEqual(source.count(old), 1)
        changed = source.replace(old, new, 1)

        def read_text(candidate, *args, **kwargs):
            if candidate == path:
                return changed
            return original(candidate, *args, **kwargs)

        with patch.object(Path, "read_text", read_text):
            with self.assertRaises(ValueError):
                CHECKER.check_source_order()

    def test_token_server_key_binding_preserved(self):
        self.mutate_source(
            "if application.is_empty() || !agreement.binding.matches_server(current_pin)",
            "if application.is_empty() || false && !agreement.binding.matches_server(current_pin)",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_response_uses_accepted_request_hash(self):
        self.mutate_source(
            "build_response_prefix(\n\t\t\tself.state.binding.init_hash(),",
            "build_response_prefix(\n\t\t\t&[0; 64],",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_response_signer_role_preserved(self):
        self.mutate_source(
            "role: AuthRole::Server,\n\t\t\tpublic_key: self.binding.server_pin().public_key(),",
            "role: AuthRole::Beacon,\n\t\t\tpublic_key: self.binding.server_pin().public_key(),",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_complete_signed_encoding_preserved(self):
        self.mutate_source("signature: message.signature,", "signature: &[],")

    def test_peer_map_key_preserved(self):
        self.mutate_source(
            "let old = self.known_ids.insert(\n\t\t\tremote_kid,",
            "let old = self.known_ids.insert(\n\t\t\tself.identity_key_kid,",
        )

    def test_peer_binding_assignment_preserved(self):
        self.mutate_source(
            "self.binding.finish(self.candidate.key_id())",
            "self.binding.finish(0)",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_serialization_precedes_pure_commit(self):
        self.mutate_source(
            "let encoded = match encoded {\n\t\t\tSome(encoded) => encoded,\n\t\t\tNone => return Err(rejected),\n\t\t};",
            "let (next, _) = crate::pqxdh::server_commit(self.candidate);\n\t\tlet encoded = match encoded {\n\t\t\tSome(encoded) => encoded,\n\t\t\tNone => return Err(rejected),\n\t\t};",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_exact_record_request_interpreted(self):
        self.mutate_source(
            "self.candidate.key_id(),\n\t\t\tself.candidate.server_identity_key_id(),",
            "self.candidate.server_identity_key_id(),\n\t\t\tself.candidate.key_id(),",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_core_hash_parts_are_ordered(self):
        self.mutate_source(
            "HashRequest::Triple([&self.prefix, self.ciphertext, &self.assigned_id])",
            "HashRequest::Triple([&self.assigned_id, self.ciphertext, &self.prefix])",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_record_aead_reply_is_not_substituted(self):
        self.mutate_source(
            "pending.resume(detached_view).ok()?",
            "pending.resume(Some((&[], [0; 16]))).ok()?",
        )

    def test_record_hash_reply_is_not_substituted(self):
        self.mutate_source(
            "pending.resume(commitment).ok()?",
            "pending.resume(Some([0; 64])).ok()?",
        )

    def test_record_writer_reply_is_not_substituted(self):
        self.mutate_source(
            "pending.resume(ciphertext.as_deref()).ok()?",
            "pending.resume(Some(&[])).ok()?",
        )

    def test_written_record_length_is_checked_before_signing(self):
        self.mutate_source(
            "if ciphertext.len() != length {",
            "if false && ciphertext.len() != length {",
            "beaconcrypt-core/src/registration.rs",
        )

    def test_assigned_identifier_prefix_is_core_owned(self):
        self.mutate_source(
            "registration_key_id_binding(assigned_kid).as_bytes()",
            "registration_key_id_binding(sender_kid).as_bytes()",
            "beaconcrypt-core/src/record_effects.rs",
        )


if __name__ == "__main__":
    unittest.main()
