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

    def mutate_source(self, old, new):
        path = CHECKER.HERE.parents[2] / "beaconcrypt/src/server.rs"
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
            "if auth::public_key_hash(&self.mldsa_public_key())? != authentication.server_hash",
            "if false && auth::public_key_hash(&self.mldsa_public_key())? != authentication.server_hash",
        )

    def test_response_uses_accepted_request_hash(self):
        self.mutate_source(
            "auth::response_transcript_hash(&authentication.init_hash, &response)",
            "auth::response_transcript_hash(&[0; 64], &response)",
        )

    def test_response_signer_role_preserved(self):
        self.mutate_source(
            "self.mldsa_identity.sign(AuthRole::Server, &hash)",
            "self.mldsa_identity.sign(AuthRole::Beacon, &hash)",
        )

    def test_complete_signed_encoding_preserved(self):
        self.mutate_source(
            "signature: &signature,\n\t\t\t..response",
            "signature: &[],\n\t\t\t..response",
        )

    def test_peer_map_key_preserved(self):
        self.mutate_source(
            "let old = self.known_ids.insert(\n\t\t\tremote_kid,",
            "let old = self.known_ids.insert(\n\t\t\tself.identity_key_kid,",
        )

    def test_peer_auth_hash_preserved(self):
        self.mutate_source(
            "EstablishedRemote::new(public_key, ratchet, authentication.beacon_hash)",
            "EstablishedRemote::new(public_key, ratchet, authentication.server_hash)",
        )

    def test_signing_precedes_commit(self):
        old = "let signature = self.mldsa_identity.sign(AuthRole::Server, &hash)?;"
        commit = "let (next_control, established_peer) = verified_pqxdh::server_commit(candidate);"
        self.mutate_source(old, commit + "\n\t\t" + old)


if __name__ == "__main__":
    unittest.main()
