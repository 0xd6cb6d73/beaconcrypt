#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject drift in moved-token lifetime, full response tail and result scope."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "pending_checker", Path(__file__).with_name("check-pending-registration.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class PendingTests(unittest.TestCase):
    def test_manifest(self):
        CHECKER.validate_targets()
        self.assertEqual(len(CHECKER.TARGETS), 4)
        self.assertEqual(sum(t.cls == "security" for t in CHECKER.TARGETS), 0)

    def mutate_model(self, filename, old, new, check):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for name in (
                "registration-set-response.pvl",
                "fs-pending-response.pvl",
                "fs-pending-registration.pvl",
                CHECKER.NORMAL,
                CHECKER.CONTROL,
            ):
                shutil.copy(CHECKER.HERE / name, directory / name)
            path = directory / filename
            before = path.read_text()
            self.assertIn(old, before)
            path.write_text(before.replace(old, new, 1))
            with self.assertRaises(ValueError):
                check(directory)

    def test_no_second_use_in_real_model(self):
        self.mutate_model(
            CHECKER.NORMAL, "= false.", "= true.", CHECKER.check_token_service
        )

    def test_reuse_control_is_different(self):
        self.mutate_model(
            CHECKER.CONTROL, "= true.", "= false.", CHECKER.check_token_service
        )

    def test_origin_does_not_gate_lookup(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "get sched_pending(=token, origin: bitstring",
            "get sched_pending(=token, =owner",
            CHECKER.check_token_service,
        )

    def test_consumption_not_dropped(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "event SchedTokenConsumed(owner, token);",
            "",
            CHECKER.check_token_service,
        )

    def test_consumption_precedes_binding(self):
        before = "event SchedTokenConsumed(owner, token);"
        self.mutate_model(
            "fs-pending-registration.pvl",
            before,
            "if server_identity = ed_public(SERVER_IDENTITY_SECRET) then " + before,
            CHECKER.check_token_service,
        )

    def test_exhaustion_keeps_consumption(self):
        before = "event SchedTokenConsumed(owner, token);"
        self.mutate_model(
            "fs-pending-registration.pvl",
            before,
            "if counter < limit then " + before,
            CHECKER.check_token_service,
        )

    def test_spent_reply_is_none(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "let SchedSpent(lease: channel) =",
            "let SchedSpent(lease: channel) = SchedConsume(lease);",
            CHECKER.check_token_service,
        )

    def test_current_builder_routed(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "out(lease, (owner, data, failure_stage",
            "out(lease, (origin, data, failure_stage",
            CHECKER.check_token_service,
        )

    def test_attempt_caps_are_separate(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "if builds < build_cap then",
            "if accepts < build_cap then",
            CHECKER.check_token_service,
        )

    def test_request_reply_correlation(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "out(c, sched_reply(request, reply))",
            "out(c, reply)",
            CHECKER.check_token_service,
        )

    def test_exact_next_chain(self):
        self.mutate_model(
            "fs-pending-response.pvl",
            "ratchet_next(send_chain)",
            "send_chain",
            CHECKER.check_tail,
        )

    def test_call_label_preserved(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "let sched_call(call_id: bitstring, operation: bitstring) = request in",
            "let operation = request in",
            CHECKER.check_token_service,
        )

    def test_root_not_returned_as_handle(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "sched_some_token(token)",
            "sched_some_token(root)",
            CHECKER.check_publication,
        )

    def test_root_not_separately_exposed(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "event SchedTokenCreated(owner, token);",
            "event SchedTokenCreated(owner, token); out(c, root);",
            CHECKER.check_publication,
        )

    def test_accepting_owner_preserved(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "insert sched_pending(token, owner, server_identity",
            "insert sched_pending(token, raw, server_identity",
            CHECKER.check_publication,
        )

    def test_pending_publication_after_consumed(self):
        self.mutate_model(
            "fs-pending-registration.pvl",
            "insert registration_set_consumed(owner, rid);",
            "",
            CHECKER.check_publication,
        )

    def test_exact_ad_order(self):
        self.mutate_model(
            "fs-pending-response.pvl",
            "build_associated_data(server_identity, beacon_identity)",
            "build_associated_data(beacon_identity, server_identity)",
            CHECKER.check_tail,
        )

    def test_preserves_source_default(self):
        self.mutate_model(
            "fs-pending-response.pvl",
            "registration_response_witness()",
            "registration_response_empty()",
            CHECKER.check_tail,
        )

    def test_no_security_class(self):
        targets = (replace(CHECKER.TARGETS[0], cls="security"),) + CHECKER.TARGETS[1:]
        with self.assertRaisesRegex(ValueError, "finite operational scope"):
            CHECKER.validate_targets(targets)

    def test_no_duplicate_target(self):
        with self.assertRaisesRegex(ValueError, "duplicate pending target"):
            CHECKER.validate_targets(CHECKER.TARGETS + CHECKER.TARGETS[:1])

    def test_no_missing_query(self):
        with self.assertRaisesRegex(ValueError, "query roster is incomplete"):
            CHECKER.validate_targets(CHECKER.TARGETS[1:])

    def test_no_control_as_real(self):
        targets = (
            replace(CHECKER.TARGETS[0], hooks=(CHECKER.CONTROL,)),
        ) + CHECKER.TARGETS[1:]
        with self.assertRaisesRegex(ValueError, "only the negative control"):
            CHECKER.validate_targets(targets)

    def test_normal_linearity_cannot_be_dropped(self):
        targets = CHECKER.TARGETS[:2] + CHECKER.TARGETS[3:]
        with self.assertRaisesRegex(ValueError, "exact four-target pending roster"):
            CHECKER.validate_targets(targets)

    def test_normal_linearity_cannot_be_replaced_by_witness(self):
        targets = (
            CHECKER.TARGETS[:2]
            + (replace(CHECKER.TARGETS[0], name="pending-OTHER"),)
            + CHECKER.TARGETS[3:]
        )
        with self.assertRaisesRegex(ValueError, "exact four-target pending roster"):
            CHECKER.validate_targets(targets)


class NativeMovedTokenSourceGate(unittest.TestCase):
    def test_current_authenticated_token(self):
        CHECKER.check_source()

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
                CHECKER.check_source()

    def test_private_auth_context_moves_with_token(self):
        self.mutate_source(
            "control: pending,\n\t\t\tauthentication,\n\t\t} = reg_out;",
            "control: pending,\n\t\t} = reg_out;",
        )

    def test_token_server_key_binding_preserved(self):
        self.mutate_source(
            "if !authentication.matches_server(&self.authentication_pin()?)",
            "if false && !authentication.matches_server(&self.authentication_pin()?)",
        )

    def test_size_preflight_stays_before_token_move(self):
        self.mutate_source(
            "registration_response_len(plaintext.len(), next_key_id)?;",
            "let RegistrationOutput { derived_secret, control: pending, authentication, } = reg_out;\n"
            "\t\tregistration_response_len(plaintext.len(), next_key_id)?;",
        )


if __name__ == "__main__":
    unittest.main()
