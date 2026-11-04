#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for complete original seal-dispatcher reification."""

import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import lift_adapter_seal_requests as lift


class SealLift(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (lift.ROOT / lift.SOURCE).read_bytes()

    def rejects(self, before, after):
        self.assertIn(before, self.source)
        changed = self.source.replace(before, after, 1)
        self.assertNotEqual(changed, self.source)
        with self.assertRaises(ValueError):
            lift.transform(changed)

    def test_exact_original_source_and_provenance(self):
        generated = lift.transform(self.source).decode()
        self.assertIn("def execute\n", generated)
        self.assertIn("Lifted.key request.key", generated)
        self.assertIn("Lifted.nonce request.nonce", generated)
        self.assertIn(
            "Lifted.join (E := E) (Array.make 2#usize [ s, application ])", generated
        )
        self.assertEqual(generated.count("Operations.aead (E := E)"), 2)
        self.assertEqual(generated.count("Lifted.tag"), 2)
        self.assertEqual(generated.count("Lifted.fromResidual"), 6)
        self.assertIn(hashlib.sha256(self.source).hexdigest(), generated)
        self.assertIn(
            hashlib.sha256(Path(lift.__file__).read_bytes()).hexdigest(), generated
        )
        self.assertIn("set_option warningAsError true", generated)

    def test_reject_key_operand_drift(self):
        self.rejects(b"request.key", b"request.nonce")

    def test_reject_nonce_conversion_drift(self):
        self.rejects(b"CoreConvertFromArrayU812", b"CoreConvertFromArrayU832")

    def test_reject_associated_data_drift(self):
        self.rejects(b"request.associated_data", b"request.key")

    def test_reject_single_plaintext_drift(self):
        self.rejects(
            b"plaintext (core.option.Option.Some s) nonce key",
            b"s (core.option.Option.Some s) nonce key",
        )

    def test_reject_prefixed_join_order_drift(self):
        self.rejects(
            b"Array.make 2#usize [ s, application ]",
            b"Array.make 2#usize [ application, s ]",
        )

    def test_reject_omitted_application(self):
        self.rejects(
            b"Array.make 2#usize [ s, application ]", b"Array.make 2#usize [ s, s ]"
        )

    def test_reject_join_replaced_with_unconditional_success(self):
        self.rejects(
            b"ratchet.join_record_parts (Array.make 2#usize [ s, application ])",
            b"pure (core.option.Option.Some application)",
        )

    def test_reject_extra_aead_before_join(self):
        self.rejects(
            b"let o \xe2\x86\x90 ratchet.join_record_parts",
            b"let _ \xe2\x86\x90 beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf.encrypt_detached application .None nonce key\n    let o \xe2\x86\x90 ratchet.join_record_parts",
        )

    def test_reject_wrapper_creation_omission(self):
        self.rejects(b"zeroize.Zeroizing.new", b"pure")

    def test_reject_wrapper_deref_omission(self):
        self.rejects(b"zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref", b"pure")

    def test_reject_tag_width_drift(self):
        self.rejects(
            b"16#usize core.U8.Insts.CoreMarkerCopy",
            b"32#usize core.U8.Insts.CoreMarkerCopy",
        )

    def test_reject_tag_success_drift(self):
        self.rejects(b"Some (ciphertext, val1)", b"Some (tag, val1)")

    def test_reject_aead_failure_becoming_success(self):
        self.rejects(
            b"core.result.Result.ok r",
            b"pure (core.option.Option.Some (application, application))",
        )

    def test_reject_failure_branch_omission(self):
        self.rejects(
            b"core.ops.control_flow.ControlFlow.Break residual",
            b"core.ops.control_flow.ControlFlow.Break ignored",
        )

    def test_reject_extra_or_missing_source_declaration(self):
        for changed in (
            self.source + b"\ndef fabricated := True\n",
            self.source.replace(
                lift.DECLARATION.encode(), b"def ratchet.other_seal\n", 1
            ),
        ):
            with self.assertRaises(ValueError):
                lift.transform(changed)

    def test_reject_unchecked_obligation(self):
        with self.assertRaises(ValueError):
            lift.transform(self.source + b"\naxiom desired_source : True\n")

    def test_exact_leaf_multiplicities(self):
        wrong = list(lift.REPLACEMENTS)
        before, after, count = wrong[0]
        wrong[0] = before, after, count + 1
        with patch.object(lift, "REPLACEMENTS", wrong):
            with self.assertRaisesRegex(ValueError, "multiplicity"):
                lift.transform(self.source)

    def test_reject_unlifted_standard_operation(self):
        changed = [
            entry for entry in lift.REPLACEMENTS if entry[0] != "core.result.Result.ok"
        ]
        with patch.object(lift, "REPLACEMENTS", changed):
            with self.assertRaisesRegex(ValueError, "unlifted"):
                lift.transform(self.source)

    def test_reject_omitted_residual_lift(self):
        with patch.object(lift, "RESIDUAL", lift.re.compile("no_such_residual")):
            with self.assertRaisesRegex(ValueError, "residual branch"):
                lift.transform(self.source)

    def test_reject_omitted_tag_lift(self):
        with patch.object(lift, "TAG", lift.re.compile("no_such_tag")):
            with self.assertRaisesRegex(ValueError, "tag conversion"):
                lift.transform(self.source)

    def test_check_rejects_full_output_drift_without_mutation(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-lift-control-") as directory:
            output = Path(directory) / "output.lean"
            malformed = lift.transform(self.source) + b"\naxiom desired_source : True\n"
            output.write_bytes(malformed)
            result = subprocess.run(
                [
                    sys.executable,
                    str(Path(lift.__file__)),
                    "--check",
                    "--output",
                    str(output),
                ],
                capture_output=True,
                timeout=15,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(output.read_bytes(), malformed)

    def test_combined_modes_cannot_mutate_output(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-lift-modes-") as directory:
            output = Path(directory) / "output.lean"
            output.write_bytes(b"preserve\n")
            result = subprocess.run(
                [
                    sys.executable,
                    str(Path(lift.__file__)),
                    "--check",
                    "--write",
                    "--output",
                    str(output),
                ],
                capture_output=True,
                timeout=15,
            )
            self.assertEqual(result.returncode, 2)
            self.assertEqual(output.read_bytes(), b"preserve\n")


if __name__ == "__main__":
    unittest.main()
