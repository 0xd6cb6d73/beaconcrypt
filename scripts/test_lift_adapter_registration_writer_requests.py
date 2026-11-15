#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Exact control/field-preserving lifting controls for both runtime writers."""

from pathlib import Path
import unittest
import lift_adapter_registration_writer_requests as lifting


class RegistrationWriterLifting(unittest.TestCase):
    def setUp(self):
        self.source = (lifting.ROOT / lifting.SOURCE).read_bytes()

    def test_reviewed_generated_output(self):
        self.assertEqual(
            lifting.transform(self.source),
            (lifting.ROOT / lifting.DESTINATION).read_bytes(),
        )

    def test_selected_two_bodies(self):
        output = lifting.transform(self.source).decode()
        self.assertEqual(output.count("def encodeInit\n"), 1)
        self.assertEqual(output.count("def encodeResponse\n"), 1)
        self.assertIn("Lifted.writeInit (E := E) val init", output)
        self.assertIn("Lifted.writeResponse (E := E) val response", output)
        self.assertIn("init.one_time_key", output)
        self.assertIn("response.key_id", output)

    def reject(self, before, after):
        changed = self.source.replace(before, after, 1)
        self.assertNotEqual(changed, self.source)
        with self.assertRaises(ValueError):
            lifting.transform(changed)

    def test_reject_changed_control_branch(self):
        self.reject(b"ControlFlow.Continue val", b"ControlFlow.Break val")

    def test_reject_changed_ml_field(self):
        self.reject(b"init.one_time_key", b"init.pq_key")

    def test_reject_reordered_field(self):
        self.reject(b"init.pre_key", b"init.one_time_key")

    def test_reject_omitted_capacity_gate(self):
        self.reject(
            b"beaconcrypt_core.transport.encoded_init_len", b"other.encoded_init_len"
        )

    def test_reject_changed_key_id(self):
        self.reject(b"response.key_id", b"0#u64")

    def test_reject_different_allocation_path(self):
        self.reject(
            b"wire.encode_record\n      wire.encode_response",
            b"wire.other\n      wire.encode_response",
        )

    def test_reject_missed_residual(self):
        self.reject(
            b"from_residual\n      (alloc.vec.Vec Std.U8) residual",
            b"from_residual\n      (alloc.vec.Vec Std.U8) other",
        )

    def test_reject_renamed_public_body(self):
        self.reject(b"def wire.encode_init\n", b"def wire.other_init\n")

    def test_reject_duplicate_public_body(self):
        with self.assertRaises(ValueError):
            lifting.transform(self.source + b"\ndef wire.encode_init\n")


if __name__ == "__main__":
    unittest.main()
