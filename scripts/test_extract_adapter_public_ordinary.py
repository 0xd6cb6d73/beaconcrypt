#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Source, layout and dynamic-leaf drift controls for ordinary SDK extraction."""

import json
import unittest
import extract_adapter_public_ordinary as extraction
import lift_adapter_public_ordinary_requests as lifting


class ExtractionTests(unittest.TestCase):
    def evidence(self):
        return json.loads((extraction.DESTINATION / "source-evidence.json").read_text())

    def test_installed_source_and_request(self):
        extraction.check_source()
        expected = lifting.transform((lifting.ROOT / lifting.SOURCE).read_bytes())
        self.assertEqual(expected, (lifting.ROOT / lifting.DESTINATION).read_bytes())

    def test_changed_source_put_rejected(self):
        raw = self.evidence()["raw"]["Funs.lean"].encode()
        changed = raw.replace(
            b"ratchet.RatchetKernelSlot.put rks kernel",
            b"ratchet.RatchetKernelSlot.put rks crk",
            1,
        )
        self.assertNotEqual(raw, changed)
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            extraction.normalize(changed, "Funs.lean")

    def test_missing_server_body_rejected(self):
        raw = self.evidence()["raw"]["Funs.lean"].encode()
        changed = raw.replace(
            b"def server.Server.decrypt_message\n", b"def server.Server.missing\n", 1
        )
        with self.assertRaisesRegex(ValueError, "missing"):
            extraction.require_roots(changed)

    def test_changed_driver_order_rejected(self):
        source = (lifting.ROOT / lifting.SOURCE).read_bytes()
        changed = source.replace(
            b"ratchet.execute_record_send crk context",
            b"ratchet.execute_record_send kernel context",
            1,
        )
        self.assertNotEqual(source, changed)
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            lifting.transform(changed)


if __name__ == "__main__":
    unittest.main()
