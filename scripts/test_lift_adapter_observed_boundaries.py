#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Keep both private observer holes tied to the complete extracted public bodies."""

from contextlib import redirect_stdout
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import lift_adapter_build_observed as build
import lift_adapter_finish_observed as finish


class ObservedBoundaryTests(unittest.TestCase):
    modules = (build, finish)

    def render_source(self, module, text):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "source.lean"
            source.write_text(text)
            with patch.object(module, "SOURCE", source):
                return module.render()

    def test_current_complete_body_matches_reviewed_output(self):
        for module in self.modules:
            with self.subTest(body=module.NAME):
                self.assertEqual(module.render(), module.TARGET.read_text())

    def test_outer_source_changes_are_retained_and_invalidate_output(self):
        for module, field in ((build, "self.known_ids"), (finish, "self.state")):
            with self.subTest(body=module.NAME):
                text = module.SOURCE.read_text()
                start = text.index(module.NAME)
                branch = text.index(module.BRANCH, start)
                position = text.index(field, start, branch)
                changed = text[:position] + text[position:].replace(
                    field, field + "_changed", 1
                )
                result = self.render_source(module, changed)
                self.assertIn(field + "_changed", result)
                self.assertNotEqual(result, module.TARGET.read_text())

    def test_duplicate_observer_hole_is_rejected(self):
        for module in self.modules:
            with self.subTest(body=module.NAME):
                text = module.SOURCE.read_text()
                position = text.index(module.BRANCH, text.index(module.NAME))
                changed = text[:position] + module.BRANCH + text[position:]
                with self.assertRaisesRegex(ValueError, "exactly one"):
                    self.render_source(module, changed)

    def test_removed_actual_kdf_in_hole_is_rejected(self):
        for module in self.modules:
            with self.subTest(body=module.NAME):
                text = module.SOURCE.read_text()
                branch = text.index(module.BRANCH, text.index(module.NAME))
                position = text.index("ratchet_initial_ratchet_hkdf", branch)
                changed = text[:position] + text[position:].replace(
                    "ratchet_initial_ratchet_hkdf", "omitted_initial_kdf", 1
                )
                with self.assertRaisesRegex(ValueError, "subtree changed"):
                    self.render_source(module, changed)

    def test_check_rejects_stale_output_without_writing(self):
        for module in self.modules:
            with self.subTest(body=module.NAME):
                with tempfile.TemporaryDirectory() as directory:
                    target = Path(directory) / "observed.lean"
                    target.write_text(module.render() + "\n-- stale\n")
                    original = target.read_bytes()
                    with patch.object(module, "TARGET", target):
                        with patch("sys.argv", ["observer", "--check"]):
                            with redirect_stdout(io.StringIO()):
                                with self.assertRaisesRegex(SystemExit, "differs"):
                                    module.main()
                    self.assertEqual(target.read_bytes(), original)


if __name__ == "__main__":
    unittest.main()
