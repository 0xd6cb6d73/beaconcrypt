#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Fail-closed regression tests for the production frame codec extraction."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location(
    "extract_frame_codec", Path(__file__).with_name("extract_frame_codec.py")
)
extraction = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(extraction)


class FrameCodecExtractionTests(unittest.TestCase):
    def test_policy_ignores_nested_comments_and_quoted_evidence(self):
        extraction.checked_lean(
            b"/- outer /- axiom injected : False -/ sorry -/\n"
            b'-- admit\nexample : String := "axiom \\"sorry\\""\n',
            "evidence",
        )
        for keyword in ("sorry", "admit", "axiom", "sorryAx", "opaque", "unsafe"):
            with self.subTest(keyword=keyword), self.assertRaises(ValueError):
                extraction.checked_lean(
                    f"/- harmless -/ {keyword} injected".encode(), "model"
                )

    def test_unterminated_comment_cannot_hide_executable_declaration(self):
        with self.assertRaises(ValueError):
            extraction.checked_lean(b"/- unterminated\naxiom injected : False", "model")

    def test_external_template_must_remain_empty(self):
        extraction.checked_template(
            b"import Aeneas\nopen Aeneas\n/- no obligations -/\n"
        )
        for declaration in (
            "axiom parser_correct : False",
            "@[simp] def parser_correct : Bool := true",
            "noncomputable def hidden := Classical.choice",
            "constant parser : Bool",
        ):
            with self.subTest(declaration=declaration), self.assertRaises(ValueError):
                extraction.checked_template(declaration.encode())

    def test_scratch_directory_cannot_overlap_source_checkout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "source"
            root.mkdir()
            for candidate in (root, root / "target", root.parent):
                with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                    extraction.isolated_work(candidate, root)

    def test_scratch_symlink_cannot_redirect_generated_outputs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "source"
            root.mkdir()
            work = Path(directory) / "work"
            work.mkdir()
            (work / "generated").symlink_to(root, target_is_directory=True)
            with self.assertRaises(ValueError):
                extraction.isolated_work(work, root)

    def test_hash_rosters_reject_added_omitted_and_malformed_evidence(self):
        baseline = {"one": "0" * 64}
        self.assertEqual(extraction.hash_roster(baseline, {"one"}, "test"), baseline)
        for value in (
            {},
            baseline | {"two": "0" * 64},
            {"one": "bad"},
            {"one": 3},
            None,
        ):
            with self.subTest(value=value), self.assertRaises(ValueError):
                extraction.hash_roster(value, {"one"}, "test")

    def test_partial_aeneas_success_with_placeholder_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = Path(directory)
            (generated / "Types.lean").write_text(
                "namespace beaconcrypt_parse\nend beaconcrypt_parse\n"
            )
            (generated / "FunsExternal_Template.lean").write_text("import Aeneas\n")
            (generated / "Funs.lean").write_text("def frame.decode := by sorry\n")
            with self.assertRaises(ValueError):
                extraction.assembled(generated)

    def test_body_omission_is_rejected_even_without_placeholder(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = Path(directory)
            (generated / "Types.lean").write_text(
                "namespace beaconcrypt_parse\nend beaconcrypt_parse\n"
            )
            (generated / "FunsExternal_Template.lean").write_text("import Aeneas\n")
            (generated / "Funs.lean").write_text("def frame.decode := true\n")
            with self.assertRaisesRegex(ValueError, "missing or duplicate"):
                extraction.assembled(generated)

    def test_stale_llbc_cannot_reach_aeneas_after_empty_success(self):
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            (work / "beaconcrypt_parse.llbc").write_bytes(b"old artifact")
            tools = {"charon": Path("charon"), "aeneas": Path("aeneas")}
            with patch.object(extraction.subprocess, "run") as runner:
                runner.return_value.returncode = 0
                with self.assertRaisesRegex(ValueError, "fresh nonempty"):
                    extraction.pipeline(tools, work)
                self.assertEqual(runner.call_count, 1)
                self.assertEqual(runner.call_args.args[0][0], "charon")


if __name__ == "__main__":
    unittest.main()
