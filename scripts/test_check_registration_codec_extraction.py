#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD

"""Negative controls for the unfinished registration codec extraction checkpoint."""

from pathlib import Path
import tempfile
import unittest

import check_registration_codec_extraction as checkpoint


class RegistrationCodecCheckpointTests(unittest.TestCase):
    def generated(self, root: Path, cohort: str = "registration") -> Path:
        root.mkdir(parents=True, exist_ok=True)
        (root / "Types.lean").write_text(
            "namespace beaconcrypt_parse\nend beaconcrypt_parse\n"
        )
        (root / "Funs.lean").write_text(
            "\n".join(
                "def " + name.replace("::", ".") + " : Nat := 0"
                for name in checkpoint.COHORTS[cohort]
            )
        )
        (root / "FunsExternal_Template.lean").write_text("-- no external obligations\n")
        return root

    def test_commands_keep_all_reachable_bodies(self):
        tools = {name: Path("/tools") / name for name in ("charon", "aeneas")}
        for cohort, names in checkpoint.COHORTS.items():
            with self.subTest(cohort=cohort):
                charon, aeneas = checkpoint.commands(
                    tools, Path("/work"), cohort, False
                )
                self.assertEqual(
                    [arg for arg in charon if arg.startswith("--opaque=")],
                    ["--opaque=beaconcrypt_core"],
                )
                self.assertEqual(
                    [arg for arg in charon if arg.startswith("--start-from=")],
                    ["--start-from=beaconcrypt_parse::" + name for name in names],
                )
                self.assertIn("-abort-on-error", aeneas)

    def test_log_errors_cannot_pass_when_compiler_returns_zero(self):
        for log in (
            "[Error] unsupported nested borrow",
            "[\x1b[91mError\x1b[39m] unsupported operation",
            "Could not translate the body of validate_initkex",
            "Ignoring the body of preflight because of previous error",
        ):
            with self.subTest(log=log), self.assertRaises(ValueError):
                checkpoint.checked_diagnostics(log)

    def test_absent_and_duplicate_entry_points_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            functions = generated / "Funs.lean"
            original = functions.read_text()
            for bad in (
                original.replace("def decode_init : Nat := 0", ""),
                original + "\ndef decode_init : Nat := 0",
            ):
                functions.write_text(bad)
                with self.assertRaises(ValueError):
                    checkpoint.checked_output(generated, "registration")

    def test_incomplete_translation_placeholders_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            functions = generated / "Funs.lean"
            original = functions.read_text()
            for placeholder in (
                "sorry",
                "admit",
                "sorryAx",
                "axiom omitted : False",
                "opaque omitted : Nat",
            ):
                functions.write_text(original + "\n" + placeholder)
                with (
                    self.subTest(placeholder=placeholder),
                    self.assertRaises(ValueError),
                ):
                    checkpoint.checked_output(generated, "registration")

    def test_comment_cannot_stand_in_for_an_extracted_body(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            functions = generated / "Funs.lean"
            functions.write_text(
                functions.read_text().replace(
                    "def decode_init : Nat := 0", "/- def decode_init : Nat := 0 -/"
                )
            )
            with self.assertRaises(ValueError):
                checkpoint.checked_output(generated, "registration")

    def test_unresolved_core_or_parser_model_is_an_explicit_obligation(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            external = generated / "FunsExternal_Template.lean"
            for model in (
                "axiom parser_correct : True",
                "axiom beaconcrypt_core.transport.encoded_init_len : Nat",
            ):
                external.write_text(model)
                with self.subTest(model=model), self.assertRaises(ValueError):
                    checkpoint.checked_output(generated, "registration")

    def test_missing_external_roster_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            (generated / "FunsExternal_Template.lean").unlink()
            with self.assertRaises(ValueError):
                checkpoint.checked_output(generated, "registration")

    def test_unresolved_external_types_also_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            (generated / "TypesExternal_Template.lean").write_text(
                "axiom SliceModel : Type"
            )
            with self.assertRaises(ValueError):
                checkpoint.checked_output(generated, "registration")

    def test_empty_generated_files_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            (generated / "Types.lean").write_text("")
            with self.assertRaises(ValueError):
                checkpoint.checked_output(generated, "registration")

    def test_complete_roster_is_hashed(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = self.generated(Path(directory))
            hashes = checkpoint.checked_output(generated, "registration")
            self.assertEqual(
                set(hashes), {"Types.lean", "Funs.lean", "FunsExternal_Template.lean"}
            )
            self.assertTrue(all(len(value) == 64 for value in hashes.values()))


if __name__ == "__main__":
    unittest.main()
