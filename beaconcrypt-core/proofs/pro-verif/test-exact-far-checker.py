#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject omitted targets, wrong far recipes and inconclusive verifier output."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "exact_far_tests", Path(__file__).with_name("check-exact-far.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)


class ExactFarChecks(unittest.TestCase):
    def test_reviewed_manifest_and_complete_endpoints(self):
        CHECKER.validate_targets()
        for direction, lower, upper in (("b2s", 3, 53), ("s2b", 4, 54)):
            text = CHECKER.family(direction)
            CHECKER.check_family(text, direction)
            self.assertIn(f"fs_far_chain(anchor, {lower}) = anchor\n", text)
            self.assertIn(f"fs_far_chain(anchor, {upper}) = hkdf_second_32", text)

    def test_every_recipe_must_have_the_exact_depth(self):
        for direction in ("b2s", "s2b"):
            text = CHECKER.family(direction)
            lines = text.splitlines()
            for index in range(1, 52):
                corrupted = list(lines)
                left, _ = corrupted[index].split(" = ")
                corrupted[index] = (
                    left + " = pqxdh_ff32_padding()" + ("." if index == 51 else "")
                )
                with self.assertRaises(ValueError):
                    CHECKER.check_family("\n".join(corrupted), direction)

    def test_case_omission_duplicate_and_out_of_range_branch(self):
        for direction in ("b2s", "s2b"):
            text = CHECKER.family(direction)
            lines = text.splitlines()
            for bad in (
                "\n".join(lines[:2] + lines[3:]),
                "\n".join(lines[:2] + [lines[2]] + lines[2:]),
                text[:-1]
                + "\notherwise forall anchor: bitstring; fs_far_chain(anchor, 55) = anchor.",
                text.replace("otherwise", "reduc", 1),
            ):
                with self.assertRaises(ValueError):
                    CHECKER.check_family(bad, direction)

    def test_wrong_label_and_projection(self):
        text = CHECKER.family("b2s")
        for bad in (
            text.replace("symmetric_ratchet_domain", "pqxdh_domain", 1),
            text.replace("hkdf_second_32", "hkdf_first_32", 1),
        ):
            with self.assertRaises(ValueError):
                CHECKER.check_family(bad, "b2s")

    def test_controls_are_explicit_and_cannot_replace_real_cases(self):
        for direction in ("b2s", "s2b"):
            public = CHECKER.family(direction, True)
            CHECKER.check_family(public, direction, True)
            with self.assertRaises(ValueError):
                CHECKER.check_family(public, direction)
            with self.assertRaises(ValueError):
                CHECKER.check_family(CHECKER.family(direction), direction, True)

    def test_roster_classes_bounds_and_control_polarity(self):
        for i, target in enumerate(CHECKER.TARGETS):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(CHECKER.TARGETS[:i] + CHECKER.TARGETS[i + 1 :])
            changed = list(CHECKER.TARGETS)
            changed[i] = replace(target, cls="definitional")
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(changed)
            self.assertEqual(target.fs_target().bound, 1)
            self.assertFalse(target.fs_target().failstop)

    def test_receive_changes_only_the_helper_definition(self):
        for target in CHECKER.TARGETS:
            filename = f"fs-records-{target.direction}-receive.pvl"
            source = (CHECKER.HERE / filename).read_text()
            rendered = CHECKER.receive_model(
                source, target.direction, target.public_chain
            )
            restored = rendered.replace(
                CHECKER.family(target.direction, target.public_chain),
                CHECKER.DECLARATION,
            )
            self.assertEqual(restored, source)
            with self.assertRaises(ValueError):
                CHECKER.receive_model(source + CHECKER.DECLARATION, target.direction)

    def test_input_change_requires_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            for name in CHECKER.TOKEN_SHA256:
                out = directory / name
                out.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE / name, out)
            source = directory / "fs-records-b2s-receive.pvl"
            source.write_text(
                source.read_text().replace(
                    "=assigned_key_id", "ignored_key_id: key_id", 1
                )
            )
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(directory=directory)

    def test_source_admission_change_requires_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in CHECKER.SOURCE_SHA256:
                out = root / name
                out.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy(CHECKER.HERE.parents[2] / name, out)
            source = root / "beaconcrypt-core/src/ratchet/control.rs"
            source.write_text(
                source.read_text().replace(
                    "let skipped = derivations - 1;",
                    "let skipped = derivations - 2;",
                    1,
                )
            )
            with self.assertRaises(ValueError):
                CHECKER.validate_targets(source_root=root)

    def test_verdicts_and_traces_fail_closed(self):
        for target in CHECKER.TARGETS:
            output = (
                "RESULT "
                + target.results[0]
                + "\n"
                + "A trace has been found.\n" * target.expected_traces()
                + "Verification summary:\nQuery "
                + target.results[0]
                + "\n"
            )
            CHECKER.check_output(output, target)
            for bad in (
                output.replace("RESULT ", "", 1),
                output.replace("Verification summary:", ""),
                output
                + "I could not confirm that the previous trace falsifies the query.\n",
                output.replace(" is true.", " cannot be proved.").replace(
                    " is false.", " cannot be proved."
                ),
                output + "RESULT not event(Unlisted) is true.\n",
                output + "Warning: unsupported proof assumption\n",
                output + "A trace has been found.\n",
            ):
                with self.assertRaises(ValueError):
                    CHECKER.check_output(bad, target)
            if target.expected_traces():
                with self.assertRaises(ValueError):
                    CHECKER.check_output(
                        output.replace("A trace has been found.\n", ""), target
                    )


if __name__ == "__main__":
    unittest.main()
