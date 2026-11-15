#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the exact completion roster and source gate wiring."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

import check_computational_completion as gate


class RosterTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.path = (
            "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/Fixture.lean"
        )
        self.text = (
            "set_option warningAsError true\n"
            "theorem endpoint : True := True.intro\n"
            "/-- info: 'endpoint' does not depend on any axioms -/\n"
            "#guard_msgs in\n#print axioms endpoint\n"
        )
        target = self.root / self.path
        target.parent.mkdir(parents=True)
        target.write_text(self.text)
        (self.root / gate.LEAN_ROOT).write_text(
            "import BeaconcryptCore.Refinement.Fixture\n"
        )
        self.manifest = {
            "version": 1,
            "artifacts": [
                {
                    "path": self.path,
                    "category": "handwritten-lean",
                    "declarations": gate.DECLARATION.findall(self.text),
                    "guards": gate.guard_blocks(self.text),
                }
            ],
            "sourceChecks": [],
            "tests": [],
        }

    def rejected(self, text=None, manifest=None):
        if text is not None:
            (self.root / self.path).write_text(text)
        with self.assertRaises(ValueError):
            gate.check_roster(self.root, manifest or self.manifest)

    def extraction_workspace(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        return Path(directory.name)

    def negative_source_fixture(self):
        old = self.root / self.path
        self.path = gate.SOURCE_VALUE_GUARD_PATH
        target = self.root / self.path
        target.parent.mkdir(parents=True, exist_ok=True)
        old.unlink()
        self.text = (
            "set_option warningAsError true\n"
            + "\n".join(gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS[self.path])
            + "\n"
        )
        target.write_text(self.text)
        (self.root / gate.LEAN_ROOT).write_text(
            "import BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards\n"
        )
        self.manifest["artifacts"][0].update(path=self.path, declarations=[], guards=[])

    def test_reviewed_source_value_negative_control(self):
        self.negative_source_fixture()
        gate.check_roster(self.root, self.manifest)

    def test_source_value_negative_expected_error_changed(self):
        self.negative_source_fixture()
        self.rejected(self.text.replace("does not reach", "reaches"))

    def test_source_value_negative_required_proof_changed(self):
        self.negative_source_fixture()
        self.rejected(
            self.text.replace("AdapterSealNative.source_native", "Other.source")
        )

    def test_source_value_negative_guard_on_unrelated_module(self):
        self.rejected(self.text + gate.NEGATIVE_SOURCE_VALUE_GUARD + "\n")

    def test_source_value_negative_duplicate_guard(self):
        self.negative_source_fixture()
        self.rejected(self.text + gate.NEGATIVE_SOURCE_VALUE_GUARD + "\n")

    def test_each_branch_negative_is_exact_and_module_scoped(self):
        for name, snippet in gate.REVIEWED_NEGATIVE_SOURCE_GUARDS.items():
            with self.subTest(module=name):
                target = self.root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                controls = gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS.get(
                    name, (snippet,)
                )
                text = "set_option warningAsError true\n" + "\n".join(controls) + "\n"
                target.write_text(text)
                module = (
                    name.removeprefix("beaconcrypt-core/proofs/lean/")
                    .removesuffix(".lean")
                    .replace("/", ".")
                )
                (self.root / gate.LEAN_ROOT).write_text("import " + module + "\n")
                manifest = copy.deepcopy(self.manifest)
                manifest["artifacts"][0].update(path=name, declarations=[], guards=[])
                gate.check_roster(self.root, manifest)
                for changed in (
                    text.replace("does not reach", "reaches"),
                    text + snippet + "\n",
                ):
                    target.write_text(changed)
                    with self.assertRaises(ValueError):
                        gate.check_roster(self.root, manifest)

    def test_ad_hash_phase_negative_is_required(self):
        self.negative_source_fixture()
        controls = gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS[self.path]
        self.assertEqual(len(controls), 3)
        ad_phase = controls[1]
        for changed in (
            self.text.replace(ad_phase, ""),
            self.text + ad_phase + "\n",
            self.text.replace(ad_phase, ad_phase.replace("does not reach", "reaches")),
            self.text.replace(
                ad_phase, ad_phase.replace("state_hash_receipt", "other_receipt")
            ),
        ):
            with self.subTest(changed=changed):
                self.rejected(changed)

    def test_pure_pin_does_not_satisfy_ad_source_guard(self):
        self.negative_source_fixture()
        control = gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS[self.path][2]
        for changed in (
            self.text.replace(control, ""),
            self.text + control + "\n",
            self.text.replace(control, control.replace("does not reach", "reaches")),
            self.text.replace(control, control.replace("pin_source", "present_source")),
        ):
            with self.subTest(changed=changed):
                self.rejected(changed)

    def proof_value_controls_fixture(self):
        old = self.root / self.path
        self.path = gate.PROOF_VALUE_GUARD_PATH
        target = self.root / self.path
        target.parent.mkdir(parents=True, exist_ok=True)
        old.unlink()
        controls = gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS[self.path]
        self.text = "set_option warningAsError true\n" + "\n".join(controls) + "\n"
        target.write_text(self.text)
        (self.root / gate.LEAN_ROOT).write_text(
            "import BeaconcryptCore.Computational.RegistrationNativeProofValueGuard\n"
        )
        self.manifest["artifacts"][0].update(
            path=self.path, category="lean-control", declarations=[], guards=[]
        )
        return controls

    def test_proof_value_controls_exact_group(self):
        controls = self.proof_value_controls_fixture()
        self.assertEqual(len(controls), 8)
        self.assertIn("nestedTypeArgumentOnly", "\n".join(controls))
        self.assertIn("wrappedIgnored", "\n".join(controls))
        gate.check_roster(self.root, self.manifest)

    def test_each_proof_value_control_is_required_exactly_once(self):
        controls = self.proof_value_controls_fixture()
        for control in controls:
            for changed in (
                self.text.replace(control, ""),
                self.text + control + "\n",
                self.text.replace(
                    control, control.replace("does not reach", "reaches")
                ),
                self.text.replace(
                    control, control.replace("includes [anchor]", "includes [other]")
                ),
            ):
                with self.subTest(control=control, changed=changed):
                    self.rejected(changed)

    def test_proof_value_controls_are_module_scoped(self):
        controls = gate.REVIEWED_NEGATIVE_SOURCE_GUARD_GROUPS[
            gate.PROOF_VALUE_GUARD_PATH
        ]
        self.rejected(self.text + "\n".join(controls))

    def test_fresh_extraction_retry_preserves_prior_evidence(self):
        self.manifest["sourceChecks"] = [
            ["scripts/extract_fixture.py", "--check-source"]
        ]
        work = self.extraction_workspace()
        first = gate.fresh_extraction_commands(self.manifest, work, self.root)
        prior = Path(first[0][3])
        prior.mkdir()
        evidence = prior / "failed-tool.log"
        evidence.write_text("retained earlier extraction evidence")
        second = gate.fresh_extraction_commands(self.manifest, work, self.root)
        self.assertNotEqual(first[0][3], second[0][3])
        self.assertFalse(Path(second[0][3]).exists())
        self.assertEqual(evidence.read_text(), "retained earlier extraction evidence")
        self.assertEqual(
            second[0][:3], ["scripts/extract_fixture.py", "--check", "--work-dir"]
        )

    def test_fresh_extraction_checkout_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside the checkout"):
            gate.fresh_extraction_commands(
                self.manifest, self.root / "scratch", self.root
            )
        self.assertFalse((self.root / "scratch").exists())

    def test_fresh_extraction_ancestor_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside the checkout"):
            gate.fresh_extraction_commands(self.manifest, self.root.parent, self.root)

    def test_fresh_extraction_write_mode_rejected(self):
        self.manifest["sourceChecks"] = [["scripts/extract_fixture.py", "--write"]]
        with self.assertRaisesRegex(ValueError, "invalid fresh extraction control"):
            gate.fresh_extraction_commands(
                self.manifest, self.extraction_workspace(), self.root
            )

    def test_exact_fixture(self):
        gate.check_roster(self.root, self.manifest)

    def test_single_and_multiline_dependency_comments(self):
        for comment in (
            "/-- info: 'endpoint' does not depend on any axioms -/",
            "/--\ninfo: 'endpoint' does not depend on any axioms\n-/",
            "/--\ninfo: 'endpoint' depends on axioms: [propext,\n"
            " Classical.choice,\n Quot.sound]\n-/",
        ):
            with self.subTest(comment=comment):
                text = self.text.replace(
                    "/-- info: 'endpoint' does not depend on any axioms -/", comment
                )
                expected = comment + "\n#guard_msgs in\n#print axioms endpoint"
                self.assertEqual(gate.guard_blocks(text), [expected])
                manifest = copy.deepcopy(self.manifest)
                manifest["artifacts"][0]["guards"] = [expected]
                (self.root / self.path).write_text(text)
                gate.check_roster(self.root, manifest)

    def test_mixed_comment_layouts_keep_individual_guards(self):
        extra = (
            "theorem other : True := True.intro\n"
            "/--\ninfo: 'other' depends on axioms: [propext, Quot.sound]\n-/\n"
            "#guard_msgs in\n#print axioms other\n"
        )
        text = self.text + extra
        blocks = gate.guard_blocks(text)
        self.assertEqual(len(blocks), 2)
        self.assertEqual(blocks[0], self.manifest["artifacts"][0]["guards"][0])
        self.assertEqual(blocks[1], extra[extra.index("/--") :].rstrip())
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"][0].update(
            declarations=gate.DECLARATION.findall(text), guards=blocks
        )
        (self.root / self.path).write_text(text)
        gate.check_roster(self.root, manifest)

    def test_multiline_guard_requires_adjacent_complete_commands(self):
        text = self.text.replace("/-- info:", "/--\ninfo:").replace(
            "axioms -/", "axioms\n-/"
        )
        for changed in (
            text.replace("#guard_msgs in", "#check True\n#guard_msgs in"),
            text.replace("#print axioms", "#check True\n#print axioms"),
            text.replace("#guard_msgs in", "/-- unrelated -/\n#guard_msgs in"),
            text.replace("#print axioms", "/-- unrelated -/\n#print axioms"),
            text.replace("#guard_msgs in\n", "#guard_msgs in "),
            text.replace("#guard_msgs in", "#guard_msgs (drop warning) in"),
            text.replace("axioms\n-/", "axioms"),
        ):
            with self.subTest(changed=changed):
                self.assertEqual(gate.guard_blocks(changed), [])
                manifest = copy.deepcopy(self.manifest)
                manifest["artifacts"][0]["guards"] = []
                self.rejected(changed, manifest)

    def test_multiline_guard_cannot_hide_an_extra_print(self):
        text = self.text.replace("/-- info:", "/--\ninfo:").replace(
            "axioms -/", "axioms\n-/"
        )
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"][0]["guards"] = gate.guard_blocks(text)
        self.rejected(text + "#print axioms unguarded\n", manifest)

    def test_multiline_guard_still_requires_reviewed_axioms(self):
        for dependency in ("[native_decide]", "[propext, unreviewed]", "[]"):
            with self.subTest(dependency=dependency):
                text = self.text.replace(
                    "/-- info: 'endpoint' does not depend on any axioms -/",
                    "/--\ninfo: 'endpoint' depends on axioms: " + dependency + "\n-/",
                )
                manifest = copy.deepcopy(self.manifest)
                manifest["artifacts"][0]["guards"] = gate.guard_blocks(text)
                self.assertEqual(len(manifest["artifacts"][0]["guards"]), 1)
                self.rejected(text, manifest)

    def test_guard_layout_change_still_requires_exact_roster_review(self):
        self.rejected(self.text.replace("/-- info:", "/--\ninfo:"))

    def test_missing_import(self):
        (self.root / gate.LEAN_ROOT).write_text("")
        self.rejected()

    def test_duplicate_import(self):
        root = self.root / gate.LEAN_ROOT
        root.write_text(root.read_text() * 2)
        self.rejected()

    def test_unguarded_dependency(self):
        self.rejected(self.text.replace("#guard_msgs in\n", ""))

    def test_changed_dependency(self):
        self.rejected(self.text.replace("any axioms", "any axioms!"))

    def test_rehashed_nonstandard_dependency(self):
        text = self.text.replace(
            "does not depend on any axioms", "depends on axioms: [native_decide]"
        )
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"][0]["guards"] = gate.guard_blocks(text)
        self.rejected(text, manifest)

    def test_declaration_omission(self):
        self.rejected(self.text.replace("theorem endpoint", "theorem different"))

    def test_duplicate_artifact(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"] *= 2
        self.rejected(manifest=manifest)

    def test_warning_suppression(self):
        for extra in (
            "set_option warningAsError false\n",
            "set_option linter.deprecated false\n",
        ):
            self.rejected(self.text + extra)

    def test_placeholder(self):
        self.rejected(self.text + "axiom bypass : False\n")

    def test_path_escape(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"][0]["path"] = "../outside.lean"
        self.rejected(manifest=manifest)

    def test_symbolic_link(self):
        path = self.root / self.path
        original = path.with_suffix(".original")
        path.rename(original)
        path.symlink_to(original)
        self.rejected()

    def test_unreviewed_source_gate(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["sourceChecks"] = [["scripts/unreviewed.py", "--check"]]
        self.rejected(manifest=manifest)

    def test_missing_negative_controls(self):
        manifest = copy.deepcopy(self.manifest)
        script = "scripts/test_fixture.py"
        target = self.root / script
        target.parent.mkdir()
        target.write_text("pass\n")
        manifest["artifacts"].append(
            {"path": script, "category": "validation", "declarations": [], "guards": []}
        )
        self.rejected(manifest=manifest)

    def test_manifest_extra_claim(self):
        target = self.root / gate.MANIFEST
        value = dict(self.manifest, complete=True)
        target.write_text(json.dumps(value))
        with self.assertRaises(ValueError):
            gate.read_manifest(self.root)

    def test_source_write_mode(self):
        manifest = copy.deepcopy(self.manifest)
        script = "scripts/extract_fixture.py"
        path = self.root / script
        path.parent.mkdir()
        path.write_text("pass\n")
        manifest["artifacts"].append(
            {"path": script, "category": "validation", "declarations": [], "guards": []}
        )
        manifest["sourceChecks"] = [[script, "--write"]]
        self.rejected(manifest=manifest)

    def test_duplicate_source_gate(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["sourceChecks"] = [["unreviewed.py"]] * 2
        self.rejected(manifest=manifest)


if __name__ == "__main__":
    unittest.main()
