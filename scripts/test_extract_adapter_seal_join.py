#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the fixed-two seal join extraction/provenance boundary."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import extract_adapter_seal_join as extraction


class SealJoinExtraction(unittest.TestCase):
    def setUp(self):
        self.installed = {
            name: (extraction.DESTINATION / name).read_bytes()
            for name in ("Types.lean", "Funs.lean")
        }
        self.raw = {
            name: extraction.denormalize(contents, name)
            for name, contents in self.installed.items()
        }

    def test_reviewed_source(self):
        extraction.check_source()

    def test_raw_roundtrip(self):
        for name, contents in self.raw.items():
            self.assertEqual(extraction.digest(contents), extraction.RAW_SHA256[name])
            self.assertEqual(extraction.normalize(contents, name), self.installed[name])

    def reject_raw(self, before, after):
        changed = self.raw["Funs.lean"].replace(before, after, 1)
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def test_reject_omitted_reservation(self):
        self.reject_raw(
            b"alloc.vec.Vec.try_reserve_exact output val1",
            b"pure (core.result.Result.Ok (), output)",
        )

    def test_reject_changed_part_order(self):
        self.reject_raw(b"output1\n            s", b"output1\n            s1")

    def test_reject_changed_index(self):
        self.reject_raw(
            b"Array.index_usize parts 0#usize", b"Array.index_usize parts 2#usize"
        )

    def test_reject_changed_checked_length(self):
        self.reject_raw(
            b"core.num.Usize.checked_add val i1",
            b"core.num.Usize.checked_add val 0#usize",
        )

    def test_reject_omitted_failure_branch(self):
        self.reject_raw(
            b"core.ops.control_flow.ControlFlow.Break residual",
            b"core.ops.control_flow.ControlFlow.Break ignored",
        )

    def test_reject_reservation_error_becoming_success(self):
        self.reject_raw(
            b"      | core.ops.control_flow.ControlFlow.Break residual =>\n"
            b"        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual\n"
            b"          (alloc.vec.Vec Std.U8) residual",
            b"      | core.ops.control_flow.ControlFlow.Break _ =>\n"
            b"        ok (core.option.Option.Some output1)",
        )

    def test_reject_new_obligation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom complete_codec : True\n", "Funs.lean"
            )

    def test_reject_warning_suppression(self):
        for extra in (
            b"\nset_option warningAsError false\n",
            b"\nset_option linter.deprecated false\n",
        ):
            with self.assertRaises(ValueError):
                extraction.denormalize(self.installed["Funs.lean"] + extra, "Funs.lean")

    def test_reject_external_signature_drift(self):
        evidence = json.loads(
            (extraction.DESTINATION / "external-signatures.json").read_bytes()
        )
        templates = {
            name: value["source"].encode()
            for name, value in evidence["templates"].items()
        }
        templates["FunsExternal_Template.lean"] += b"\naxiom extra : Nat\n"
        with self.assertRaises(ValueError):
            extraction.validate_templates(templates)

    def fixture(self, change):
        with tempfile.TemporaryDirectory(
            prefix="bc-helper-extraction-control-"
        ) as directory:
            root = Path(directory)
            destination = root / "cohort"
            destination.mkdir()
            names = set(extraction.SOURCE_FILES) | set(
                extraction.preparation.source_files(extraction.ROOT)
            )
            for name in names:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((extraction.ROOT / name).read_bytes())
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            extraction.check_source(root, destination)
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def change_provenance(self, update):
        def change(_, destination):
            path = destination / "provenance.json"
            contents = json.loads(path.read_bytes())
            update(contents)
            path.write_text(json.dumps(contents))

        self.fixture(change)

    def test_reject_source_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/ratchet.rs").write_text(
                "// changed\n"
            )
        )

    def test_reject_original_generated_rust_drift(self):
        def change(root, _):
            path = next((root / "beaconcrypt-parse/src/generated").glob("*.rs"))
            path.write_text("// changed\n")

        self.fixture(change)

    def test_reject_fixed_parts_proof_drift(self):
        self.fixture(
            lambda root, _: (
                root
                / "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterSealFixedParts.lean"
            ).write_text("-- changed\n")
        )

    def test_reject_mutable_external_model_drift(self):
        self.fixture(
            lambda _, destination: (destination / "FunsExternal.lean").write_text(
                "-- changed\n"
            )
        )

    def test_reject_rehashed_external_model_drift(self):
        def change(_, destination):
            path = destination / "FunsExternal.lean"
            path.write_bytes(path.read_bytes() + b"\n-- unreviewed model edit\n")
            receipt = destination / "provenance.json"
            contents = json.loads(receipt.read_bytes())
            contents["model_sha256"][path.name] = extraction.digest(path.read_bytes())
            receipt.write_text(json.dumps(contents))

        self.fixture(change)

    def test_reject_allocator_model_substitution(self):
        self.fixture(
            lambda root, _: (
                root
                / "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterWireExtraction/FunsExternal.lean"
            ).write_text("-- discarded allocation\n")
        )

    def test_reject_extra_provenance_field(self):
        self.change_provenance(lambda contents: contents.update(unreviewed=True))

    def test_reject_tampered_preparation_certificate(self):
        def update(contents):
            contents["source_preparation"]["source_changes"][
                "beaconcrypt/src/ratchet.rs"
            ]["fold_order"] = [1, 0]

        self.change_provenance(update)

    def test_reject_rehashed_installed_body_drift(self):
        def change(_, destination):
            path = destination / "Funs.lean"
            changed = path.read_bytes().replace(
                b"output1\n            s", b"output1\n            s1", 1
            )
            path.write_bytes(changed)
            receipt = destination / "provenance.json"
            contents = json.loads(receipt.read_bytes())
            contents["installed_sha256"]["Funs.lean"] = extraction.digest(changed)
            receipt.write_text(json.dumps(contents))

        self.fixture(change)

    def test_reject_rehashed_raw_roster_drift(self):
        self.change_provenance(
            lambda contents: contents["raw_generated_sha256"].update(
                {"Funs.lean": "0" * 64}
            )
        )

    def test_cli_combined_modes_cannot_mutate(self):
        before = {
            path.name: path.read_bytes()
            for path in extraction.DESTINATION.iterdir()
            if path.is_file()
        }
        result = subprocess.run(
            [
                sys.executable,
                str(extraction.ROOT / "scripts/extract_adapter_seal_join.py"),
                "--write",
                "--check",
            ],
            capture_output=True,
            timeout=15,
        )
        self.assertEqual(result.returncode, 2)
        self.assertIn(b"not allowed with argument", result.stderr)
        self.assertEqual(
            before,
            {
                path.name: path.read_bytes()
                for path in extraction.DESTINATION.iterdir()
                if path.is_file()
            },
        )

    def test_source_command_selects_only_fixed_two_join(self):
        with tempfile.TemporaryDirectory(prefix="bc-helper-command-") as directory:
            charon, aeneas = extraction.commands(
                {name: Path(name) for name in extraction.PINNED_TOOLS}, Path(directory)
            )
        self.assertEqual(
            [
                part.removeprefix("--start-from=")
                for part in charon
                if part.startswith("--start-from=")
            ],
            extraction.START_FROM,
        )
        self.assertIn("--opaque=beaconcrypt_parse", charon)
        self.assertIn(extraction.SUBDIRECTORY, aeneas)


if __name__ == "__main__":
    unittest.main()
