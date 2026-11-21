#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the unchanged original seal dispatcher."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import extract_adapter_seal as extraction


class SealExtraction(unittest.TestCase):
    def setUp(self):
        self.raw = {
            name: extraction.denormalize(
                (extraction.DESTINATION / name).read_bytes(), name
            )
            for name in ("Types.lean", "Funs.lean")
        }

    def reject_body(self, before, after):
        source = self.raw["Funs.lean"]
        self.assertIn(before, source)
        changed = source.replace(before, after, 1)
        with self.assertRaises(ValueError):
            extraction.normalize(changed, "Funs.lean")

    def fixture(self, change):
        with tempfile.TemporaryDirectory(prefix="bc-seal-control-") as temporary:
            root = Path(temporary)
            destination = root / "cohort"
            destination.mkdir()
            files = extraction.source_files(extraction.ROOT)
            for name in extraction.SOURCE_FILES:
                files[name] = (extraction.ROOT / name).read_bytes()
            for name, contents in files.items():
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(contents)
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reviewed_source(self):
        extraction.check_source()

    def test_roundtrip(self):
        for name, source in self.raw.items():
            self.assertEqual(
                extraction.normalize(source, name),
                (extraction.DESTINATION / name).read_bytes(),
            )

    def test_exact_root_and_boundaries(self):
        tools = {name: Path("/tools") / name for name in extraction.PINNED_TOOLS}
        charon, aeneas = extraction.commands(tools, Path("/scratch"))
        self.assertEqual(
            [x for x in charon if x.startswith("--start-from=")],
            ["--start-from=beaconcrypt::ratchet::execute_seal_request"],
        )
        for name in (
            "beaconcrypt",
            "beaconcrypt_core",
            "beaconcrypt_crypto",
            "zeroize",
            "core",
            "alloc",
            "std",
        ):
            self.assertIn("--opaque=" + name, charon)
        self.assertIn(
            "--include=beaconcrypt_core::record_effects::AeadSealRequest", charon
        )
        self.assertIn(
            "--include=beaconcrypt_core::record_effects::SealPlaintextRequest", charon
        )
        self.assertIn("-abort-on-error", aeneas)
        self.assertEqual(extraction.TRANSFORMATION["body_rewrites"], [])
        self.assertEqual(extraction.TRANSFORMATION["mutable_serializers"], [])

    def test_single_plaintext_is_not_joined(self):
        self.reject_body(
            b"plaintext (core.option.Option.Some s) nonce key",
            b"application (core.option.Option.Some s) nonce key",
        )

    def test_prefixed_join_is_retained(self):
        self.reject_body(
            b"ratchet.join_record_parts (Array.make 2#usize [ s, application ])",
            b"ok core.option.Option.None",
        )

    def test_join_part_order(self):
        self.reject_body(b"[ s, application ]", b"[ application, s ]")

    def test_join_array_width(self):
        self.reject_body(
            b"Array.make 2#usize [ s, application ]",
            b"Array.make 3#usize [ s, application ]",
        )

    def test_key_conversion(self):
        self.reject_body(b"Key.Insts.CoreConvertFromArrayU832", b"Key.Insts.Unchecked")

    def test_nonce_conversion(self):
        self.reject_body(
            b"Nonce.Insts.CoreConvertFromArrayU812", b"Nonce.Insts.Unchecked"
        )

    def test_associated_data_operand(self):
        self.reject_body(
            b"core.array.Array.as_slice request.associated_data",
            b"core.array.Array.as_slice request.key",
        )

    def test_aead_operand_order(self):
        self.reject_body(
            b"plaintext (core.option.Option.Some s) nonce key",
            b"plaintext (core.option.Option.Some s) key nonce",
        )

    def test_zeroizing_constructor(self):
        self.reject_body(b"zeroize.Zeroizing.new", b"zeroize.Zeroizing.unchecked")

    def test_zeroizing_deref(self):
        self.reject_body(
            b"zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref",
            b"zeroize.Zeroizing.unchecked_deref",
        )

    def test_aead_error_conversion(self):
        self.reject_body(b"core.result.Result.ok r", b"core.result.Result.unwrap r")

    def test_tag_width(self):
        self.reject_body(
            b"16#usize core.U8.Insts.CoreMarkerCopy s1",
            b"15#usize core.U8.Insts.CoreMarkerCopy s1",
        )

    def test_residual_failure_branch(self):
        self.reject_body(b"ControlFlow.Break residual", b"ControlFlow.Break ignored")

    def test_reject_new_obligation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom trusted : True\n", "Funs.lean"
            )

    def test_reject_warning_suppression(self):
        installed = (extraction.DESTINATION / "Funs.lean").read_bytes()
        with self.assertRaises(ValueError):
            extraction.denormalize(
                installed + b"\nset_option linter.deprecated false\n", "Funs.lean"
            )

    def test_reject_missing_operation_binder(self):
        installed = (
            (extraction.DESTINATION / "Funs.lean")
            .read_bytes()
            .replace(
                b"variable [BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]\n",
                b"",
                1,
            )
        )
        with self.assertRaises(ValueError):
            extraction.denormalize(installed, "Funs.lean")

    def test_reject_runtime_source_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/ratchet.rs").write_text(
                "// changed\n"
            )
        )

    def test_reject_copied_generated_source_drift(self):
        self.fixture(
            lambda root, _: (
                root / "beaconcrypt-parse/src/generated/cbordetveraux.rs"
            ).write_text("// changed\n")
        )

    def test_reject_new_copied_source(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/unreviewed.rs").write_text(
                "// changed\n"
            )
        )

    def test_reject_model_drift_even_if_rehashed(self):
        def change(_, destination):
            model = destination / "FunsExternal.lean"
            model.write_text(
                model.read_text().replace(
                    "operations.join parts", "operations.join parts -- altered", 1
                )
            )
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            value["model_sha256"]["FunsExternal.lean"] = extraction.digest(
                model.read_bytes()
            )
            path.write_text(json.dumps(value))

        self.fixture(change)

    def test_reject_primitive_model_drift(self):
        self.fixture(
            lambda root, _: (
                root
                / "beaconcrypt-core/proofs/lean/BeaconcryptCore/Refinement/AdapterSealPrimitive.lean"
            ).write_text("// changed\n")
        )

    def test_reject_installed_body_even_if_rehashed(self):
        def change(_, destination):
            path = destination / "Funs.lean"
            changed = path.read_bytes().replace(
                b"encrypt_detached", b"unchecked_detached", 1
            )
            path.write_bytes(changed)
            provenance = destination / "provenance.json"
            value = json.loads(provenance.read_text())
            value["installed_sha256"]["Funs.lean"] = extraction.digest(changed)
            value["raw_generated_sha256"]["Funs.lean"] = extraction.digest(
                self.raw["Funs.lean"].replace(
                    b"encrypt_detached", b"unchecked_detached", 1
                )
            )
            provenance.write_text(json.dumps(value))

        self.fixture(change)

    def test_reject_external_signature_drift(self):
        def change(_, destination):
            path = destination / "external-signatures.json"
            value = json.loads(path.read_text())
            value["platform_signatures"]["unchecked"] = "True"
            path.write_text(json.dumps(value))

        self.fixture(change)

    def test_reject_template_drift_even_if_rehashed(self):
        def change(_, destination):
            path = destination / "external-signatures.json"
            value = json.loads(path.read_text())
            template = value["templates"]["FunsExternal_Template.lean"]
            template["source"] += "\naxiom unexpected : True\n"
            template["sha256"] = extraction.digest(template["source"].encode())
            path.write_text(json.dumps(value))
            provenance = destination / "provenance.json"
            data = json.loads(provenance.read_text())
            data["installed_sha256"]["external-signatures.json"] = extraction.digest(
                path.read_bytes()
            )
            data["raw_generated_sha256"]["FunsExternal_Template.lean"] = template[
                "sha256"
            ]
            provenance.write_text(json.dumps(data))

        self.fixture(change)

    def test_reject_extra_provenance_field(self):
        def change(_, destination):
            path = destination / "provenance.json"
            value = json.loads(path.read_text())
            value["unchecked"] = True
            path.write_text(json.dumps(value))

        self.fixture(change)

    def test_exact_original_fixture(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-fixture-") as temporary:
            fixture = Path(temporary) / "source"
            extraction.prepare_source(extraction.ROOT, fixture)
            expected = {
                name: extraction.digest(value)
                for name, value in extraction.source_files(extraction.ROOT).items()
            }
            extraction.check_fixture(fixture, expected)
            (fixture / "beaconcrypt/src/ratchet.rs").write_text("// changed\n")
            with self.assertRaises(ValueError):
                extraction.check_fixture(fixture, expected)

    def test_reject_fixture_extra_file(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-extra-") as temporary:
            fixture = Path(temporary)
            (fixture / "unchecked").write_text("unchecked")
            with self.assertRaises(ValueError):
                extraction.check_fixture(fixture, {})

    def test_reject_existing_fixture(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-existing-") as temporary:
            with self.assertRaises(ValueError):
                extraction.prepare_source(extraction.ROOT, Path(temporary))

    def test_reject_fixture_symlink(self):
        with tempfile.TemporaryDirectory(prefix="bc-seal-symlink-") as temporary:
            fixture = Path(temporary)
            (fixture / "link").symlink_to(
                extraction.ROOT / "beaconcrypt/src/ratchet.rs"
            )
            with self.assertRaises(ValueError):
                extraction.check_fixture(fixture, {})

    def test_reject_combined_modes(self):
        result = subprocess.run(
            [
                sys.executable,
                str(extraction.ROOT / "scripts/extract_adapter_seal.py"),
                "--check-source",
                "--write",
            ],
            capture_output=True,
        )
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
