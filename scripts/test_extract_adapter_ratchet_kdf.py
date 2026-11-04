#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed source/provenance controls for the three ratchet KDF wrappers."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

import extract_adapter_ratchet_kdf as extraction


class RatchetKdfExtraction(unittest.TestCase):
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
        with self.assertRaises(ValueError):
            extraction.normalize(source.replace(before, after, 1), "Funs.lean")

    def fixture(self, change):
        with tempfile.TemporaryDirectory(prefix="bc-ratchet-kdf-control-") as temporary:
            root = Path(temporary)
            destination = root / "cohort"
            destination.mkdir()
            files = extraction.source_fixture.source_files(extraction.ROOT)
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

    def provenance(self):
        return json.loads((extraction.DESTINATION / "provenance.json").read_text())

    def test_reviewed_source(self):
        extraction.check_source()

    def test_exact_roundtrip_and_core_method_binding(self):
        for name, source in self.raw.items():
            installed = (extraction.DESTINATION / name).read_bytes()
            self.assertEqual(extraction.normalize(source, name), installed)
        self.assertEqual(len(extraction.INTERFACES), 2)
        self.assertEqual(extraction.TRANSFORMATION["control_flow_rewrites"], [])
        self.assertEqual(extraction.TRANSFORMATION["fixture_rust_rewrites"], [])
        for before, after in extraction.INTERFACES:
            self.assertIn(before.encode(), self.raw["Funs.lean"])
            self.assertIn(
                after.encode(), (extraction.DESTINATION / "Funs.lean").read_bytes()
            )

    def test_exact_three_roots_and_opaque_primitives(self):
        tools = {name: Path("/tools") / name for name in extraction.PINNED_TOOLS}
        charon, aeneas = extraction.commands(tools, Path("/scratch"))
        self.assertEqual(
            [value for value in charon if value.startswith("--start-from=")],
            ["--start-from=" + name for name in extraction.START_FROM],
        )
        self.assertEqual(len(extraction.START_FROM), 3)
        for name in (
            "beaconcrypt",
            "beaconcrypt_core",
            "beaconcrypt_crypto",
            "zeroize",
            "core",
            "alloc",
            "std",
            "beaconcrypt_parse",
        ):
            self.assertIn("--opaque=" + name, charon)
        self.assertIn("--include=core::ops::range::RangeFull", charon)
        self.assertIn("-sequential", aeneas)
        self.assertIn("-abort-on-error", aeneas)

    def test_string_bounds_are_explicit_kernel_checked_proofs(self):
        installed = (extraction.DESTINATION / "Funs.lean").read_bytes()
        self.assertEqual(len(extraction.PROOF_ARGUMENTS), 2)
        for before, after in extraction.PROOF_ARGUMENTS:
            self.assertIn(before.encode(), self.raw["Funs.lean"])
            self.assertIn(after.encode(), installed)
            with self.assertRaises(ValueError):
                extraction.denormalize(
                    installed.replace(after.encode(), before.encode(), 1), "Funs.lean"
                )

    def test_both_role_only_profiles_are_explicit(self):
        self.assertEqual(
            extraction.PROFILES,
            {
                "canonical": "beacon,server,pqxdh",
                "beacon": "beacon,pqxdh",
                "server": "server,pqxdh",
            },
        )
        tools = {name: Path("/tools") / name for name in extraction.PINNED_TOOLS}
        for profile, features in extraction.PROFILES.items():
            charon, _ = extraction.commands(tools, Path("/scratch"), profile)
            self.assertIn("--no-default-features", charon)
            self.assertEqual(
                [value for value in charon if value.startswith("--features=")],
                ["--features=" + features],
            )
        with self.assertRaisesRegex(ValueError, "unreviewed.*profile"):
            extraction.commands(tools, Path("/scratch"), "other")

    def test_const_output_bound_and_both_expects_remain(self):
        self.assertEqual(self.raw["Funs.lean"].count(b"core.result.Result.expect"), 2)
        for before, after in (
            (b"255#usize * 64#usize", b"254#usize * 64#usize"),
            (b"massert (OUTPUT_SIZE <= i)", b"ok ()"),
            (b"core.result.Result.expect", b"core.result.Result.unchecked"),
        ):
            with self.subTest(before=before):
                self.reject_body(before, after)

    def test_salt_input_info_and_expand_operand_order(self):
        for before, after in (
            (
                b"extract core.option.Option.None s",
                b"extract core.option.Option.None s2",
            ),
            (
                b"SymmetricRatchetKdfRequest.input request",
                b"SymmetricRatchetKdfRequest.info request",
            ),
            (b"(core.option.Option.Some s2) prk", b"(core.option.Option.Some s1) prk"),
            (b"expand_into s1", b"expand_into s2"),
        ):
            with self.subTest(before=before):
                self.reject_body(before, after)

    def test_zero_initialization_and_mutable_writeback(self):
        for before, after in (
            (b"Array.repeat OUTPUT_SIZE 0#u8", b"Array.repeat OUTPUT_SIZE 1#u8"),
            (b"Zeroizing.new", b"Zeroizing.unchecked_new"),
            (b"DerefDerefMut.deref_mut", b"DerefDerefMut.unchecked"),
            (b"index_mut_back s3", b"index_mut_back s1"),
            (b"deref_mut_back a4", b"deref_mut_back a2"),
        ):
            with self.subTest(before=before):
                self.reject_body(before, after)

    def test_production_widths_are_not_interchanged(self):
        for before, after in (
            (
                b"symmetric_ratchet_hkdf 76#usize request",
                b"symmetric_ratchet_hkdf 64#usize request",
            ),
            (
                b"symmetric_ratchet_hkdf 64#usize request",
                b"symmetric_ratchet_hkdf 76#usize request",
            ),
        ):
            with self.subTest(before=before):
                self.reject_body(before, after)

    def test_missing_method_binding_and_warning_suppression_rejected(self):
        source = (extraction.DESTINATION / "Funs.lean").read_bytes()
        for changed in (
            source.replace(b".impl.input request", b".input request", 1),
            source.replace(extraction.BINDER.encode(), b"", 1),
            source + b"\nset_option linter.deprecated false\n",
        ):
            with self.subTest(changed=changed[-100:]):
                with self.assertRaises(ValueError):
                    extraction.denormalize(changed, "Funs.lean")

    def test_added_proof_obligation_rejected(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom trusted : True\n", "Funs.lean"
            )

    def test_runtime_source_or_core_getter_drift_rejected(self):
        for name in (
            "beaconcrypt/src/ratchet.rs",
            "beaconcrypt-crypto/src/crypto_kdf.rs",
            "beaconcrypt-core/src/ratchet.rs",
            "beaconcrypt-core/proofs/lean/BeaconcryptCore/Extraction/Funs.lean",
        ):
            with self.subTest(name=name):
                self.fixture(
                    lambda root, _, name=name: (root / name).write_text("// changed\n")
                )

    def test_added_fixture_source_rejected(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/unreviewed.rs").write_text(
                "// added\n"
            )
        )

    def test_model_drift_is_rejected_even_if_provenance_rehashed(self):
        def change(_, destination):
            path = destination / "FunsExternal.lean"
            path.write_text(path.read_text() + "\n-- changed\n")
            metadata = destination / "provenance.json"
            value = json.loads(metadata.read_text())
            value["model_sha256"][path.name] = extraction.digest(path.read_bytes())
            metadata.write_text(json.dumps(value))

        self.fixture(change)

    def test_profile_omission_output_drift_or_new_evidence_rejected(self):
        before = self.provenance()
        missing = copy.deepcopy(before)
        del missing["profile_comparisons"]["server"]
        drift = copy.deepcopy(before)
        drift["profile_comparisons"]["beacon"]["raw_generated_sha256"]["Funs.lean"] = (
            "0" * 64
        )
        extra = copy.deepcopy(before)
        extra["profile_comparisons"]["canonical"]["ignored"] = True
        for changed in (missing, drift, extra):
            with self.subTest(changed=changed["profile_comparisons"]):
                with self.assertRaises(ValueError):
                    extraction.validate_profile_comparisons(changed)

    def test_role_profile_outputs_equal_canonical_installed_modules(self):
        value = self.provenance()
        extraction.validate_profile_comparisons(value)
        expected = {
            name: extraction.digest((extraction.DESTINATION / name).read_bytes())
            for name in ("Types.lean", "Funs.lean")
        }
        for profile in extraction.PROFILES:
            self.assertEqual(
                value["profile_comparisons"][profile]["normalized_generated_sha256"],
                expected,
            )


if __name__ == "__main__":
    unittest.main()
