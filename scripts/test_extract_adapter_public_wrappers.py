#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Exact source, interface, control-certificate and warning-policy controls."""

import json
from pathlib import Path
import tempfile
import unittest

import extract_adapter_public_wrappers as extraction


class PublicExtraction(unittest.TestCase):
    def setUp(self):
        self.raw = {
            name: extraction.denormalize(
                (extraction.DESTINATION / name).read_bytes(), name
            )
            for name in ("Types.lean", "Funs.lean")
        }

    def test_source_and_models(self):
        extraction.check_source()

    def test_roundtrip(self):
        for name, raw in self.raw.items():
            normalized = extraction.normalize(raw, name)
            self.assertEqual(normalized, (extraction.DESTINATION / name).read_bytes())
            self.assertEqual(extraction.denormalize(normalized, name), raw)

    def test_reject_reordered_consumption(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    b"consumed_registrations", b"known_ids", 1
                ),
                "Funs.lean",
            )

    def test_reject_changed_abort_stage(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(b"core.mem.replace", b"core.mem.swap", 1),
                "Funs.lean",
            )

    def test_reject_changed_role(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    b"DhSecretRole.LocalIdentity", b"DhSecretRole.BeaconPrekey", 1
                ),
                "Funs.lean",
            )

    def test_reject_new_obligation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"] + b"\naxiom source_correct : True\n", "Funs.lean"
            )

    def test_reject_missing_operation(self):
        with self.assertRaises(ValueError):
            extraction.normalize(
                self.raw["Funs.lean"].replace(
                    b"auth.execute_hash hr", b"ok core.option.Option.None", 1
                ),
                "Funs.lean",
            )

    def test_reject_added_warning_suppression(self):
        contents = (
            extraction.DESTINATION / "Funs.lean"
        ).read_bytes() + b"\nset_option linter.deprecated false\n"
        with self.assertRaises(ValueError):
            extraction.denormalize(contents, "Funs.lean")

    def test_reject_disabled_warning_errors(self):
        contents = (
            (extraction.DESTINATION / "Types.lean")
            .read_bytes()
            .replace(b"warningAsError true", b"warningAsError false")
        )
        with self.assertRaises(ValueError):
            extraction.denormalize(contents, "Types.lean")

    def test_reject_changed_accessor_interface(self):
        contents = (
            (extraction.DESTINATION / "Funs.lean")
            .read_bytes()
            .replace(
                b"PublicWrapperPlatform.peerBinding peer",
                b"PublicWrapperPlatform.peerBinding other",
            )
        )
        with self.assertRaises(ValueError):
            extraction.denormalize(contents, "Funs.lean")

    def fixture(self, change):
        with tempfile.TemporaryDirectory(
            prefix="bc-public-source-control-"
        ) as temporary:
            root = Path(temporary)
            destination = root / "cohort"
            destination.mkdir()
            for name in extraction.snapshot()["source_sha256"]:
                target = root / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((extraction.ROOT / name).read_bytes())
            for name in (*extraction.MODELS, *extraction.INSTALLED, "provenance.json"):
                (destination / name).write_bytes(
                    (extraction.DESTINATION / name).read_bytes()
                )
            change(root, destination)
            with self.assertRaises(ValueError):
                extraction.check_source(root, destination)

    def test_reject_production_parser_drift(self):
        self.fixture(
            lambda root, _: (
                root / "beaconcrypt-parse/src/generated/transport.rs"
            ).write_text("// changed parser\n")
        )

    def test_reject_public_source_drift(self):
        self.fixture(
            lambda root, _: (root / "beaconcrypt/src/beacon.rs").write_text(
                "// changed wrapper\n"
            )
        )

    def test_reject_model_drift(self):
        self.fixture(
            lambda _, destination: (destination / "PlatformOperations.lean").write_text(
                "// changed platform\n"
            )
        )

    def change_evidence(self, edit):
        def change(_, destination):
            path = destination / "external-signatures.json"
            evidence = json.loads(path.read_bytes())
            edit(evidence)
            path.write_text(json.dumps(evidence))
            # Repair only the outer hash, to exercise the inner semantic roster.
            path = destination / "provenance.json"
            provenance = json.loads(path.read_bytes())
            provenance["installed_sha256"]["external-signatures.json"] = (
                extraction.digest(
                    (destination / "external-signatures.json").read_bytes()
                )
            )
            path.write_text(json.dumps(provenance))

        self.fixture(change)

    def test_reject_missing_control_branch(self):
        self.change_evidence(
            lambda evidence: evidence["control_preparation"]["distributions"].pop()
        )

    def test_reject_missing_template(self):
        self.change_evidence(
            lambda evidence: evidence["templates"].pop("FunsExternal_Template.lean")
        )

    def test_reject_changed_loop_certificate(self):
        self.change_evidence(
            lambda evidence: evidence["source_preparation"]["source_changes"][
                "beaconcrypt/src/beacon.rs"
            ].update(helper_body="return None;")
        )

    def test_reject_missing_generated_immutable_input(self):
        self.change_evidence(
            lambda evidence: evidence["source_preparation"]["unchanged_sha256"].pop(
                "beaconcrypt-parse/src/generated/transport.rs"
            )
        )

    def test_reject_provenance_roster_extension(self):
        def change(_, destination):
            path = destination / "provenance.json"
            contents = json.loads(path.read_bytes())
            contents["extra"] = True
            path.write_text(json.dumps(contents))

        self.fixture(change)


if __name__ == "__main__":
    unittest.main()
