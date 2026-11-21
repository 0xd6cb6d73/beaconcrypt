#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for the actual public Server delegator cohort."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest
import extract_adapter_public_server_entry as entry


class PublicServerEntryControls(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix="bc-server-entry-controls-")
        self.root = Path(self.scratch.name) / "root"
        self.root.mkdir()
        for name in entry.DEPENDENCIES:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(entry.ROOT / name, target)
        for name in (
            "Cargo.toml",
            "Cargo.lock",
            "hax.toml",
            "beaconcrypt/src/server.rs",
        ):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(entry.ROOT / name, target)
        parser = self.root / "beaconcrypt-parse/src/generated/control.rs"
        parser.parent.mkdir(parents=True)
        parser.write_text("// Immutable generated-parser fixture.\n")
        self.destination = (
            self.root / "beaconcrypt-core/proofs/lean" / entry.SUBDIRECTORY
        )
        self.destination.mkdir(parents=True)
        self.contents = {
            name: (entry.DESTINATION / name).read_bytes()
            for name in (*entry.INSTALLED, *entry.MODELS)
        }
        for name, value in self.contents.items():
            (self.destination / name).write_bytes(value)
        request = self.root / entry.REQUEST
        request.parent.mkdir(parents=True, exist_ok=True)
        request.write_bytes(entry.request(self.contents["Funs.lean"]))
        self.metadata = entry.receipt(self.root, self.contents, entry.TOOL_SHA256)
        self.save_metadata()

    def tearDown(self):
        self.scratch.cleanup()

    def save_metadata(self):
        (self.destination / "provenance.json").write_text(json.dumps(self.metadata))

    def rejected(self):
        with self.assertRaises((ValueError, KeyError, TypeError, FileNotFoundError)):
            entry.check_source(self.root)

    def test_current_cohort(self):
        entry.check_source(self.root)

    def test_inverse_source_certificate(self):
        for name in ("Types.lean", "Funs.lean"):
            raw = entry.denormalize(self.contents[name], name)
            self.assertEqual(entry.normalize(raw, name), self.contents[name])

    def test_original_source_call_order(self):
        path = self.root / "beaconcrypt/src/server.rs"
        path.write_text(
            path.read_text().replace(
                "let lookup = self.authenticate_registration_lookup(buffer)?;",
                "let lookup = self.authenticate_registration_lookup(buffer);",
            )
        )
        self.rejected()

    def test_original_mutable_rng_signature(self):
        path = self.root / "beaconcrypt/src/server.rs"
        path.write_text(
            path.read_text().replace(
                entry.SOURCE, entry.SOURCE.replace("rng: &mut R", "rng: &R")
            )
        )
        self.rejected()

    def test_duplicate_original_entry(self):
        path = self.root / "beaconcrypt/src/server.rs"
        path.write_text(path.read_text() + "\n" + entry.SOURCE)
        self.rejected()

    def test_generated_parser_source_drift(self):
        path = self.root / "beaconcrypt-parse/src/generated/control.rs"
        path.write_text("pub fn changed() {}\n")
        self.rejected()

    def test_child_extraction_dependency_drift(self):
        name = "beaconcrypt-core/proofs/lean/BeaconcryptCore/AdapterPublicWrapperExtraction/Funs.lean"
        path = self.root / name
        path.write_text(path.read_text() + "\n-- changed child extraction\n")
        self.rejected()

    def test_pinned_tool_identity(self):
        self.metadata["tool_sha256"]["charon"] = "0" * 64
        self.save_metadata()
        self.rejected()

    def test_missing_tool_identity(self):
        del self.metadata["tool_sha256"]["aeneas"]
        self.save_metadata()
        self.rejected()

    def test_wrong_tool_pin(self):
        self.metadata["tools"] = {**self.metadata["tools"], "charon": "candidate"}
        self.save_metadata()
        self.rejected()

    def test_wrong_fixture_mode(self):
        self.metadata["fixture"] = "transformed"
        self.save_metadata()
        self.rejected()

    def test_unknown_provenance_key(self):
        self.metadata["unchecked"] = True
        self.save_metadata()
        self.rejected()

    def test_normalized_source_changed(self):
        path = self.destination / "Funs.lean"
        path.write_bytes(
            path.read_bytes().replace(b"ok (o1, self, rng)", b"ok (o1, self, rng)\n")
        )
        self.rejected()

    def test_source_drift_cannot_be_resigned(self):
        changed = self.contents["Funs.lean"].replace(
            b"ok (o1, self, rng)", b"ok (o1, self, rng)\n"
        )
        with self.assertRaises(ValueError):
            entry.request(changed)

    def test_mutable_result_abi_changed(self):
        changed = self.contents["Funs.lean"].replace(
            b"\xc3\x97 server.Server \xc3\x97 R)", b"\xc3\x97 R)"
        )
        with self.assertRaises(ValueError):
            entry.denormalize(changed, "Funs.lean")

    def test_runtime_type_alias_drift(self):
        path = self.destination / "TypesExternal.lean"
        path.write_bytes(
            path.read_bytes().replace(
                b"beaconcrypt_public_wrapper.server.Server", b"Unit"
            )
        )
        self.rejected()

    def test_runtime_child_alias_drift_with_new_metadata(self):
        name = "FunsExternal.lean"
        self.contents[name] += b"\n-- unreviewed alias\n"
        (self.destination / name).write_bytes(self.contents[name])
        self.metadata = entry.receipt(self.root, self.contents, entry.TOOL_SHA256)
        self.save_metadata()
        self.rejected()

    def test_external_signature_roster(self):
        path = self.destination / "external-signatures.json"
        signatures = json.loads(path.read_text())
        signatures["new-unchecked-interface"] = "unreviewed"
        path.write_text(json.dumps(signatures))
        self.rejected()

    def test_external_rng_poststate_signature(self):
        path = self.destination / "external-signatures.json"
        signatures = json.loads(path.read_text())
        key = "FunsExternal_Template.lean"
        signatures[key] = signatures[key].replace("× server.Server × R)", "× R)")
        path.write_text(json.dumps(signatures))
        self.rejected()

    def test_request_branch_changed(self):
        path = self.root / entry.REQUEST
        path.write_bytes(
            path.read_bytes().replace(
                b"pure (o1, self, rng)", b"pure (o1, self, rng)\n"
            )
        )
        self.rejected()

    def test_request_child_opaque_lift(self):
        path = self.root / entry.REQUEST
        path.write_bytes(
            path.read_bytes().replace(
                b"authenticate_registration_lookup (m := m)",
                b"authenticate_registration_lookup",
            )
        )
        self.rejected()

    def test_original_immutable_fixture(self):
        destination = Path(self.scratch.name) / "fixture"
        roster = entry.immutable_fixture(self.root, destination)
        entry.verify_fixture(self.root, destination, roster)
        path = destination / "beaconcrypt-parse/src/generated/control.rs"
        path.write_text("// changed\n")
        with self.assertRaises(ValueError):
            entry.verify_fixture(self.root, destination, roster)

    def test_existing_or_inside_source_fixture_rejected(self):
        with self.assertRaises(ValueError):
            entry.immutable_fixture(self.root, self.root / "inside")
        destination = Path(self.scratch.name) / "existing"
        destination.mkdir()
        with self.assertRaises(ValueError):
            entry.immutable_fixture(self.root, destination)

    def test_source_worktree_as_output_rejected(self):
        with self.assertRaises(ValueError):
            entry.common.isolated_work_directory(entry.ROOT)


if __name__ == "__main__":
    unittest.main()
