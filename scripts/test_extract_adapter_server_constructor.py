#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Fail-closed controls for original public Server constructor source closure."""

import json
from pathlib import Path
import tempfile
import unittest
import extract_adapter_server_constructor as target


class ConstructorSourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = target.ROOT
        cls.evidence = json.loads(
            (target.DESTINATION / "source-evidence.json").read_bytes()
        )
        cls.raw = {name: value.encode() for name, value in cls.evidence["raw"].items()}
        cls.shared = (cls.root / target.SHARED_TYPES).read_bytes()
        cls.source = (target.DESTINATION / "Funs.lean").read_bytes()
        cls.bindings = (cls.root / target.BINDINGS).read_bytes()

    def test_baseline(self):
        target.check_source()
        for name in ("Types.lean", "Funs.lean"):
            self.assertEqual(
                target.normalize(self.raw[name], name, self.shared),
                (target.DESTINATION / name).read_bytes(),
            )
        self.assertEqual(
            target.request(self.source, self.bindings),
            (self.root / target.REQUEST).read_bytes(),
        )

    def test_absent_constructor(self):
        changed = self.raw["Funs.lean"].replace(
            b"def server.Server.try_new_with_rng\n", b"def missing_constructor\n", 1
        )
        with self.assertRaisesRegex(ValueError, "missing or opaque"):
            target.require_roots(changed, self.raw["FunsExternal_Template.lean"])

    def test_opaque_constructor(self):
        changed = self.raw["Funs.lean"].replace(
            b"def server.Server.try_new_with_rng\n",
            b"axiom server.Server.try_new_with_rng\n",
            1,
        )
        with self.assertRaisesRegex(ValueError, "missing or opaque"):
            target.require_roots(changed, self.raw["FunsExternal_Template.lean"])

    def test_external_constructor_premise(self):
        changed = (
            self.raw["FunsExternal_Template.lean"]
            + b"\naxiom server.Server.try_new_with_rng : Type\n"
        )
        with self.assertRaisesRegex(ValueError, "external premise"):
            target.require_roots(self.raw["Funs.lean"], changed)

    def test_absent_panicking_entry(self):
        changed = self.raw["Funs.lean"].replace(
            b"def server.Server.new\n", b"def missing_entry\n", 1
        )
        with self.assertRaises(ValueError):
            target.require_roots(changed, self.raw["FunsExternal_Template.lean"])

    def test_generator_order(self):
        changed = self.raw["Funs.lean"].replace(
            b"beaconcrypt_crypto.crypto_sign.KeyPair.generate_with_rng",
            b"changed.KeyPair.generate_with_rng",
            1,
        )
        with self.assertRaisesRegex(ValueError, "unreviewed original"):
            target.normalize(changed, "Funs.lean", self.shared)

    def test_rng_error_poststate(self):
        changed = self.raw["Funs.lean"].replace(b"ok (r3, rng2)", b"ok (r3, rng1)", 1)
        self.assertNotEqual(changed, self.raw["Funs.lean"])
        with self.assertRaises(ValueError):
            target.normalize(changed, "Funs.lean", self.shared)

    def test_shared_layout(self):
        start = self.shared.index(b"structure server.ServerIdentity where")
        changed = self.shared[:start] + self.shared[start:].replace(
            b"identity_key_kid : Std.U64", b"changed_key_id : Std.U64", 1
        )
        self.assertNotEqual(changed, self.shared)
        with self.assertRaisesRegex(ValueError, "layout changed"):
            target.shared_blocks(self.raw["Types.lean"], changed)

    def test_binding_table(self):
        changed = json.loads(self.bindings)
        changed["definitions"][0]["body"][0]["count"] += 1
        with self.assertRaisesRegex(ValueError, "binding table changed"):
            target.request(self.source, json.dumps(changed).encode())

    def test_request_source(self):
        with self.assertRaisesRegex(ValueError, "request source changed"):
            target.request(self.source.replace(b"rng2", b"rng1", 1), self.bindings)

    def fixture(self, directory):
        root = Path(directory)
        provenance = json.loads((target.DESTINATION / "provenance.json").read_bytes())
        paths = (
            set(provenance["source_sha256"])
            | set(provenance["dependency_sha256"])
            | {target.REQUEST}
        )
        for name in paths:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((self.root / name).read_bytes())
        destination = root / "beaconcrypt-core/proofs/lean" / target.SUBDIRECTORY
        destination.mkdir(parents=True, exist_ok=True)
        for name in (*target.MODELS, *target.INSTALLED, "provenance.json"):
            (destination / name).write_bytes((target.DESTINATION / name).read_bytes())
        return root, destination

    def test_primitive_rng_abi(self):
        with tempfile.TemporaryDirectory(prefix="bc-constructor-control-") as directory:
            root, destination = self.fixture(directory)
            path = destination / "FunsExternal.lean"
            path.write_bytes(
                path.read_bytes().replace(b"Array U8 64#usize", b"Array U8 32#usize", 1)
            )
            with self.assertRaisesRegex(ValueError, "drift"):
                target.check_source(root, destination)

    def test_provenance_root_roster(self):
        with tempfile.TemporaryDirectory(prefix="bc-constructor-control-") as directory:
            root, destination = self.fixture(directory)
            path = destination / "provenance.json"
            provenance = json.loads(path.read_bytes())
            provenance["entries"].remove("new")
            path.write_text(json.dumps(provenance))
            with self.assertRaisesRegex(ValueError, "drift"):
                target.check_source(root, destination)


if __name__ == "__main__":
    unittest.main()
