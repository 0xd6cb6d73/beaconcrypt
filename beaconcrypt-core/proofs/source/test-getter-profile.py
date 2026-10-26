#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Regression checks for the finite getter/phase source boundary."""

import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SPEC = importlib.util.spec_from_file_location(
    "getter_profile", Path(__file__).with_name("getter-profile.py")
)
PROFILE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROFILE)


class GetterProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.beacon = (PROFILE.ROOT / "beaconcrypt/src/beacon.rs").read_text()
        cls.server = (PROFILE.ROOT / "beaconcrypt/src/server.rs").read_text()
        cls.live = (
            PROFILE.ROOT / (PROFILE.LEAN + "PqxdhRegistrationJointLiveRead.lean")
        ).read_text()
        cls.ownership = (
            PROFILE.ROOT / (PROFILE.LEAN + "PqxdhRegistrationJointOwnership.lean")
        ).read_text()

    def compare(self, beacon=None, server=None, live=None, ownership=None):
        return PROFILE.compare(
            beacon or self.beacon,
            server or self.server,
            live or self.live,
            ownership or self.ownership,
        )

    def test_complete_phase_table(self):
        rows = PROFILE.validate()
        self.assertEqual(len(rows), 21)
        self.assertEqual(len({(r["owner"], r["field"], r["phase"]) for r in rows}), 21)
        terminal = [
            r
            for r in rows
            if r["owner"] == "Beacon" and r["phase"] in ("Established", "Aborted")
        ]
        self.assertEqual(
            [r["present"] for r in terminal],
            [True, True, False, False, False, False, False, False],
        )

    def test_identity_value_and_server_value(self):
        for role in ("beacon", "server"):
            original = getattr(self, role)
            member = "identity_key" if role == "beacon" else "identity.identity_key"
            needle = f"&self.{member}.secret_key"
            self.assertEqual(original.count(needle), 1)
            source = original.replace(needle, f"&self.{member}.public_key", 1)
            with self.assertRaises(ValueError):
                self.compare(**{role: source})

    def test_private_collection_hasher_cannot_be_substituted(self):
        relative = "beaconcrypt/src/collections.rs"
        self.assertIn(relative, PROFILE.SOURCE_SHA256)
        path = PROFILE.ROOT / relative
        original = Path.read_bytes
        source = original(path)
        before = b"SipHasher13::new_with_key(&self.0)"
        self.assertEqual(source.count(before), 1)
        changed = source.replace(before, b"SipHasher13::new_with_key(&[0; 16])", 1)

        def read_bytes(candidate):
            return changed if candidate == path else original(candidate)

        with (
            mock.patch.object(Path, "read_bytes", read_bytes),
            self.assertRaisesRegex(ValueError, relative),
        ):
            PROFILE.validate()

    def test_every_secret_getter_rejects_wrong_field(self):
        for field, (name, secret_type, member) in PROFILE.FIELDS.items():
            body = PROFILE.getter(self.beacon, name, secret_type, field != "identity")
            source = PROFILE.compact(self.beacon).replace(
                body, body.replace(".secret_key", ".public_key"), 1
            )
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.compare(beacon=source)

    def test_changed_presence_is_detected(self):
        for field in ("kem", "prekey", "oneTime"):
            name, secret_type, member = PROFILE.FIELDS[field]
            body = PROFILE.getter(self.beacon, name, secret_type, True)
            changed = body.replace("BeaconState::InitSent", "BeaconState::Established")
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.compare(
                    beacon=PROFILE.compact(self.beacon).replace(body, changed, 1)
                )

    def test_mutating_or_duplicate_getter_rejected(self):
        for source in (
            self.beacon.replace("pub fn pq_sk(&self)", "pub fn pq_sk(&mut self)"),
            self.beacon
            + "\npub fn pq_sk(&self) -> Option<&crypto_kem::mlkem768::SecretKey> { None }",
        ):
            with self.assertRaises(ValueError):
                self.compare(beacon=source)

    def test_extra_getter_effect_rejected(self):
        source = self.beacon.replace(
            "Some(&pq_key.secret_key)", "{ log_secret(); Some(&pq_key.secret_key) }"
        )
        with self.assertRaises(ValueError):
            self.compare(beacon=source)

    def test_lean_current_field_and_erasure_changes_rejected(self):
        for name, source in (
            (
                "live",
                self.live.replace(".oneTime, .initSent", ".oneTime, .established"),
            ),
            (
                "live",
                self.live.replace("some (.identity owner.beacon.identity)", "none"),
            ),
            (
                "ownership",
                self.ownership.replace(
                    "| .established _ _ _ | .aborted _ => none",
                    "| .established _ _ _ | .aborted _ => some oldKeys",
                ),
            ),
        ):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.compare(**{name: source})

    def test_whitespace_does_not_change_getter_table(self):
        self.assertEqual(
            self.compare(), self.compare(beacon=PROFILE.compact(self.beacon))
        )

    def test_each_full_source_boundary_change_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in PROFILE.SOURCE_SHA256:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((PROFILE.ROOT / name).read_bytes())
            self.assertEqual(PROFILE.validate(root), PROFILE.validate())
            for name in PROFILE.SOURCE_SHA256:
                path = root / name
                original = path.read_bytes()
                path.write_bytes(
                    original + b"\n// changed visibility/lifecycle/freshness boundary\n"
                )
                with self.subTest(path=name), self.assertRaises(ValueError):
                    PROFILE.validate(root)
                path.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
