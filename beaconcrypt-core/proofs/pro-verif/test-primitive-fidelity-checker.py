#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Reject drift in the encoding profile and its checked source derivative."""

from dataclasses import replace
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "primitive_checker", Path(__file__).with_name("check-primitive-fidelity.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class FidelityTests(unittest.TestCase):
    def test_manifest(self):
        CHECKER.validate_targets()
        self.assertEqual(len(CHECKER.TARGETS), 9)
        self.assertEqual(sum(t.cls == "security" for t in CHECKER.TARGETS), 4)
        self.assertEqual({t.bound for t in CHECKER.TARGETS}, {2})

    def mutate(self, filename, old, new):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            for name in (
                "crypto.pvl",
                "crypto-fs-encoding.pvl",
                "fs-registration.pvl",
                "fs-encoding-registration.pvl",
            ):
                shutil.copy(CHECKER.HERE / name, directory / name)
            path = directory / filename
            source = path.read_text()
            self.assertIn(old, source)
            path.write_text(source.replace(old, new, 1))
            with self.assertRaises(ValueError):
                CHECKER.check_derivative(directory)

    def test_drop_server_guard(self):
        self.mutate("fs-encoding-registration.pvl", CHECKER.SERVER_GATE, "")

    def test_drop_beacon_guard(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "  (* Beacon core rejection precedes any root/ratchet use. *)\n  "
            + CHECKER.SERVER_GATE,
            "",
        )

    def test_remove_zero_event(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "event FsServerZeroRejected(obj, server_identity, identity, registration_id);",
            "",
        )

    def test_zero_rejection_consumes_identifier(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "event FsServerZeroRejected(obj, server_identity, identity, registration_id);",
            "event FsServerZeroRejected(obj, server_identity, identity, registration_id); let slot_1 = registration_id in",
        )

    def test_wrong_root_dh(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "fs_root_dh2(dh2, dh3)",
            "fs_root_dh2(dh3, dh3)",
        )

    def test_wrong_pin(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "if response_server_identity = server_identity then",
            "if true then",
        )

    def test_wrong_sequence(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "frame_sequence = fs_seq(1)",
            "frame_sequence = fs_seq(2)",
        )

    def test_wrong_guard_placement(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            "if fs_dh_nonzero(dh1, dh2, dh3, dh4) then\n      (",
            "( if fs_dh_nonzero(dh1, dh2, dh3, dh4) then",
        )

    def test_wrong_guard_field(self):
        self.mutate(
            "fs-encoding-registration.pvl",
            CHECKER.SERVER_GATE,
            "if fs_dh_nonzero(dh1, dh2, dh3, dh3) then",
        )

    def test_kdf_primitive_drift(self):
        self.mutate("crypto-fs-encoding.pvl", "hkdf_second_32", "hkdf_first_32")

    def test_signature_primitive_drift(self):
        self.mutate("crypto-fs-encoding.pvl", "= message.", "= signing_key.")

    def test_registration_baseline_drift(self):
        self.mutate(
            "fs-registration.pvl",
            "frame_sequence = fs_seq(1)",
            "frame_sequence = fs_seq(2)",
        )

    def test_unknown_and_unconfirmed_receipts_fail(self):
        target = CHECKER.TARGETS[0]
        receipt = (
            "RESULT "
            + target.results[0]
            + "\nVerification summary:\nQuery "
            + target.results[0]
            + "\n"
        )
        CHECKER.FS.check_output(receipt, target)
        for bad in (
            receipt.replace("is true.", "cannot be proved."),
            receipt.replace(
                "Verification summary:",
                "A trace has been found.\nVerification summary:",
            ),
            receipt.replace("FsBeaconEstablished", "FsBeaconStarted"),
        ):
            with self.assertRaises(ValueError):
                CHECKER.FS.check_output(bad, target)

    def test_bounds_classes_and_hooks(self):
        target = CHECKER.TARGETS[0]
        for bad in (
            replace(target, bound=3),
            replace(target, cls="witness"),
            replace(target, hooks=(CHECKER.FS.NOCHECK, CHECKER.FS.BINDING)),
            replace(target, failstop=True),
            replace(target, inverted=True),
        ):
            with self.assertRaises(ValueError):
                CHECKER.validate_targets((bad, *CHECKER.TARGETS[1:]))

    def test_source_boundary_drift(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            directory = root / "beaconcrypt-core/proofs/pro-verif"
            directory.mkdir(parents=True)
            core = root / "beaconcrypt-core/src"
            core.mkdir()
            source = CHECKER.HERE.parents[2] / "beaconcrypt-core/src/pqxdh.rs"
            shutil.copy(source, core / "pqxdh.rs")
            shutil.copy(CHECKER.HERE / "fs-encoding-interface.pvl", directory)
            CHECKER.check_source_boundary(directory)
            for before, after in (
                ("|| is_all_zero(&secrets.dh4)", ""),
                ("InvalidDhOutput", "IdentityMismatch"),
            ):
                (core / "pqxdh.rs").write_text(
                    source.read_text().replace(before, after)
                )
                with self.assertRaises(ValueError):
                    CHECKER.check_source_boundary(directory)
            shutil.copy(source, core / "pqxdh.rs")
            interface = directory / "fs-encoding-interface.pvl"
            interface.write_text(
                interface.read_text().replace(
                    "dh4 <> x25519_all_zero", "dh3 <> x25519_all_zero"
                )
            )
            with self.assertRaises(ValueError):
                CHECKER.check_source_boundary(directory)

    def test_missing_new_query_target(self):
        with self.assertRaises(ValueError):
            CHECKER.validate_targets(CHECKER.TARGETS[:-1])


if __name__ == "__main__":
    unittest.main()
