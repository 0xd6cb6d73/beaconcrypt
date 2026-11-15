#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Negative controls for the curated-stub check; no extension build is needed."""

import unittest

import generate_python_stubs as stubs

EXCEPTIONS = {"PersistenceError": "ValueError"}
GENERATED = """
from _typeshed import Incomplete
MAX_MESSAGE_SIZE: Final[int]
class SnapshotHead:
    def __eq__(self, value: object, /) -> bool: ...
    def __ne__(self, value: object, /) -> bool: ...
class Beacon:
    def __new__(cls, /, kid: SupportsIndex) -> Beacon: ...
    def generate_registration(self, /) -> bytes | None: ...
def snapshot_head(data: SupportsGetItem[int, SupportsIndex]) -> SnapshotHead: ...
def __getattr__(name: str) -> Incomplete: ...
"""
CURATED = """
from typing import Literal, Protocol
MAX_MESSAGE_SIZE: Final[int]
class PersistenceError(ValueError):
    code: Literal["storage"]
class SnapshotHead:
    def __eq__(self, other: object) -> bool: ...
class _Store(Protocol):
    def load(self) -> bytes | None: ...
class Beacon:
    def __new__(cls, /, kid: int) -> Beacon: ...
    def generate_registration(self, /) -> bytes | None: ...
def snapshot_head(data: Sequence[int]) -> SnapshotHead: ...
"""


class CompareTests(unittest.TestCase):
    def check(self, curated, generated=GENERATED, exceptions=EXCEPTIONS):
        return stubs.compare(curated, generated, exceptions)

    def test_curated_typing_additions_are_accepted(self):
        self.assertEqual(self.check(CURATED), [])

    def test_removed_extension_member_is_rejected(self):
        curated = CURATED.replace(
            "    def generate_registration(self, /) -> bytes | None: ...\n",
            "    def generate_registration(self, /) -> bytes | None: ...\n"
            "    def mldsa_public_key(self, /) -> bytes: ...\n",
        )
        self.assertEqual(
            self.check(curated),
            ["not exported by the extension: Beacon.mldsa_public_key"],
        )

    def test_missing_extension_members_are_rejected(self):
        curated = CURATED.replace("def snapshot_head", "def other_head")
        self.assertEqual(
            self.check(curated),
            [
                "missing from beaconcrypt.pyi: def snapshot_head",
                "not exported by the extension: def other_head",
            ],
        )

    def test_raw_generated_stub_is_rejected_for_missing_exceptions(self):
        self.assertEqual(
            self.check(GENERATED),
            ["missing from beaconcrypt.pyi: class PersistenceError(ValueError)"],
        )

    def test_exception_base_and_unlisted_public_classes_are_checked(self):
        wrong_base = CURATED.replace(
            "PersistenceError(ValueError)", "PersistenceError(KeyError)"
        )
        self.assertEqual(
            self.check(wrong_base),
            [
                "not exported by the extension: class PersistenceError(KeyError)",
                "missing from beaconcrypt.pyi: class PersistenceError(ValueError)",
            ],
        )
        self.assertEqual(
            self.check(CURATED, exceptions={}),
            [
                "not exported by the extension: PersistenceError.code",
                "not exported by the extension: class PersistenceError(ValueError)",
            ],
        )

    def test_exception_declarations_are_read_from_rust_sources(self):
        source = (
            "pyo3::create_exception!(beaconcrypt, PersistenceError, PyValueError);\n"
            "pyo3::create_exception!(beaconcrypt, RowRegistrationError, RowError);\n"
            "pyo3::create_exception!(elsewhere, Ignored, PyValueError);\n"
        )
        self.assertEqual(
            stubs.exception_classes([source]),
            {"PersistenceError": "ValueError", "RowRegistrationError": "RowError"},
        )


class RepositoryStubTests(unittest.TestCase):
    def test_committed_stub_declares_every_extension_exception(self):
        exceptions = stubs.exception_classes(
            [(stubs.ROOT / source).read_text() for source in stubs.EXCEPTION_SOURCES]
        )
        self.assertEqual(
            set(exceptions),
            {"PersistenceError", "RowPersistenceError", "RowRegistrationError"},
        )
        surface = stubs.api_surface((stubs.ROOT / stubs.STUB_NAME).read_text())
        for name, base in exceptions.items():
            self.assertIn(f"class {name}({base})", surface)
        self.assertIn("PersistenceError.code", surface)
        self.assertNotIn("BeaconCryptBeacon.mldsa_public_key", surface)


if __name__ == "__main__":
    unittest.main()
