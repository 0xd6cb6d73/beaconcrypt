#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Localize one pure optional mutable view in an isolated source fixture."""

from __future__ import annotations

import hashlib
from pathlib import Path

import extract_adapter_public_server_entry as entry

SOURCE = "beaconcrypt/src/server.rs"
ORIGINAL = "\tpub(crate) fn ratchet_manager_mut(&mut self, k: u64) -> Option<&mut RatchetManager> {\n\t\tself.known_ids\n\t\t\t.get_mut(&k)\n\t\t\t.map(EstablishedRemote::ratchet_mut)\n\t}"
LOCALIZED = "\tpub(crate) fn ratchet_manager_mut(&mut self, k: u64) -> Option<&mut RatchetManager> {\n\t\tmatch self.known_ids.get_mut(&k) {\n\t\t\tSome(remote) => Some(remote.ratchet_mut()),\n\t\t\tNone => None,\n\t\t}\n\t}"
ORIGINAL_SHA256 = "6f9720a072851241fcf1b826a118a30e8897837c8c05287e1ea7b8592edd9435"
BORROWED_TRY = (
    "\t\tencrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)"
)
BORROWED_MATCH = "\t\tlet Some(ratchet) = self.ratchet_manager_mut(k) else {\n\t\t\treturn None;\n\t\t};\n\t\tencrypt_message_with_ratchet(b, k, sender, &ad, ratchet)"


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def transform(source: str) -> str:
    if digest(ORIGINAL.encode()) != ORIGINAL_SHA256 or source.count(ORIGINAL) != 1:
        raise ValueError("unreviewed ordinary mutable peer accessor")
    if source.count(BORROWED_TRY) != 1:
        raise ValueError("ordinary mutable optional continuation changed")
    return source.replace(ORIGINAL, LOCALIZED, 1).replace(
        BORROWED_TRY, BORROWED_MATCH, 1
    )


def certificate(root: Path) -> dict:
    roster = entry.inputs(root)
    prepared = dict(roster)
    prepared[SOURCE] = digest(transform((root / SOURCE).read_text()).encode())
    return {
        "source_sha256": roster,
        "fixture_sha256": prepared,
        "normalization": {
            "original": ORIGINAL,
            "localized": LOCALIZED,
            "original_sha256": ORIGINAL_SHA256,
            "law": "AdapterPublicOrdinaryBorrow.optional_lens",
            "lens_law": "AdapterPublicOrdinaryBorrow.remote_lens",
            "borrowed_try": BORROWED_TRY,
            "borrowed_match": BORROWED_MATCH,
            "branch_law": "AdapterPublicOrdinaryBorrow.borrowed_option_branch",
            "effect_order": ["known_ids.get_mut", "EstablishedRemote.ratchet_mut"],
        },
    }


def prepare(root: Path, fixture: Path) -> dict:
    proof = certificate(root)
    entry.immutable_fixture(root, fixture)
    (fixture / SOURCE).write_text(transform((fixture / SOURCE).read_text()))
    verify(root, fixture, proof)
    return proof


def verify(root: Path, fixture: Path, proof: dict) -> None:
    if certificate(root) != proof:
        raise ValueError("ordinary source inputs changed during extraction")
    for name, expected in proof["fixture_sha256"].items():
        if name != "hax.toml" and digest((fixture / name).read_bytes()) != expected:
            raise ValueError("ordinary isolated fixture changed: " + name)
