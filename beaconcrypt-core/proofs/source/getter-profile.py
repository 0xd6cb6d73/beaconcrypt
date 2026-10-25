#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the reviewed, finite Rust getter/Lean field-availability boundary.

This is a source tripwire and exhaustive phase-table comparison, not a Rust
compiler proof, a primitive representation proof, or a compromise theorem.
The table covers the four named classical/KEM fields, not all secret material.
ML-DSA identities are private adapter state; only their public keys and public
key fingerprints have new getters. See doc/impl/mldsa-source-pins.md.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
LEAN = "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/"
PHASES = ("Fresh", "FreshWithCoins", "InitSent", "Established", "Aborted")
PHASE_NAMES = dict(
    zip(PHASES, ("fresh", "freshWithCoins", "initSent", "established", "aborted"))
)
FIELDS = {
    "identity": ("identity_sk", "crypto_sign::SecretKey", "identity_key"),
    "kem": ("pq_sk", "crypto_kem::mlkem768::SecretKey", "pq_key"),
    "prekey": ("get_prekey_sk", "crypto_kx::SecretKey", "prekey"),
    "oneTime": ("get_onetime_sk", "crypto_kx::SecretKey", "onetime_key"),
}
# Filled with reviewed complete source files, including lifecycle and adapter
# visibility. Any change requires re-review, even outside a getter body.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "e041cd9d18eab646e1cf4266156295cc118ddfd30dabe2e407c7a14bc3e9956b",
    "beaconcrypt/src/server.rs": "6924195a2790f663e9ab3a9bd9aee0b05b0edfae384241f933565dd3f16f63f9",
    "beaconcrypt/src/ratchet.rs": "139db9986e11979050b85616fc02226863db593d1c2b46c56cd5c014eb5671b1",
    "beaconcrypt/src/shared.rs": "756ef890648966d53d742ca8fd06dbe4cd1ee612bf10758cdc985b4262157d42",
    "beaconcrypt/src/cbinds.rs": "82f6680efb5cc6b145944d9a1c3e6468c3394e2ce3c94876349683d288760c36",
    "beaconcrypt/src/pybinds.rs": "6dc9a248f6eba84f6bbc6cfdf16d741b45a61ea1428caacf3a4d1302a8b19dce",
    "beaconcrypt/src/lib.rs": "612958dd4b3e1f4cdab304c5a8d3d95e9c9daa0fe9a2ceaf7490bd1b2bf59270",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointLiveRead.lean": "c3866a86f826c1fdc57bf605f7f47832ce6f88344c747819aaa53af3915b76fb",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointOwnership.lean": "b802789bbb7ff115b50464900a759b1405db75e0c2212d5105021043971ceaec",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxProtocolReveals.lean": "452bff899641ed154e7a84110407ca07d828f54f29975b4330cba80bc50f42b8",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxLiveLineage.lean": "a8c5adb13126e1f0a7e0c84f3fc2614de0c5f45ff730d484c9aaaf15e7cb9193",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageFreshness.lean": "b62c79fa6a4716de40e138534117b023841fc3f7bc74928a47afb2f8401905de",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageReveals.lean": "5759dc6718dc7e5fc6e26f173deabb45d7dce988c27b5aa65091880dd293a911",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhJointIdentity.lean": "d9b9c25ac490e14743fe77ebfe6ae476d01fd22b8e5dba763f3e5faacf0c1a37",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "e4119ce56650add757b83144f728aabc84904219e4f3fc3678fdce7028ebca29",
    "beaconcrypt/src/pqxdh.rs": "4d786bf9f42a8f05204bc871f987f2b93440238672120af16c02f6837b11c52d",
    "beaconcrypt-core/src/agreement.rs": "cea8e603c7943f18ba79f95743cc113e3d16e8589c3614240b542ee3ac1109de",
    "beaconcrypt-core/src/registration.rs": "fb6f679499585a9d9976abaea31f8dbd8f68f53f6c0f1deb7462ee393acf9f25",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018",
    "beaconcrypt-core/src/record_effects.rs": "dbdf79661a17c8d8c128ff349a7efe906d6713912e5510c9a0476b0c3efad2b5",
    "beaconcrypt-core/src/peer.rs": "df4b0fc85a7a303f56908b13a4d90fb7d9233601040b43e035a99d341bd757bc",
    "beaconcrypt-core/src/transport.rs": "bc3f347f251cb07e44c47699c6fa3db4c9ae8b73c6d1d54c6f9eb54911a463a9",
}


def compact(text):
    return re.sub(r"\s+", "", text)


def balanced(text, start):
    """Extract a balanced brace block in the deliberately tiny getter grammar."""
    if text[start] != "{":
        raise ValueError("expected opening brace")
    depth = 0
    for i in range(start, len(text)):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[start : i + 1]
    raise ValueError("unterminated getter")


def getter(text, name, secret_type, optional):
    result = f"Option<&{secret_type}>" if optional else f"&{secret_type}"
    header = compact(f"pub fn {name}(&self) -> {result}")
    source = compact(text)
    if source.count(header + "{") != 1:
        raise ValueError("changed complete read-only getter signature: " + name)
    start = source.index(header + "{") + len(header)
    return balanced(source, start)[1:-1]


def rust_available(text, name, secret_type, member, optional):
    body = getter(text, name, secret_type, optional)
    if not optional:
        if body != f"&self.{member}.secret_key":
            raise ValueError("changed identity projection")
        return set(PHASES)
    match = re.fullmatch(
        r"match&self\.state\{(.+)=>Some\(&" + member + r"\.secret_key\),_=>None,\}",
        body,
    )
    if match is None:
        raise ValueError("changed optional getter expression: " + name)
    phases = []
    for pattern in match[1].split("|"):
        arm = re.fullmatch(r"BeaconState::(\w+)\{" + member + r",\.\.\}", pattern)
        if arm is None or arm[1] not in PHASES or arm[1] in phases:
            raise ValueError("changed or duplicated getter phase: " + name)
        phases.append(arm[1])
    return set(phases)


def definition(text, name):
    """Only inspect the named complete expression, ending at the next doc item."""
    match = re.search(
        r"^def " + re.escape(name) + r"\b.*? :=\n(.*?)(?=\n\n/--)", text, re.M | re.S
    )
    if match is None:
        raise ValueError("missing complete Lean definition: " + name)
    return compact(match[1])


def lean_available(live, ownership):
    active = definition(ownership, "activeKey")
    if active != compact("""
      match owner.beacon.phase with
      | .fresh _ _ keys | .freshWithCoins _ _ _ keys | .initSent _ _ _ keys => some keys
      | .established _ _ _ | .aborted _ => none
    """):
        raise ValueError("changed complete current KEM projection")
    value = definition(live, "value")
    if value != compact("""
      match field with
      | .identity => some (.identity owner.beacon.identity)
      | .kem => (activeKey owner).map fun pair => .kem pair.2
      | _ => localValue field owner
    """):
        raise ValueError("changed complete native field projection")
    local = definition(live, "localValue")
    if local != compact("""
      match field, owner.beacon.phase with
      | .prekey, .fresh _ scalar _ | .prekey, .freshWithCoins _ scalar _ _ | .prekey, .initSent _ scalar _ _ => some (.prekey scalar)
      | .oneTime, .freshWithCoins _ _ scalar _ | .oneTime, .initSent _ _ scalar _ => some (.oneTime scalar)
      | .kernel, .established _ _ kernel => some (.kernel kernel)
      | _, _ => none
    """):
        raise ValueError("changed complete local field projection")
    # Independently extract the supported branches from those checked complete
    # definitions rather than copying the Rust presence table into this side.
    kem = set(
        re.findall(r"\|\.([A-Za-z][A-Za-z0-9]*)_+keys", active.split("=>somekeys")[0])
    )
    result = {"identity": set(PHASE_NAMES.values()), "kem": kem}
    for field in ("prekey", "oneTime"):
        result[field] = set(
            re.findall(r"\|\." + field + r",\.([A-Za-z][A-Za-z0-9]*)_", local)
        )
    return result


def compare(beacon, server, live, ownership):
    actual = {}
    for field, (name, secret_type, member) in FIELDS.items():
        actual[field] = rust_available(
            beacon, name, secret_type, member, field != "identity"
        )
    modeled = lean_available(live, ownership)
    rows = []
    for field in FIELDS:
        for phase in PHASES:
            present = phase in actual[field]
            if present != (PHASE_NAMES[phase] in modeled[field]):
                raise ValueError(f"Rust/Lean getter presence mismatch: {field}/{phase}")
            rows.append(
                {"owner": "Beacon", "field": field, "phase": phase, "present": present}
            )
    rust_available(
        server, "identity_sk", "crypto_sign::SecretKey", "identity_key", False
    )
    rows.append(
        {"owner": "Server", "field": "identity", "phase": "live", "present": True}
    )
    return rows


def validate(root=ROOT):
    for path, expected in SOURCE_SHA256.items():
        if hashlib.sha256((root / path).read_bytes()).hexdigest() != expected:
            raise ValueError("review changed getter/source/freshness boundary: " + path)
    return compare(
        (root / "beaconcrypt/src/beacon.rs").read_text(),
        (root / "beaconcrypt/src/server.rs").read_text(),
        (root / (LEAN + "PqxdhRegistrationJointLiveRead.lean")).read_text(),
        (root / (LEAN + "PqxdhRegistrationJointOwnership.lean")).read_text(),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json", action="store_true", help="print the complete checked phase table"
    )
    args = parser.parse_args()
    rows = validate()
    if args.json:
        print(json.dumps(rows, indent=2))
    print(
        "Getter profile: 20 Beacon phase cases agree; Server identity remains live. No secrecy or network-compromise claim."
    )
