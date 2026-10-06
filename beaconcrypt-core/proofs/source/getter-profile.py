#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the reviewed, finite Rust getter/Lean field-availability boundary.

This is a source tripwire and exhaustive phase-table comparison, not a Rust
compiler proof, a primitive representation proof, or a compromise theorem.
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
    "beaconcrypt/src/beacon.rs": "c9db3b5357ba13b6c2ef5865a150285a18180e966e52db65c572f3f815a538a8",
    "beaconcrypt/src/server.rs": "40efdd7a1a86e5dac0afee4bfa2c2433a66cf86e4fbdca640e2464241e1c0569",
    "beaconcrypt/src/ratchet.rs": "f5156cd43267eeec43b22875a7eef5fd8ec954feec4ee0b43288a7a1091b0c52",
    "beaconcrypt/src/shared.rs": "3b83ab0cabf2937db620f37e24f081f1ea4b37b0ae0be928de51620591beefd3",
    "beaconcrypt/src/cbinds.rs": "332e181706147f981479045d6feb9eb08d2fdc696589d07dbb81851851749793",
    "beaconcrypt/src/pybinds.rs": "9e454e6a1bbefdf4be2486ae7f1f25b6e563c17640a0ba8b49ebce65b757c20b",
    "beaconcrypt/src/lib.rs": "2eaad96abd3e7286c34a5613ba6b7de44133338322dccbc1c42b6c35313e1d91",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointLiveRead.lean": "c3866a86f826c1fdc57bf605f7f47832ce6f88344c747819aaa53af3915b76fb",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointOwnership.lean": "b802789bbb7ff115b50464900a759b1405db75e0c2212d5105021043971ceaec",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxProtocolReveals.lean": "452bff899641ed154e7a84110407ca07d828f54f29975b4330cba80bc50f42b8",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxLiveLineage.lean": "a8c5adb13126e1f0a7e0c84f3fc2614de0c5f45ff730d484c9aaaf15e7cb9193",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageFreshness.lean": "b62c79fa6a4716de40e138534117b023841fc3f7bc74928a47afb2f8401905de",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageReveals.lean": "5759dc6718dc7e5fc6e26f173deabb45d7dce988c27b5aa65091880dd293a911",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhJointIdentity.lean": "49f2746c41bf71f3b0e9bb966f4fdfa795d70fca95e11442660717ea9a3e3a6c",
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
