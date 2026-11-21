#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check the reviewed, finite Rust getter/Lean field-availability boundary.

This is a source tripwire and exhaustive phase-table comparison, not a Rust compiler proof, a primitive representation proof, or a compromise theorem.
The table covers the four named classical/KEM fields, not all secret material.
The Server's stored ML-DSA identity remains private adapter state, with a public-key getter; Beacon has no ML-DSA identity and the former fingerprint getter is gone.
Retained Init fields and session transcript metadata are public data; the finite table does not cover every secret-bearing API.
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
    "beaconcrypt/src/beacon.rs": "669482d038c8143ac25698bd4a1517480745c9b29c348d7d5c023992f813a845",
    "beaconcrypt/src/server.rs": "b5e6992a58eacce5b51d2624ff58206fbd56c744a97561146d07176a9242b66b",
    "beaconcrypt/src/ratchet.rs": "f9fa5f0b41821cc54fe5f626d18a853489300a7a2cde061efd8f7f0da277370d",
    "beaconcrypt/src/shared.rs": "98ff9810f5b1a8425a2177dab49c53eda6aa75cf5f78aedb1617712b4da17387",
    "beaconcrypt/src/cbinds.rs": "d6b84d410a604fa89ee95e2e237df94012e8ef7f6532130ad7c21a31eef04d46",
    "beaconcrypt/src/pybinds.rs": "47065efeda4b5908cfa4c2d08ed160a07de5b00fa2aa4a941d692727b76d93fb",
    "beaconcrypt/src/lib.rs": "59b2239615ff5c4bfa10db7a7162b078db5abdd10f143f9a3624937a6ff4a3ba",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointLiveRead.lean": "efbb903e307af5c8738b6b98cb952ab193aa7fe5a93a3bdd15a04fdeee1ef754",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhRegistrationJointOwnership.lean": "d7cc2f32a9f43076d5ad783e6a393df563bb3d76cc2722f933ea195aa3d88fbf",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxProtocolReveals.lean": "452bff899641ed154e7a84110407ca07d828f54f29975b4330cba80bc50f42b8",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxLiveLineage.lean": "95392feb7e6fbfa2e5c4c4953ed82e610704737ef573691f66df5d7ef50a187d",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageFreshness.lean": "b62c79fa6a4716de40e138534117b023841fc3f7bc74928a47afb2f8401905de",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/RawCtxSelectedMessageReveals.lean": "5759dc6718dc7e5fc6e26f173deabb45d7dce988c27b5aa65091880dd293a911",
    "beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhJointIdentity.lean": "d9b9c25ac490e14743fe77ebfe6ae476d01fd22b8e5dba763f3e5faacf0c1a37",
    "beaconcrypt-core/src/authentication.rs": "eef28a2a39d5134528173e40d22d02f9846319d2c2d67dc4b0e60d14d6637659",
    "beaconcrypt-core/src/ratchet.rs": "ff8981ab40ed42f406e04b1258063b8e5a9418af76cccc9f065f12160fa08f47",
    "beaconcrypt-core/src/session.rs": "4f83234a89c0fe8df60d68753930339f68208e2f14c464849177006af550c15e",
    "beaconcrypt/src/auth.rs": "f812e268cdd86cac01c43fdba5b25b944ebcdda1f6c03407203a6fbfa9ed16b5",
    "beaconcrypt/src/pqxdh.rs": "031465df2916c2fd118a28b3cb91f79484f535e2149c9c5bc48d3c5395dacf23",
    "beaconcrypt-core/src/agreement.rs": "7abf5bb56eb76ed461d52d0d6efff8bb18f165cc6831417a4f78f6e4d0672fa6",
    "beaconcrypt-core/src/registration.rs": "8be65a2c601a151d0ec9d2a570b929d55d72394edceac59599e1b11d741bba83",
    "beaconcrypt-core/src/pqxdh.rs": "0e90604b6537968f73873850ca7626f5019a9482c3225bb333d9a3ff555fde4f",
    "beaconcrypt-core/src/record_effects.rs": "dbdf79661a17c8d8c128ff349a7efe906d6713912e5510c9a0476b0c3efad2b5",
    "beaconcrypt-core/src/peer.rs": "5ace82b81a3e1c191223fd0629be3f00bbd321336baed0b568c9e432df0f9d77",
    "beaconcrypt-core/src/transport.rs": "795012d453a3ed209d6f8815eeedb2ccabaebd9a81d03f932d64f95aea9c3617",
    "beaconcrypt-crypto/src/crypto_aead.rs": "1b62a128ed169c81a45825ede6853b32ae715ce9ea96f9d53803e7fb461b9bf1",
    "beaconcrypt-crypto/src/crypto_generichash.rs": "292e806217ff105632f48ac32d89f3e9820b8a2b118810790be06e60104168f3",
    "beaconcrypt-crypto/src/crypto_kdf.rs": "8fc41159cc32f483a89ee4a273b9ebdf32fd75d23591580c991efb8b8c70cdf2",
    "beaconcrypt-crypto/src/crypto_kem.rs": "3c9a4f768a65f0b013c3b4a479d17be07574adc09305456692effc1ded5e2af5",
    "beaconcrypt-crypto/src/crypto_kx.rs": "d91d59ad9bc3e95ab8f8227c870282b039274bba07a5572696bf65deaa49b387",
    "beaconcrypt-crypto/src/crypto_scalarmult.rs": "e5eb492b32357a010c29c6655dc0e2397ab8747225a04b349613f310b570d2ca",
    "beaconcrypt-crypto/src/crypto_sign.rs": "8340a01b3c081ab79c621785cd4c6193b8af1fa483a4cd726b00ddc172fa011c",
    "beaconcrypt-crypto/src/lib.rs": "5d808be88690164585ab2c5c17f84396789defbf694694ab3150e709b7debc7f",
    "beaconcrypt-crypto/Cargo.toml": "dc34ba30e7cfbe1c17e27be5ffe2e49f151c9ba170fed7e42baf5bc09cec4560",
    "Cargo.lock": "2f9299d8f9844467ef90c9bbea76cdcacec7e1dffae7025930565ef56906b8e6",
    "beaconcrypt/src/collections.rs": "2eac87345a8673bad9fe89e705a65eb0f20c6ac67a2516872fedd599576b8334",
    "beaconcrypt/Cargo.toml": "bd72a2dd47102f91b1f927b90666f78674a9e4af91419dffad3ac69d7195a098",
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
        server, "identity_sk", "crypto_sign::SecretKey", "identity.identity_key", False
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
