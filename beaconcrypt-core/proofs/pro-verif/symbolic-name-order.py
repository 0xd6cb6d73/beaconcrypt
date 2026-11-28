#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Maintain the finite premises of the reviewed E20 symbolic trace argument.

This checker does not prove contextual equivalence or run ProVerif. It does
not reorder a computational sampler or change a maintained process.
The source pin is a drift guard for a classical projection whose record AD is
registration version 3 transcript AD151 but which omits the pinned-Server ML-DSA
response signature. It establishes no current version-3 refinement or reordering
across authentication and primitive failure. Reviewed scope is recorded in
var/formal-verification-analysis.md.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
TOKEN = re.compile(
    r'"(?:\\.|[^"\\])*"|\(\*.*?\*\)|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|==>|<=>|<>|<=|>=|&&|\|\||<-|->|[^\s]',
    re.S,
)
MACROS = {
    "fs-records-s2b.pvl": "FsS2bServer",
    "fs-records-b2s.pvl": "FsB2sServer",
}
TOKEN_SHA256 = {
    "extraction/lib.pvl": "858836a8c5009b167e0e1ec9b7067c8d84b683d3b126ae57dca4efb6e37dfe75",
    "fs-records-s2b.pvl": "8ccbb333d6366b0b94691049e0492fc36e1653184f64e0d2cf8c1c95ead4219f",
    "fs-records-b2s.pvl": "4960848b849207617d6413752874751ed4d9a2772fc26de693c297e368187654",
    "crypto.pvl": "6e2f24249ce5a0d061676c5aa7f8762bcb77214a0a152d2b559a3ea9afa3dcc1",
    "production-transcript-interface.pvl": "46f7c94e5a4ce6e63dc41cf212f40ba08e9db2acdd06805d057993146445dadb",
    "fs-common.pvl": "86ba720e2790fa558957cc8b755057bc41cce7feb2d0426e5be14c51dd581cdd",
}
SOURCE_SHA256 = {
    "beaconcrypt/src/server.rs": "f00083746068778587480f3f2eddb7175052427406fec0849324a11a57045ec4",
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
    "Cargo.lock": "96eb9ed30f1a0346926bbf0a2eb323d92f6c9cf698de8de3a118c49dc1243e4e",
    "beaconcrypt/src/collections.rs": "2eac87345a8673bad9fe89e705a65eb0f20c6ac67a2516872fedd599576b8334",
    "beaconcrypt/src/lib.rs": "59b2239615ff5c4bfa10db7a7162b078db5abdd10f143f9a3624937a6ff4a3ba",
    "beaconcrypt/Cargo.toml": "de9f6bd946f81149af8ed78f696f72c5fe5b47c9e93cd93b54c06d8f7409dbb1",
}
NAMES = ("ephemeral_secret", "kem_coins")


def tokens(text):
    return [m[0] for m in TOKEN.finditer(text) if not m[0].startswith("(*")]


def digest(parts):
    return hashlib.sha256(json.dumps(parts, separators=(",", ":")).encode()).hexdigest()


def locate(parts, needle):
    places = [i for i in range(len(parts)) if parts[i : i + len(needle)] == needle]
    if len(places) != 1:
        raise ValueError("expected one occurrence: " + " ".join(needle))
    return places[0]


def compare(text, macro):
    """Return two complete macro bodies differing only in restriction order."""
    parts = tokens(text)
    declaration = ["let", macro, "(", "obj", ":", "bitstring", ")", "="]
    start = locate(parts, declaration) + len(declaration)
    try:
        end = parts.index(".", start)
    except ValueError as error:
        raise ValueError("unterminated Server macro") from error
    body = parts[start:end]
    public_identity = tokens(
        "let server_identity = ed_public(SERVER_IDENTITY_SECRET) in"
    )
    draws = tokens("new ephemeral_secret: bitstring; new kem_coins: bitstring;")
    if body[: len(public_identity) + len(draws)] != public_identity + draws:
        raise ValueError("changed per-object fresh-name prefix/order")
    without = body[: len(public_identity)] + body[len(public_identity) + len(draws) :]
    cut = locate(without, tokens("let (dh1: bitstring, dh2: bitstring,"))
    crossed = without[len(public_identity) : cut]
    if any(name in crossed for name in NAMES):
        raise ValueError("a deferred name occurs in the crossed prefix")
    if any(
        word in crossed
        for word in (
            "out",
            "event",
            "new",
            "if",
            "else",
            "|",
            "!",
            "insert",
            "get",
            "phase",
            "sync",
        )
    ):
        raise ValueError("crossed prefix is not the reviewed input and pure let chain")
    bundle_input = tokens("in(c, bundle: bitstring) [precise];")
    if crossed[: len(bundle_input)] != bundle_input:
        raise ValueError("changed single precise bundle input")
    if crossed.count(";") != 1 or crossed.count("let") != 4:
        raise ValueError("changed one-input/four-let crossed prefix")
    if any("new" == word for word in without[:cut]):
        raise ValueError("unexpected prefix restriction")
    for name in NAMES:
        if body.count(name) < 2 or locate(body, tokens(f"new {name}: bitstring;")) < 0:
            raise ValueError("missing local fresh-name use")
    late = without[:cut] + draws + without[cut:]
    # Compare the entire untouched continuation, not just public key margins.
    late_cut = cut + len(draws)
    if late[late_cut:] != without[cut:]:
        raise ValueError("continuation changed")
    return {
        "early": body,
        "late": late,
        "crossed": crossed,
        "continuation": without[cut:],
        "early_sha256": digest(body),
        "late_sha256": digest(late),
        "continuation_sha256": digest(without[cut:]),
    }


def validate(directory=HERE, source_root=None):
    marker = (
        "(* @beaconcrypt-fidelity-v1 legacy_profiles.scope="
        "historical_classical_projection:no_current_runtime_refinement_claim *)"
    )
    if (directory / "production-transcript-interface.pvl").read_text().count(
        marker
    ) != 1:
        raise ValueError("E20 requires the reviewed classical-projection scope")
    if source_root is None:
        source_root = HERE.parents[2]
    for name, expected in TOKEN_SHA256.items():
        if digest(tokens((directory / name).read_text())) != expected:
            raise ValueError("review changed E20 process/theory: " + name)
    for name, expected in SOURCE_SHA256.items():
        if hashlib.sha256((source_root / name).read_bytes()).hexdigest() != expected:
            raise ValueError("review changed E20 source-order anchor: " + name)
    return {
        name: compare((directory / name).read_text(), macro)
        for name, macro in MACROS.items()
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.parse_args()
    result = validate()
    print(
        f"Symbolic name-order premises: {len(result)} complete Server continuations; paper trace argument only, no computational reorder or new solver verdict."
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        print("symbolic name-order check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
