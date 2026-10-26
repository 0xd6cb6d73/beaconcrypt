#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Maintain the finite premises of the reviewed E20 symbolic trace argument.

This checker does not prove contextual equivalence or run ProVerif. It does
not reorder a computational sampler or change a maintained process.
The source pin concerns the classical projection after the mandatory ML-DSA
guard; it establishes no reordering across that guard or primitive failure.
See doc/impl/mldsa-source-pins.md for the reviewed source changes.
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
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-records-s2b.pvl": "cdadbc31c34fbe7bc6b592bdcd21f88427c420af0586e036aad80f171ffd4e22",
    "fs-records-b2s.pvl": "7fc2a35fefe9cfa0aa0e93a641b73523e8d1d2345baa55edf717772ad1bdaf3a",
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
}
SOURCE_SHA256 = {
    "beaconcrypt/src/server.rs": "c47d482bfd41e9d93623acf94319a36cadb8e2ab413df07ea7678e64209e67dc",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "45b2513e304b4d4b12b41ca15ff15b94db54886e302453971d99ec0f1ce4f884",
    "beaconcrypt/src/pqxdh.rs": "f3b880ec118bebfd49851156588e681da40f50761470fbacc6940fd69cabc319",
    "beaconcrypt-core/src/agreement.rs": "cea8e603c7943f18ba79f95743cc113e3d16e8589c3614240b542ee3ac1109de",
    "beaconcrypt-core/src/registration.rs": "fb6f679499585a9d9976abaea31f8dbd8f68f53f6c0f1deb7462ee393acf9f25",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018",
    "beaconcrypt-core/src/record_effects.rs": "dbdf79661a17c8d8c128ff349a7efe906d6713912e5510c9a0476b0c3efad2b5",
    "beaconcrypt-core/src/peer.rs": "df4b0fc85a7a303f56908b13a4d90fb7d9233601040b43e035a99d341bd757bc",
    "beaconcrypt-core/src/transport.rs": "bc3f347f251cb07e44c47699c6fa3db4c9ae8b73c6d1d54c6f9eb54911a463a9",
    "beaconcrypt-crypto/src/crypto_aead.rs": "1b62a128ed169c81a45825ede6853b32ae715ce9ea96f9d53803e7fb461b9bf1",
    "beaconcrypt-crypto/src/crypto_generichash.rs": "292e806217ff105632f48ac32d89f3e9820b8a2b118810790be06e60104168f3",
    "beaconcrypt-crypto/src/crypto_kdf.rs": "1a5d147f6de89829b7259d41fd28ec6a206ca27531cc193048c1b3e79dbfac7f",
    "beaconcrypt-crypto/src/crypto_kem.rs": "3c9a4f768a65f0b013c3b4a479d17be07574adc09305456692effc1ded5e2af5",
    "beaconcrypt-crypto/src/crypto_kx.rs": "d91d59ad9bc3e95ab8f8227c870282b039274bba07a5572696bf65deaa49b387",
    "beaconcrypt-crypto/src/crypto_scalarmult.rs": "e5eb492b32357a010c29c6655dc0e2397ab8747225a04b349613f310b570d2ca",
    "beaconcrypt-crypto/src/crypto_sign.rs": "8340a01b3c081ab79c621785cd4c6193b8af1fa483a4cd726b00ddc172fa011c",
    "beaconcrypt-crypto/src/lib.rs": "5d808be88690164585ab2c5c17f84396789defbf694694ab3150e709b7debc7f",
    "beaconcrypt-crypto/Cargo.toml": "dc34ba30e7cfbe1c17e27be5ffe2e49f151c9ba170fed7e42baf5bc09cec4560",
    "Cargo.lock": "fa0bcc041f43039e1f186aa7b596260a5c49180d8bf7010eb2e09d6d4be7d17d",
    "beaconcrypt/src/collections.rs": "2eac87345a8673bad9fe89e705a65eb0f20c6ac67a2516872fedd599576b8334",
    "beaconcrypt/src/lib.rs": "df6cac5a7de0938f7b7f77a03d46320ad88617b48c9bf7f7904aa7551b14bfa4",
    "beaconcrypt/Cargo.toml": "c7a3237a77de3606618b538cdb19a0e41ab1c9271302488b872a524db49bb50a",
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
        "classical_projection:MLDSA_guards_not_globally_lifted *)"
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
