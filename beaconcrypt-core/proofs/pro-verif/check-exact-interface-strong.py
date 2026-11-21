#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact-interface Kr3 active secrecy and public-response lookup auxiliaries.

The private-application paired source/context argument is separately reviewed.
No public optional-plaintext or completed computational/global result is claimed.
"""

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FS = load("exact_strong_fs", "check-free-schedule.py")
ACTIVE = load("exact_strong_active", "check-active-strong-secrecy.py")
MODELS = load("exact_strong_models", "exact-interface-strong-models.py")
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "fs-registration-binding.pvl",
)


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    direction: str
    kind: str
    query: str
    result: str
    process: str
    bound: int = 3

    @property
    def results(self):
        return (self.result,)

    @property
    def control(self):
        return self.kind != "equivalence"

    def expected_traces(self):
        return int(self.cls == "negative-control")

    def libraries(self):
        prefix = "exact-interface-strong-" + self.direction
        old = "record-origin" if self.direction == "b2s" else "tasking-origin"
        if self.kind == "equivalence":
            registration = "exact-interface-strong-registration.pvl"
            receive = "-receive.pvl"
            sends = "-sends.pvl"
            main = ".pvl"
        else:
            registration = "registration-set-admission.pvl"
            receive = (
                "-origin-receive.pvl"
                if self.kind == "origin"
                else "-control-receive.pvl"
            )
            sends = "-" + self.kind + "-sends.pvl"
            main = "-origin.pvl" if self.kind == "origin" else "-auxiliary.pvl"
        return LIBRARIES + (
            registration,
            "fs-pending-response.pvl",
            prefix + receive,
            old + "-kr3.pvl",
            prefix + sends,
            prefix + main,
        )


TARGETS = (
    Target(
        "SSX-b2s",
        "security",
        "b2s",
        "equivalence",
        "exact-interface-strong-b2s.pv",
        "Observational equivalence is true.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b",
        "security",
        "s2b",
        "equivalence",
        "exact-interface-strong-s2b.pv",
        "Observational equivalence is true.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-origin",
        "security",
        "b2s",
        "origin",
        "exact-interface-strong-b2s-origin.pv",
        "event(ExactStrongFinishedResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) && event(L2SelectedIdentity(k)) ==> event(ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) is true.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-origin",
        "security",
        "s2b",
        "origin",
        "exact-interface-strong-s2b-origin.pv",
        "event(ExactStrongFinishedResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) && event(S2bSelectedIdentity(k)) ==> event(ExactStrongBuiltResponse(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),response_2,root_4)) is true.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-leak",
        "negative-control",
        "b2s",
        "leak",
        "exact-interface-strong-b2s-leak.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-leak",
        "negative-control",
        "s2b",
        "leak",
        "exact-interface-strong-s2b-leak.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "S2bMain(false)",
        3,
    ),
    Target(
        "SSX-b2s-ungated",
        "negative-control",
        "b2s",
        "ungated",
        "exact-interface-strong-b2s-ungated.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "L2Main(false)",
        3,
    ),
    Target(
        "SSX-s2b-ungated",
        "negative-control",
        "s2b",
        "ungated",
        "exact-interface-strong-s2b-ungated.pv",
        "not (event(ExactStrongProbe(true,m)) && attacker(m)) is false.",
        "S2bMain(false)",
        3,
    ),
)

# Owner-approved per-target resource exception (owner decision of 2026-11-13). The group
# limits are the --timeout and --address-space-kib arguments; the Makefile passes the
# approved 1800 s and 10 GiB, which every other target keeps. SSX-b2s passed in 1736 s
# in the third transcript-AD port pass (pvport3, 47000 rules). Its two pvport4 runs hit
# the 1800 s limit at 43600 and 44600 rules on a loaded machine; both logs are identical
# prefixes of the passing pvport3 log, so the inputs (changed only in comments) did not
# change its saturation. This is a resource change only: no model, query, bound or
# expected verdict changes. SSX-b2s alone gets 2700 s, 1.5 times the 1800 s group limit
# and about 1.56 times its pvport3 time; its address space stays at the group limit. A
# larger group limit still applies.
LIMIT_EXCEPTIONS = {
    "SSX-b2s": (2700, None),
}


def target_limits(target, timeout, address_space_kib):
    """The (seconds, address-space KiB) of one target: the group limits, raised to the
    owner-approved exception when the target is that entry of the roster."""
    exception = LIMIT_EXCEPTIONS.get(target.name)
    if exception is None or target not in TARGETS:
        return timeout, address_space_kib
    seconds, space = exception
    if space is not None and address_space_kib:
        address_space_kib = max(address_space_kib, space)
    return max(timeout, seconds), address_space_kib


def validate_limit_exceptions():
    """The only exception is the owner-approved time limit of the SSX-b2s equivalence."""
    for name, (seconds, space) in LIMIT_EXCEPTIONS.items():
        matches = [target for target in TARGETS if target.name == name]
        if (
            len(matches) != 1
            or matches[0].cls != "security"
            or matches[0].kind != "equivalence"
            or matches[0].direction != "b2s"
        ):
            raise ValueError(f"{name}: a limit exception names the SSX-b2s equivalence")
        if seconds > 2700 or space is not None:
            raise ValueError(f"{name}: limit exception above the owner-approved values")


TOKEN_SHA256 = {
    "application-secrecy-b2s-leak-sends.pvl": "101c4ed638ee169413fbebf99fe5272ea478cc0078d1c9cb52bbc0e93090bf9f",
    "application-secrecy-b2s-leak.pv": "c1245b0b56a1c9d0157baa3c1433e22ec362c177f79f014cde264fb95fc75f81",
    "application-secrecy-b2s-receive.pvl": "abc719ac4d0435ccdd3e5484b3088b1d351fac1e42b9dcd9dd38bba2084fec0e",
    "application-secrecy-b2s-sends.pvl": "5e3cd1beb81e955767afc6fa51362768d8426f09e048b1db461a8ec73e80f847",
    "application-secrecy-b2s.pv": "c1245b0b56a1c9d0157baa3c1433e22ec362c177f79f014cde264fb95fc75f81",
    "application-secrecy-b2s.pvl": "a21bf81c66d77b2403ce3763283ce76236ce1eb842dca5438ec39f91b290c4fe",
    "application-secrecy-s2b-leak-sends.pvl": "a9b7ed262b7de336d1d9697ba1cecd617a6548a71a4b34f43d9b9f79c63added",
    "application-secrecy-s2b-leak.pv": "2c36eef0e4b73451b3c441110a4113abd7ab804e21683670369d3429b4164eeb",
    "application-secrecy-s2b-receive.pvl": "829e8086b22ca8972d5f6b6e50207982978a5aff76922f4fb9bdea3d6908c23d",
    "application-secrecy-s2b-sends.pvl": "0ade487b09cbe3158bb57663da7d5ad0e57b45e9fb3e7966bad008b751cc1ce7",
    "application-secrecy-s2b.pv": "2c36eef0e4b73451b3c441110a4113abd7ab804e21683670369d3429b4164eeb",
    "application-secrecy-s2b.pvl": "56cf33e1ae1285698d3dc5a0eaa3bc96eb56c5422203bf98fe9932a888825ab1",
    "crypto.pvl": "6e2f24249ce5a0d061676c5aa7f8762bcb77214a0a152d2b559a3ea9afa3dcc1",
    "delayed-response.pvl": "74f5324610516333aae3140d32cf99b768a31622f66c409c81a32304ad57b050",
    "extraction/lib.pvl": "858836a8c5009b167e0e1ec9b7067c8d84b683d3b126ae57dca4efb6e37dfe75",
    "fs-common.pvl": "86ba720e2790fa558957cc8b755057bc41cce7feb2d0426e5be14c51dd581cdd",
    "fs-pending-response.pvl": "18c8d2371eeba3371f4b465b62077871d94c5dcac9e4ba26e698c3ba8de82672",
    "fs-registration-binding.pvl": "2f3fdb8967409447053a29f75e79585172326bcb04dfa417345896025f82edfd",
    "production-transcript-interface.pvl": "46f7c94e5a4ce6e63dc41cf212f40ba08e9db2acdd06805d057993146445dadb",
    "record-origin-auth.pv": "23447544587bbb618572d7bcdec8fb33db9d7eea339b39e4611dd53f25a5f6e4",
    "record-origin-cache-receive.pvl": "fd5755370828ded315488f66c00d70aa534588d6a3a7004e15338c0d65f5a0e2",
    "record-origin-cache-sends.pvl": "b87e459475d5f04a45fbd24f1d373c20cab0afd7534e3e0c9e1111acbcf7e3e7",
    "record-origin-cache-witness.pv": "37a38897cf13ba3886b7e817a975335e9149f0285bcade6c0fce7d74193eb281",
    "record-origin-cache.pvl": "14775b7fb6adfb6eac40adc2408d309e668902005aabad5ea89a1c027bdc49d5",
    "record-origin-identity.pv": "344b162cada803c6a6f0ec8e54ccf3bc74c8e63860b44dbcc9cbc79a0f195fea",
    "record-origin-kr2.pvl": "ade2896d6f22a8aeeb5239857e76d357b0b6213e2db23f3ce36178a943078a45",
    "record-origin-kr3.pvl": "f817aff4f11b7d8ba2729349d7df9ebc77f06ac7f0b39b7b2ed98fe07e1948b5",
    "record-origin-leak-control.pv": "718f6de1b4226f28d15c0d7bacdc2ac22d8247db7644c06da3ec7cc5d7bd0406",
    "record-origin-receive.pvl": "ed55b9872958c9ce8026a79ae3659a23454663ca2b6d5916ed01f2da7364519d",
    "record-origin-sends.pvl": "221a9af907cb8bfc8c1a8a9610867f21455c634f9b27d2180bfd0599d21dd67b",
    "record-origin.pvl": "6f7da48dcf89c4cace32a2c1211ad4e89b8b32d8a2c483efb419dbedc7efa0e3",
    "registration-provenance.pvl": "c75baa6a7ffe8c8a320365940a19bbe91f72c7263ac91b04382e866ecd1f8349",
    "registration-set-admission.pvl": "739fa116a13001f7a437dd4591ae8a0083cb6dd988f266a663acdef805a63e49",
    "tasking-origin-auth.pv": "27d45efd8e7da6907ff2b0a2d3fb9e069de29dfefd220f3afb2543f5b3933590",
    "tasking-origin-cache-receive.pvl": "a5e4f61fc4cfd66b43022daf8597587c61404dc83920db6ab0c66684437e49d5",
    "tasking-origin-cache-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin-cache-witness.pv": "a82b2aa9fffcb98a91ae5085030017eb2e011b6c71cf6602c615396c46652b67",
    "tasking-origin-cache.pvl": "587ec1de1bdf3374a96a65940c30deac197f89f11aa63c05372f38c565515f41",
    "tasking-origin-identity.pv": "f2c9e537971e1be783a2333fe1f0e547cee8b6b64ddce57837698de9675c642d",
    "tasking-origin-initial.pv": "8cdc8c218aec8644b1b99c4911bfea3157f9f42b47620f0d78da89a3208cdf41",
    "tasking-origin-kr2.pvl": "ecb0f4d5b2bcd0bd9bf9bd2770d8f3db124ed5d9650a67f72bf1257558d357bb",
    "tasking-origin-kr3.pvl": "90bdf7d544fe3e0b66ee9a854b6df0f702610b3382d796c52837f442fc525ef6",
    "tasking-origin-leak-control.pv": "bf5896bdda3af995c47e9f250a978706ed05e19f13954bc0217ab1b243d64c28",
    "tasking-origin-receive.pvl": "cde8076d5e39b37015d3b4014eb6f78ba6d2936ce5051d899aed19415a66ac82",
    "tasking-origin-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin.pvl": "587ec1de1bdf3374a96a65940c30deac197f89f11aa63c05372f38c565515f41",
    "exact-interface-strong-b2s-auxiliary.pvl": "a21bf81c66d77b2403ce3763283ce76236ce1eb842dca5438ec39f91b290c4fe",
    "exact-interface-strong-b2s-control-receive.pvl": "6ff16f4611ca9f001e736e7fd1e7b9d1cc4f2086c5ec52ed4034938f0e2feb7d",
    "exact-interface-strong-b2s-leak-sends.pvl": "e3eeec9eb2948af166f36b2db08fc7054af25d6e517e5b939e717bbd026c5f19",
    "exact-interface-strong-b2s-leak.pv": "97c53615086d3f663ae1de1dad3e2296a90344d6a19ec5851afcccb577db0d84",
    "exact-interface-strong-b2s-origin-receive.pvl": "6b5ac22c9fff06e79029e3016793c532731a2b4ec846e1f1d6e20d6902b8c08d",
    "exact-interface-strong-b2s-origin-sends.pvl": "66db1c17862ce80332bf62c2d51b1f58b183219801e75c79a12787d51db02f05",
    "exact-interface-strong-b2s-origin.pv": "2e7d1269144bc2b2b1d453c4e548209e21673e6f7bd11c1bd6eee6303b9bd8b5",
    "exact-interface-strong-b2s-origin.pvl": "dd5ff0bb8b06896ddc47aea3229d65582dc1d1433520d0f4d8a2860a8ce2e279",
    "exact-interface-strong-b2s-receive.pvl": "4ea1e57f24a76d22c14b67d191c3279cc82e4db9bcc01f6eb26390c9010e7f5b",
    "exact-interface-strong-b2s-sends.pvl": "16937c05492ab24141c8f367147d46e8ee795b50fce627002a830216b674567d",
    "exact-interface-strong-b2s-ungated-sends.pvl": "60cc2b6e47ee0034211d51b06b9d2a051155896480d6c5d6c7454d3b31120375",
    "exact-interface-strong-b2s-ungated.pv": "97c53615086d3f663ae1de1dad3e2296a90344d6a19ec5851afcccb577db0d84",
    "exact-interface-strong-b2s.pv": "e25e4c1d5084d7cdeb6df48f16fb0e876c89756ed544f0bd76484aca08bfaf4b",
    "exact-interface-strong-b2s.pvl": "6f7da48dcf89c4cace32a2c1211ad4e89b8b32d8a2c483efb419dbedc7efa0e3",
    "exact-interface-strong-registration.pvl": "aec641183c265d13026df0b8a52a6e92433f31b22dcc36c093270f01aa70e030",
    "exact-interface-strong-s2b-auxiliary.pvl": "c9382d71c4b599fa628e6e3b0affa567b96d79f1f0567314d6d6c053185fdccd",
    "exact-interface-strong-s2b-control-receive.pvl": "bdbaa3a87c1ca5eb52acee934871b0f03f0e252004200a81aedaca52c535bf04",
    "exact-interface-strong-s2b-leak-sends.pvl": "6c79f950a8fd7efd02f14973359691ec85cf1fba20af776c994454b131f2e7f3",
    "exact-interface-strong-s2b-leak.pv": "48a2b2db58378b910b7e126ec3b103abd4cfb13cbe36d59d895db4d9700bb843",
    "exact-interface-strong-s2b-origin-receive.pvl": "f108f7548aa66582412f80d529e2ba9645478369b8b7cb441f2677649143cf58",
    "exact-interface-strong-s2b-origin-sends.pvl": "637971062de2dd9cfc19f2d5cff9120b188017306e202e6733ee5de92ca91034",
    "exact-interface-strong-s2b-origin.pv": "665526184085f995812e723db119665ce5c304f753d2e2284e1008d61db2a1c2",
    "exact-interface-strong-s2b-origin.pvl": "69a4f07f6bcb8bb04deb8e84620bf8c541f9fab38893ae8b16842d49772e1fbb",
    "exact-interface-strong-s2b-receive.pvl": "62c073c129af5198adbe84a63f1c04ba0b1ff9c012d144830c21e6db7812d5e2",
    "exact-interface-strong-s2b-sends.pvl": "5b34ffb832c165cf8bb14e6b8dbf491425d6008e462406577a4a42532df1925c",
    "exact-interface-strong-s2b-ungated-sends.pvl": "d968d33b859c642899235e370fef52632575b247654b267938937fb03d5be535",
    "exact-interface-strong-s2b-ungated.pv": "48a2b2db58378b910b7e126ec3b103abd4cfb13cbe36d59d895db4d9700bb843",
    "exact-interface-strong-s2b.pv": "3390dcea7fc8605b42c71dc106713a107ca4d9fce07d1d0cdc7ba1fb4cd0f222",
    "exact-interface-strong-s2b.pvl": "5389befc77f20cd447f08f47dd135ca16b97c3d13219db6c9fbfc71b9321ff7c",
}
# Classical projection: every record AD is registration version 3 transcript AD151 (pvport3); the pinned-Server ML-DSA response signature is omitted and covered by the separate current profile.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "669482d038c8143ac25698bd4a1517480745c9b29c348d7d5c023992f813a845",
    "beaconcrypt/src/server.rs": "b5e6992a58eacce5b51d2624ff58206fbd56c744a97561146d07176a9242b66b",
    "beaconcrypt/src/ratchet.rs": "f9fa5f0b41821cc54fe5f626d18a853489300a7a2cde061efd8f7f0da277370d",
    "beaconcrypt/src/shared.rs": "98ff9810f5b1a8425a2177dab49c53eda6aa75cf5f78aedb1617712b4da17387",
    "beaconcrypt/src/pqxdh.rs": "031465df2916c2fd118a28b3cb91f79484f535e2149c9c5bc48d3c5395dacf23",
    "beaconcrypt-core/src/pqxdh.rs": "0e90604b6537968f73873850ca7626f5019a9482c3225bb333d9a3ff555fde4f",
    "beaconcrypt-core/src/pqxdh/concrete.rs": "fb8bfbbf3c2a6615540983a4665def830ffd6493a1dfaa9ffad396793bd0c5f0",
    "beaconcrypt-core/src/ratchet.rs": "ff8981ab40ed42f406e04b1258063b8e5a9418af76cccc9f065f12160fa08f47",
    "beaconcrypt-core/src/ratchet/concrete.rs": "c9f907f20f23ac2851792ff6eef77565a843e61ff266d21617411100e12e431d",
    "beaconcrypt-core/src/ratchet/refined.rs": "ce940e42b1e95bc841121ba80107ce74757fea4f4fcbd771834b93e28cdb459f",
    "beaconcrypt-core/src/record.rs": "530f820ec1998cb60ce9f2d6666f33feabcfcc597fd06997d1272d3abba9edc0",
    "beaconcrypt-core/src/session.rs": "4f83234a89c0fe8df60d68753930339f68208e2f14c464849177006af550c15e",
    "beaconcrypt/src/auth.rs": "f812e268cdd86cac01c43fdba5b25b944ebcdda1f6c03407203a6fbfa9ed16b5",
    "beaconcrypt-core/src/agreement.rs": "7abf5bb56eb76ed461d52d0d6efff8bb18f165cc6831417a4f78f6e4d0672fa6",
    "beaconcrypt-core/src/registration.rs": "8be65a2c601a151d0ec9d2a570b929d55d72394edceac59599e1b11d741bba83",
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
    "beaconcrypt/src/lib.rs": "59b2239615ff5c4bfa10db7a7162b078db5abdd10f143f9a3624937a6ff4a3ba",
    "beaconcrypt/Cargo.toml": "bd72a2dd47102f91b1f927b90666f78674a9e4af91419dffad3ac69d7195a098",
}


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("exact-interface-strong roster, classes or formulas changed")
    validate_limit_exceptions()
    if {p.name for p in directory.glob("exact-interface-strong-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("exact-interface-strong query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed exact-interface-strong theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed exact-interface-strong source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing exact-interface-strong input " + name)


def check_output(output, target):
    ACTIVE.check_output(output, target)


def run(args, logdir):
    import fcntl

    rows = []
    failures = []
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    for target in TARGETS:
        paths = [HERE / name for name in (*target.libraries(), target.query)]
        command = [args.proverif]
        for path in paths[:-1]:
            command += ["-lib", str(path)]
        command.append(str(paths[-1]))
        log = logdir / (target.name + ".log")
        timeout, address_space_kib = target_limits(
            target, args.timeout, args.address_space_kib
        )
        approved = (
            f", owner-approved limits {timeout} s, {address_space_kib} KiB address space"
            if (timeout, address_space_kib) != (args.timeout, args.address_space_kib)
            else ""
        )
        with args.lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
            row = {
                "name": target.name,
                "class": target.cls,
                "start": datetime.now(timezone.utc).isoformat(),
                "sources": before,
                "limits": {
                    "seconds": timeout,
                    "address_space_kib": address_space_kib,
                },
            }
            seconds, peak, code, timed_out = FS.run_process(
                command, log, timeout, address_space_kib
            )
            row.update(
                end=datetime.now(timezone.utc).isoformat(),
                seconds=seconds,
                peak_rss_kib=peak,
                exit=code,
                timed_out=timed_out,
                log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
            )
            try:
                if timed_out or code:
                    raise ValueError("timeout or verifier failure")
                if before != {
                    p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths
                }:
                    raise ValueError("verifier sources changed during execution")
                check_output(log.read_text(), target)
                row["checked"] = True
                print(
                    f"{target.name}: {target.cls}, exact expected verdict ({seconds:.2f}s{approved})",
                    flush=True,
                )
            except ValueError as error:
                row.update(checked=False, error=str(error))
                failures.append(target.name + ": " + str(error))
        rows.append(row)
        (logdir / "receipts.json").write_text(json.dumps(rows, indent=2) + "\n")
    if failures:
        raise ValueError("; ".join(failures))
    print(
        "Exact-interface strong secrecy: 8 checked T0 targets: 2 equivalences, 2 public-response safety auxiliaries, 4 reachability controls; private application profile only."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help="seconds per target (LIMIT_EXCEPTIONS: owner-approved exception)",
    )
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error(
            "retain the reviewed 1800-second and 10-GiB group caps (owner decision "
            "2026-11-13: the only per-target exception is SSX-b2s, 2700 s, in "
            "LIMIT_EXCEPTIONS)"
        )
    if args.check_only:
        print(
            "Exact-interface strong secrecy manifest: 8 targets: both Kr3 equivalences, exact public response/root origin, four confirmed-trace controls."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-exact-interface-strong-"))
        print("Exact-interface strong secrecy logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("exact-interface-strong check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
