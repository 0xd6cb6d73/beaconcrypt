#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check selected near-record publication origin in the exact scoped T0 process."""

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


FS = load("record_origin_fs", "check-free-schedule.py")
MODELS = load("record_origin_models", "record-origin-models.py")
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "fs-registration-binding.pvl",
    "registration-set-admission.pvl",
    "fs-pending-response.pvl",
)


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    query: str
    results: tuple[str, ...]
    process: str
    bound: int = 3
    cache_witness: bool = False

    def libraries(self):
        prefix = "record-origin-cache" if self.cache_witness else "record-origin"
        return LIBRARIES + (
            prefix + "-receive.pvl",
            f"record-origin-kr{self.bound}.pvl",
            prefix + "-sends.pvl",
            prefix + ".pvl",
        )

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


ORIGIN = "event(FsReceived(beacon_to_server,s,ed_public(k),kid,root_4,t,m)) && event(L2SelectedIdentity(k)) ==> event(L2Published(beacon_to_server,s,ed_public(k),kid,root_4,t,m))"
TARGETS = (
    Target(
        "L2-origin",
        "security",
        "record-origin-auth.pv",
        (ORIGIN + " is true.",),
        "L2Main(false)",
    ),
    Target(
        "L2-identity",
        "security",
        "record-origin-identity.pv",
        ("not (event(L2SelectedIdentity(k)) && attacker(k)) is true.",),
        "L2Main(false)",
    ),
    Target(
        "L2-C-chain",
        "negative-control",
        "record-origin-leak-control.pv",
        (ORIGIN + " is false.",),
        "L2Main(true)",
    ),
    Target(
        "L2-cache",
        "witness",
        "record-origin-cache-witness.pv",
        (
            "not (event(L2CachedAccepted(s,ed_public(k),kid,root_4,m)) && event(L2SelectedIdentity(k))) is false.",
        ),
        "L2Main(false)",
        2,
        True,
    ),
)

TOKEN_SHA256 = {
    "production-transcript-interface.pvl": "46f7c94e5a4ce6e63dc41cf212f40ba08e9db2acdd06805d057993146445dadb",
    "crypto.pvl": "6e2f24249ce5a0d061676c5aa7f8762bcb77214a0a152d2b559a3ea9afa3dcc1",
    "extraction/lib.pvl": "858836a8c5009b167e0e1ec9b7067c8d84b683d3b126ae57dca4efb6e37dfe75",
    "fs-common.pvl": "86ba720e2790fa558957cc8b755057bc41cce7feb2d0426e5be14c51dd581cdd",
    "fs-registration-binding.pvl": "2f3fdb8967409447053a29f75e79585172326bcb04dfa417345896025f82edfd",
    "registration-set-admission.pvl": "739fa116a13001f7a437dd4591ae8a0083cb6dd988f266a663acdef805a63e49",
    "fs-pending-response.pvl": "18c8d2371eeba3371f4b465b62077871d94c5dcac9e4ba26e698c3ba8de82672",
    "delayed-response.pvl": "74f5324610516333aae3140d32cf99b768a31622f66c409c81a32304ad57b050",
    "registration-provenance.pvl": "c75baa6a7ffe8c8a320365940a19bbe91f72c7263ac91b04382e866ecd1f8349",
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
        raise ValueError("record-origin roster, classes or formulas changed")
    if {p.name for p in directory.glob("record-origin-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("record-origin query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed record-origin theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed record-origin source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing record-origin input " + name)


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
        with args.lock.open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            before = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
            row = {
                "name": target.name,
                "class": target.cls,
                "start": datetime.now(timezone.utc).isoformat(),
                "sources": before,
                "limits": {
                    "seconds": args.timeout,
                    "address_space_kib": args.address_space_kib,
                },
            }
            seconds, peak, code, timed_out = FS.run_process(
                command, log, args.timeout, args.address_space_kib
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
                FS.check_output(log.read_text(), target)
                row["checked"] = True
                print(
                    f"{target.name}: {target.cls}, exact expected verdict ({seconds:.2f}s)",
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
        "Record origin: 4 checked T0 targets; injectivity additionally uses the reviewed paper replay argument."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 180 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the reviewed 180-second and 10-GiB maximum caps")
    if args.check_only:
        print(
            "Record origin manifest: 4 targets; Kr3 security, Kr2 cache-prefix witness, scoped paper replay composition."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-record-origin-"))
        print("Record origin logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("record-origin check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
