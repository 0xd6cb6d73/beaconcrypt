#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact T0 delayed initial-response origin and its scoped source projection."""

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


FS = load("delayed_response_fs", "check-free-schedule.py")
MODELS = load("delayed_response_models", "delayed-response-models.py")
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
    wrong_binding: bool = False

    def libraries(self):
        return LIBRARIES + (
            ("delayed-response-wrong-binding.pvl",)
            if self.wrong_binding
            else ("delayed-response.pvl",)
        )

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


TARGETS = (
    Target(
        "A1-delayed",
        "security",
        "delayed-response-a1.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is true.",
        ),
        "A1Main(false)",
        False,
    ),
    Target(
        "A1-root",
        "security",
        "delayed-response-root.pv",
        ("not (event(A1Root(root_4)) && attacker(root_4)) is true.",),
        "A1Main(false)",
        False,
    ),
    Target(
        "A1-completion",
        "witness",
        "delayed-response-reachable.pv",
        (
            "not event(FsBeaconEstablished(s,b,init_1,fs_kid(1),root_4,ad_1,p)) is false.",
        ),
        "A1Main(false)",
        False,
    ),
    Target(
        "A1-C-binding",
        "negative-control",
        "delayed-response-control-binding.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.",
            "(even event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.)",
        ),
        "A1WrongMain(false)",
        True,
    ),
    Target(
        "A1-C-chain",
        "negative-control",
        "delayed-response-control-chain.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.",
            "(even event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.)",
        ),
        "A1Main(true)",
        False,
    ),
)

TOKEN_SHA256 = {
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "registration-set-admission.pvl": "31c72ebb741cef0fdddaafebc3159c6adbc8a43ce39fc2b3e22138e8122c3fbd",
    "fs-pending-response.pvl": "709def004f3ee92f1694ca7b09e0d981111a4353acdaa4d4b38a99cabe4ddd67",
    "fs-registration.pvl": "edb6262c0365e2dd728cc6a79906db2c3c1b2bb86d64c42e162f93aea233acf9",
    "fs-registration-a1.pv": "0c4fd269ab04c8648e4a4e325ab069691869c52bf230b32326c09c177c9c8ac2",
    "delayed-response-a1.pv": "3281afd8e3f7062ad8090a5f2e758f4967b636c15b32244b716d5cc471d3ace6",
    "delayed-response-control-binding.pv": "9a4d43e98116ef577a3c872d2a78de973a33a9dc28abec4d0cc7d10569719cf5",
    "delayed-response-control-chain.pv": "9df920cb35ff794b47dc7d897de6199d3281d821cd3bb357e168d71e59315b13",
    "delayed-response-reachable.pv": "79edaa2501e449cedb7d21f162e9145309d748f69f60a79edbb1062465788bce",
    "delayed-response-root.pv": "5fff001f871cda1c299b28c879d2b427489b2aab4c81dc74e82b2ae38b0b9fe2",
    "delayed-response-wrong-binding.pvl": "b37e93f291b1bab194fc4599ccdfcb25848c990bc15beb6cb0aaaa7a9f0d0e9c",
    "delayed-response.pvl": "c2ce813d9d2c27de7516621781f637d69b7e15b1bfceb478fbe82050b0b3adcd",
}

# Reviewed classical projection of the ML-DSA source; see doc/impl/mldsa-source-pins.md.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "5778900307c39a5aeb82411150d5aa50e6d76467bcb89e478081a829407fcce7",
    "beaconcrypt/src/server.rs": "c47d482bfd41e9d93623acf94319a36cadb8e2ab413df07ea7678e64209e67dc",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018",
    "beaconcrypt/src/ratchet.rs": "139e564ba54731bce5417144fe438f519429c44684be80de53935a6d790973c7",
    "beaconcrypt/src/shared.rs": "2a1531e83277646ee47da116db0f2cf28af046342b846d3bcfb2a02b36ab855e",
    "beaconcrypt/src/pqxdh.rs": "f3b880ec118bebfd49851156588e681da40f50761470fbacc6940fd69cabc319",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "45b2513e304b4d4b12b41ca15ff15b94db54886e302453971d99ec0f1ce4f884",
    "beaconcrypt-core/src/agreement.rs": "cea8e603c7943f18ba79f95743cc113e3d16e8589c3614240b542ee3ac1109de",
    "beaconcrypt-core/src/registration.rs": "fb6f679499585a9d9976abaea31f8dbd8f68f53f6c0f1deb7462ee393acf9f25",
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


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("delayed-response roster, classes or formulas changed")
    if {p.name for p in directory.glob("delayed-response-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("delayed-response query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed delayed-response theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed delayed-response source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing delayed-response input " + name)


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
        "Delayed response: 5 checked T0 targets (7 exact verdict lines); source-profile scope applies."
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
            "Delayed response manifest: 5 targets, 7 exact verdict lines; retained finish/control comparison."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-delayed-response-"))
        print("Delayed response logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("delayed-response check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
