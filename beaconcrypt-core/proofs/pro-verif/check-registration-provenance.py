#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact T0 signature provenance and its scoped source-lifting interface."""

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


FS = load("registration_provenance_fs", "check-free-schedule.py")
THEORY = load("registration_provenance_theory", "registration-provenance-theory.py")
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
    "registration-set-admission.pvl",
    "registration-provenance.pvl",
)


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    query: str
    result: str
    process: str
    wrong_purpose: bool = False

    @property
    def results(self):
        return (self.result,)

    def libraries(self):
        return LIBRARIES + (
            ("registration-provenance-wrong-purpose.pvl",) if self.wrong_purpose else ()
        )

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


TARGETS = (
    Target(
        "A2-provenance",
        "security",
        "registration-provenance-a2.pv",
        "event(ProvAccepted(ed_public(candidate_key),candidate_init,candidate_rid)) ==> event(ProvPublished(ed_public(candidate_key),candidate_init,candidate_rid)) || attacker(candidate_key) is true.",
        "ProvMain(false)",
        False,
    ),
    Target(
        "A2-beacon-key",
        "security",
        "registration-provenance-beacon-secret.pv",
        "not (event(ProvAllocated(secret_candidate)) && attacker(secret_candidate)) is true.",
        "ProvMain(false)",
        False,
    ),
    Target(
        "A2-server-key",
        "security",
        "registration-provenance-server-secret.pv",
        "not attacker(SERVER_IDENTITY_SECRET[]) is true.",
        "ProvMain(false)",
        False,
    ),
    Target(
        "A2-origin-witness",
        "witness",
        "registration-provenance-reachable.pv",
        "not (event(ProvAccepted(published_key,published_init,published_rid)) && event(ProvPublished(published_key,published_init,published_rid))) is false.",
        "ProvMain(false)",
        False,
    ),
    Target(
        "A2-C-purpose",
        "negative-control",
        "registration-provenance-control-purpose.pv",
        "event(ProvAllocated(candidate_key)) && event(ProvAccepted(ed_public(candidate_key),candidate_init,candidate_rid)) ==> event(ProvPublished(ed_public(candidate_key),candidate_init,candidate_rid)) is false.",
        "ProvWrongPurposeMain(false)",
        True,
    ),
    Target(
        "A2-C-triple",
        "negative-control",
        "registration-provenance-control-triple.pv",
        "event(ProvAllocated(candidate_key)) && event(ProvAccepted(ed_public(candidate_key),candidate_init,candidate_rid)) ==> event(ProvPublished(ed_public(candidate_key),candidate_init,candidate_rid)) is false.",
        "ProvMain(true)",
        False,
    ),
)

TOKEN_SHA256 = {
    "registration-provenance-control-triple.pv": "327d47f20f425141f993f801f0c469786f7e54850e5d09391ae40c85872f9c8f",
    "registration-provenance-control-purpose.pv": "6ccc4a1e2ef6289cac6595bab7bcb7c227157eac4804bd5be8afd7cc8dab8b11",
    "registration-provenance-a2.pv": "c7983280799da37fd271643703e44ed26ed043c03b553f14be909ab97662ea25",
    "registration-provenance-server-secret.pv": "c60fda3d9a4b8437b6bff8cab0ef6acdf95ffb63b80bf1d2f5ba830c0c81f7e3",
    "registration-provenance-reachable.pv": "3a402f45e6469a135ecd1fbbb0201cb388f6c776f5981f85cbfb0401434a6629",
    "registration-provenance-beacon-secret.pv": "566bf650a79941374ec8bddcfe2024cc0af3f5ddd8ba0922a22ba246bc335acc",
    "registration-provenance-wrong-purpose.pvl": "375d573b614d141113e2dd09fcb4a0c1a7e65065b0bd1921373d43be29aef132",
    "registration-provenance.pvl": "121a4f12eff4f89c82684491ec2c72f5ad4f0f666e806479b6d219f0988aa307",
}

# Reviewed classical projection of the ML-DSA source; see doc/impl/mldsa-source-pins.md.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "5778900307c39a5aeb82411150d5aa50e6d76467bcb89e478081a829407fcce7",
    "beaconcrypt/src/server.rs": "c47d482bfd41e9d93623acf94319a36cadb8e2ab413df07ea7678e64209e67dc",
    "beaconcrypt-core/src/pqxdh.rs": "bff5dca4b9a292a025ad96ab9fba8761bc63d2e49dac493a2bae0d1cea67a018",
    "beaconcrypt-core/src/session.rs": "3779c778ce4f8ec534c2fa610c0a334302ada76fc5cd601ade575802ff9c07c4",
    "beaconcrypt/src/auth.rs": "45b2513e304b4d4b12b41ca15ff15b94db54886e302453971d99ec0f1ce4f884",
    "beaconcrypt/src/pqxdh.rs": "f3b880ec118bebfd49851156588e681da40f50761470fbacc6940fd69cabc319",
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
    return hashlib.sha256("".join(FS.uncommented(text).split()).encode()).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    FS.validate_legacy_scope(directory)
    if tuple(targets) != TARGETS:
        raise ValueError("signature-provenance roster, classes or formulas changed")
    if {p.name for p in directory.glob("registration-provenance-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("signature-provenance query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed signature-provenance model/query: " + filename
            )
    audit = THEORY.audit(directory)
    if len(audit["reductions"]) != 28 or len(audit["data_constructors"]) != 44:
        raise ValueError("review changed protected-term rule inventory")
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed source signing/lifecycle/admission boundary: "
                + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing signature-provenance input " + name)


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
    print("Signature provenance: 6 checked T0 targets; source-profile scope applies.")


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
            "Signature provenance manifest: 6 targets, 28 reductions, 44 data constructors."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-signature-provenance-"))
        print("Signature provenance logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("signature-provenance check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
