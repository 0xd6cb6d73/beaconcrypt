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

# Classical projection: every record AD is registration version 3 transcript AD151 (pvport3); the pinned-Server ML-DSA response signature is omitted and covered by the separate current profile.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "669482d038c8143ac25698bd4a1517480745c9b29c348d7d5c023992f813a845",
    "beaconcrypt/src/server.rs": "f00083746068778587480f3f2eddb7175052427406fec0849324a11a57045ec4",
    "beaconcrypt-core/src/pqxdh.rs": "0e90604b6537968f73873850ca7626f5019a9482c3225bb333d9a3ff555fde4f",
    "beaconcrypt-core/src/session.rs": "4f83234a89c0fe8df60d68753930339f68208e2f14c464849177006af550c15e",
    "beaconcrypt/src/auth.rs": "f812e268cdd86cac01c43fdba5b25b944ebcdda1f6c03407203a6fbfa9ed16b5",
    "beaconcrypt/src/pqxdh.rs": "031465df2916c2fd118a28b3cb91f79484f535e2149c9c5bc48d3c5395dacf23",
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
    "Cargo.lock": "96eb9ed30f1a0346926bbf0a2eb323d92f6c9cf698de8de3a118c49dc1243e4e",
    "beaconcrypt/src/collections.rs": "2eac87345a8673bad9fe89e705a65eb0f20c6ac67a2516872fedd599576b8334",
    "beaconcrypt/src/lib.rs": "59b2239615ff5c4bfa10db7a7162b078db5abdd10f143f9a3624937a6ff4a3ba",
    "beaconcrypt/Cargo.toml": "de9f6bd946f81149af8ed78f696f72c5fe5b47c9e93cd93b54c06d8f7409dbb1",
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
    # 45 -> 48 (pvport3): fs-common.pvl copies the three public transcript-AD151
    # data constructors of environment.pvl; no reduction or barrier changed.
    if len(audit["reductions"]) != 28 or len(audit["data_constructors"]) != 48:
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
            "Signature provenance manifest: 6 targets, 28 reductions, 48 data constructors."
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
