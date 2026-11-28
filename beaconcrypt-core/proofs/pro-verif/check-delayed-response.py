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
    # Counterfactual controls only: the model (binding check present) or the
    # binding-removed model with the assigned ID omitted from both
    # transcript-AD151 derivations, derived at run time.
    ad_omits_assigned_id: bool = False

    def libraries(self):
        if self.ad_omits_assigned_id:
            return LIBRARIES + (
                (MODELS.COUNTERFACTUAL_LIBRARY,)
                if self.wrong_binding
                else (MODELS.COUNTERFACTUAL_BINDING_LIBRARY,)
            )
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
    # pvport3: with transcript AD151 the binding-removed control proves the
    # correspondence, because AD151 also binds the LE64 assigned ID and the
    # relabeled response no longer opens. This is evidence of transcript
    # binding (differential control). The counterfactual pair below omits only
    # the assigned ID from both AD151 derivations: without the binding check it
    # reproduces the original negative-control trace, and with the binding
    # check A1 stays true, so in that AD the binding check is what blocks the
    # relabeled response (it is load-bearing there).
    Target(
        "A1-C-binding",
        "differential-control",
        "delayed-response-control-binding.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is true.",
        ),
        "A1WrongMain(false)",
        True,
    ),
    Target(
        "A1-C-binding-ad-omits-assigned-id",
        "negative-control",
        "delayed-response-control-binding.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.",
            "(even event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is false.)",
        ),
        "A1WrongMain(false)",
        True,
        True,
    ),
    Target(
        "A1-delayed-ad-omits-assigned-id",
        "differential-control",
        "delayed-response-a1.pv",
        (
            "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_4,ad_1,p)) ==> inj-event(FsServerCommitted(obj,s,b,init_1,kid,root_4,ad_1,p)) is true.",
        ),
        "A1Main(false)",
        False,
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
    "production-transcript-interface.pvl": "46f7c94e5a4ce6e63dc41cf212f40ba08e9db2acdd06805d057993146445dadb",
    "crypto.pvl": "6e2f24249ce5a0d061676c5aa7f8762bcb77214a0a152d2b559a3ea9afa3dcc1",
    "extraction/lib.pvl": "858836a8c5009b167e0e1ec9b7067c8d84b683d3b126ae57dca4efb6e37dfe75",
    "fs-common.pvl": "86ba720e2790fa558957cc8b755057bc41cce7feb2d0426e5be14c51dd581cdd",
    "fs-registration-binding.pvl": "2f3fdb8967409447053a29f75e79585172326bcb04dfa417345896025f82edfd",
    "registration-set-admission.pvl": "739fa116a13001f7a437dd4591ae8a0083cb6dd988f266a663acdef805a63e49",
    "fs-pending-response.pvl": "18c8d2371eeba3371f4b465b62077871d94c5dcac9e4ba26e698c3ba8de82672",
    "fs-registration.pvl": "d0f95b2737573c381225efc322208318d0b7dce5d58504050f7213c4daa23c9e",
    "fs-registration-a1.pv": "0c4fd269ab04c8648e4a4e325ab069691869c52bf230b32326c09c177c9c8ac2",
    "delayed-response-a1.pv": "3281afd8e3f7062ad8090a5f2e758f4967b636c15b32244b716d5cc471d3ace6",
    "delayed-response-control-binding.pv": "9a4d43e98116ef577a3c872d2a78de973a33a9dc28abec4d0cc7d10569719cf5",
    "delayed-response-control-chain.pv": "9df920cb35ff794b47dc7d897de6199d3281d821cd3bb357e168d71e59315b13",
    "delayed-response-reachable.pv": "79edaa2501e449cedb7d21f162e9145309d748f69f60a79edbb1062465788bce",
    "delayed-response-root.pv": "5fff001f871cda1c299b28c879d2b427489b2aab4c81dc74e82b2ae38b0b9fe2",
    "delayed-response-wrong-binding.pvl": "0d3497023ddc2a6678860ebccb62c83e48cbd9be842a16240f0f9b0eda575a20",
    "delayed-response.pvl": "74f5324610516333aae3140d32cf99b768a31622f66c409c81a32304ad57b050",
}

# Classical projection: every record AD is registration version 3 transcript AD151 (pvport3); the pinned-Server ML-DSA response signature is omitted and covered by the separate current profile.
# Full authentication/AD lifting is not inferred from these whole-file tripwires.
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "669482d038c8143ac25698bd4a1517480745c9b29c348d7d5c023992f813a845",
    "beaconcrypt/src/server.rs": "f00083746068778587480f3f2eddb7175052427406fec0849324a11a57045ec4",
    "beaconcrypt-core/src/pqxdh.rs": "0e90604b6537968f73873850ca7626f5019a9482c3225bb333d9a3ff555fde4f",
    "beaconcrypt/src/ratchet.rs": "f9fa5f0b41821cc54fe5f626d18a853489300a7a2cde061efd8f7f0da277370d",
    "beaconcrypt/src/shared.rs": "d04ba72e34b116214896e6a3d8d8eafbfe6d55af68decd98c0a605575cb36813",
    "beaconcrypt/src/pqxdh.rs": "031465df2916c2fd118a28b3cb91f79484f535e2149c9c5bc48d3c5395dacf23",
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
    "Cargo.lock": "96eb9ed30f1a0346926bbf0a2eb323d92f6c9cf698de8de3a118c49dc1243e4e",
    "beaconcrypt/src/collections.rs": "2eac87345a8673bad9fe89e705a65eb0f20c6ac67a2516872fedd599576b8334",
    "beaconcrypt/src/lib.rs": "59b2239615ff5c4bfa10db7a7162b078db5abdd10f143f9a3624937a6ff4a3ba",
    "beaconcrypt/Cargo.toml": "de9f6bd946f81149af8ed78f696f72c5fe5b47c9e93cd93b54c06d8f7409dbb1",
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
            if name in MODELS.COUNTERFACTUAL_LIBRARIES:
                continue
            if not (directory / name).is_file():
                raise ValueError("missing delayed-response input " + name)


def run(args, logdir):
    import fcntl

    rows = []
    failures = []
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    counterfactuals = {}
    for name, source in (
        (MODELS.COUNTERFACTUAL_LIBRARY, "delayed-response-wrong-binding.pvl"),
        (MODELS.COUNTERFACTUAL_BINDING_LIBRARY, "delayed-response.pvl"),
    ):
        counterfactuals[name] = logdir / name
        counterfactuals[name].write_text(
            MODELS.ad_omits_assigned_id((HERE / source).read_text())
        )
    for target in TARGETS:
        paths = [
            counterfactuals.get(name, HERE / name)
            for name in (*target.libraries(), target.query)
        ]
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
        "Delayed response: 7 checked T0 targets (9 exact verdict lines, one assigned-ID counterfactual control pair); source-profile scope applies."
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
            "Delayed response manifest: 7 targets, 9 exact verdict lines; retained finish/control comparison and assigned-ID counterfactual pair."
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
