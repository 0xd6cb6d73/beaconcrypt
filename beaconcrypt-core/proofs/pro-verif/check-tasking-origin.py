#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check selected Server-to-Beacon near publication origin in the exact scoped T0 process."""

import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
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


FS = load("tasking_origin_fs", "check-free-schedule.py")
MODELS = load("tasking_origin_models", "tasking-origin-models.py")
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
        prefix = "tasking-origin-cache" if self.cache_witness else "tasking-origin"
        return LIBRARIES + (
            prefix + "-receive.pvl",
            f"tasking-origin-kr{self.bound}.pvl",
            prefix + "-sends.pvl",
            prefix + ".pvl",
        )

    def expected_traces(self):
        return int(self.cls in ("witness", "negative-control"))


TARGETS = (
    Target(
        "S2b-origin",
        "security",
        "tasking-origin-auth.pv",
        (
            "event(FsReceived(server_to_beacon,ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),kid,root_4,t,m)) && event(S2bSelectedIdentity(k)) ==> event(S2bPublished(server_to_beacon,ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),kid,root_4,t,m)) is true.",
        ),
        "S2bMain(false)",
        3,
        False,
    ),
    Target(
        "S2b-initial",
        "security",
        "tasking-origin-initial.pv",
        (
            "event(FsBeaconEstablished(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),init_1,kid,root_4,ad_1,p)) && event(S2bSelectedIdentity(k)) ==> event(FsServerCommitted(obj,ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),init_1,kid,root_4,ad_1,p)) is true.",
        ),
        "S2bMain(false)",
        3,
        False,
    ),
    Target(
        "S2b-identity",
        "security",
        "tasking-origin-identity.pv",
        ("not (event(S2bSelectedIdentity(k)) && attacker(k)) is true.",),
        "S2bMain(false)",
        3,
        False,
    ),
    Target(
        "S2b-C-chain",
        "negative-control",
        "tasking-origin-leak-control.pv",
        (
            "event(FsReceived(server_to_beacon,ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),kid,root_4,t,m)) && event(S2bSelectedIdentity(k)) ==> event(S2bPublished(server_to_beacon,ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),kid,root_4,t,m)) is false.",
        ),
        "S2bMain(true)",
        3,
        False,
    ),
    Target(
        "S2b-cache",
        "witness",
        "tasking-origin-cache-witness.pv",
        (
            "not (event(S2bCachedAccepted(ed_public(SERVER_IDENTITY_SECRET[]),ed_public(k),kid,root_4,m)) && event(S2bSelectedIdentity(k))) is false.",
        ),
        "S2bMain(false)",
        2,
        True,
    ),
)

TOKEN_SHA256 = {
    "crypto.pvl": "cf590d7c0799f077a1e1e164aa955b81a626037a58c8aa3e279add6754625323",
    "delayed-response.pvl": "c2ce813d9d2c27de7516621781f637d69b7e15b1bfceb478fbe82050b0b3adcd",
    "extraction/lib.pvl": "d98c064616c17b784a6478e2fb732c5b743869405bd491bf40c73a1cf3f79403",
    "fs-common.pvl": "fddb894e764ce90949ab5477bd8f6ee8f6def0ea34bfd0958263d6b8ca9ceb3f",
    "fs-pending-response.pvl": "709def004f3ee92f1694ca7b09e0d981111a4353acdaa4d4b38a99cabe4ddd67",
    "fs-registration-binding.pvl": "50b006405e0a98006e2f1ebabe854b466569beed15b7338d656557bf573a679c",
    "production-transcript-interface.pvl": "27b04f004249f80c071d07b046f35e8e1932dbbe8e44b4c2af39076e5dce1edf",
    "record-origin-auth.pv": "23447544587bbb618572d7bcdec8fb33db9d7eea339b39e4611dd53f25a5f6e4",
    "record-origin-cache-receive.pvl": "fd5755370828ded315488f66c00d70aa534588d6a3a7004e15338c0d65f5a0e2",
    "record-origin-cache-sends.pvl": "b87e459475d5f04a45fbd24f1d373c20cab0afd7534e3e0c9e1111acbcf7e3e7",
    "record-origin-cache-witness.pv": "37a38897cf13ba3886b7e817a975335e9149f0285bcade6c0fce7d74193eb281",
    "record-origin-cache.pvl": "6125eb383e37dfb6cde8740b381eeb61599995ed1104d782d28af748c3dc4883",
    "record-origin-identity.pv": "344b162cada803c6a6f0ec8e54ccf3bc74c8e63860b44dbcc9cbc79a0f195fea",
    "record-origin-kr2.pvl": "ade2896d6f22a8aeeb5239857e76d357b0b6213e2db23f3ce36178a943078a45",
    "record-origin-kr3.pvl": "f817aff4f11b7d8ba2729349d7df9ebc77f06ac7f0b39b7b2ed98fe07e1948b5",
    "record-origin-leak-control.pv": "718f6de1b4226f28d15c0d7bacdc2ac22d8247db7644c06da3ec7cc5d7bd0406",
    "record-origin-receive.pvl": "ed55b9872958c9ce8026a79ae3659a23454663ca2b6d5916ed01f2da7364519d",
    "record-origin-sends.pvl": "221a9af907cb8bfc8c1a8a9610867f21455c634f9b27d2180bfd0599d21dd67b",
    "record-origin.pvl": "3862e9ec62a600e59d92933c2f9be980e7dc195b1ea18786b8fee73a1f8caf71",
    "registration-provenance.pvl": "c75baa6a7ffe8c8a320365940a19bbe91f72c7263ac91b04382e866ecd1f8349",
    "registration-set-admission.pvl": "31c72ebb741cef0fdddaafebc3159c6adbc8a43ce39fc2b3e22138e8122c3fbd",
    "tasking-origin-auth.pv": "27d45efd8e7da6907ff2b0a2d3fb9e069de29dfefd220f3afb2543f5b3933590",
    "tasking-origin-cache-receive.pvl": "a5e4f61fc4cfd66b43022daf8597587c61404dc83920db6ab0c66684437e49d5",
    "tasking-origin-cache-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin-cache-witness.pv": "a82b2aa9fffcb98a91ae5085030017eb2e011b6c71cf6602c615396c46652b67",
    "tasking-origin-cache.pvl": "ebefb3ea873a8565f03730d7af1283453108d377ee8de93c2ab3f5b137e3bfde",
    "tasking-origin-identity.pv": "f2c9e537971e1be783a2333fe1f0e547cee8b6b64ddce57837698de9675c642d",
    "tasking-origin-initial.pv": "8cdc8c218aec8644b1b99c4911bfea3157f9f42b47620f0d78da89a3208cdf41",
    "tasking-origin-kr2.pvl": "ecb0f4d5b2bcd0bd9bf9bd2770d8f3db124ed5d9650a67f72bf1257558d357bb",
    "tasking-origin-kr3.pvl": "90bdf7d544fe3e0b66ee9a854b6df0f702610b3382d796c52837f442fc525ef6",
    "tasking-origin-leak-control.pv": "bf5896bdda3af995c47e9f250a978706ed05e19f13954bc0217ab1b243d64c28",
    "tasking-origin-receive.pvl": "cde8076d5e39b37015d3b4014eb6f78ba6d2936ce5051d899aed19415a66ac82",
    "tasking-origin-sends.pvl": "8c48ea0b0e74f9a022761ec0e463ecbdd303d37a206467f317939fcb4a5a0b29",
    "tasking-origin.pvl": "ebefb3ea873a8565f03730d7af1283453108d377ee8de93c2ab3f5b137e3bfde",
}
SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "b07624435c15761d86749064cd6fd30f6a0fefcd246b485f0be80dee79d24698",
    "beaconcrypt/src/server.rs": "bede4addf22f32ead26815a2680aac04312b782d3449ccb931a9635433e9ab72",
    "beaconcrypt/src/ratchet.rs": "89e313030c12de769b7d54288b45a5e300550af330359cbb5b0c6d4ff3d2956b",
    "beaconcrypt/src/shared.rs": "0592ebe52fcdcd444f1ed92a30c693d84733ec7248c997382e0a498b9cfd3396",
    "beaconcrypt/src/pqxdh.rs": "a215beed072e1f9a38036fc96dd5d33c2cb751a95504397d8b53411d5f49b3ee",
    "beaconcrypt-core/src/pqxdh.rs": "cbb38e9d71b9f67c9c77c99ee34c834d8687cf4a1439a6965a360bb992f5eded",
    "beaconcrypt-core/src/pqxdh/concrete.rs": "b3a22f8a7c4adb087e217d58e2d302a057fd5ae224cd8fe2c44777472e469c50",
    "beaconcrypt-core/src/ratchet.rs": "3ed4d65ed1a63605819f8e685707d47b718a91ea9ee23069da88501c8031fa51",
    "beaconcrypt-core/src/ratchet/concrete.rs": "c9f907f20f23ac2851792ff6eef77565a843e61ff266d21617411100e12e431d",
    "beaconcrypt-core/src/ratchet/refined.rs": "ce940e42b1e95bc841121ba80107ce74757fea4f4fcbd771834b93e28cdb459f",
    "beaconcrypt-core/src/record.rs": "2246e63184225fe95f7596454db9380a71c88702b2b57756513cfdcdd9d6623d",
}


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
    if tuple(targets) != TARGETS:
        raise ValueError("tasking-origin roster, classes or formulas changed")
    if {p.name for p in directory.glob("tasking-origin-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("tasking-origin query roster changed")
    for filename, wanted in TOKEN_SHA256.items():
        if digest((directory / filename).read_text()) != wanted:
            raise ValueError(
                "review changed tasking-origin theory/model/query: " + filename
            )
    MODELS.validate(directory)
    root = source_root if source_root is not None else HERE.parents[2]
    for filename, wanted in SOURCE_SHA256.items():
        if hashlib.sha256((root / filename).read_bytes()).hexdigest() != wanted:
            raise ValueError(
                "review changed tasking-origin source projection: " + filename
            )
    for target in targets:
        for name in (*target.libraries(), target.query):
            if not (directory / name).is_file():
                raise ValueError("missing tasking-origin input " + name)


def run(args, logdir):
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
        "Tasking origin: 5 checked T0 targets; injectivity additionally uses the reviewed single-worker replay argument."
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
            "Tasking origin manifest: 5 targets; Kr3 origin and initial seam, Kr2 cache-prefix witness, single-worker uniqueness."
        )
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-tasking-origin-"))
        print("Tasking origin logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("tasking-origin check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
