#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact T0 delayed initial-response origin and its scoped source projection."""

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

SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "c9db3b5357ba13b6c2ef5865a150285a18180e966e52db65c572f3f815a538a8",
    "beaconcrypt/src/server.rs": "40efdd7a1a86e5dac0afee4bfa2c2433a66cf86e4fbdca640e2464241e1c0569",
    "beaconcrypt-core/src/pqxdh.rs": "d13096f6f25e8c0dbf2c055d98abfc3080e6d231f5e49bacbd023d3b322f4abf",
    "beaconcrypt/src/ratchet.rs": "f5156cd43267eeec43b22875a7eef5fd8ec954feec4ee0b43288a7a1091b0c52",
    "beaconcrypt/src/shared.rs": "3b83ab0cabf2937db620f37e24f081f1ea4b37b0ae0be928de51620591beefd3",
    "beaconcrypt/src/pqxdh.rs": "f073fff7714e411f7347e77928999c42869f8527daaa15055f9e70654641b993",
}


def digest(text):
    return hashlib.sha256(
        json.dumps(MODELS.tokens(text), separators=(",", ":")).encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
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
