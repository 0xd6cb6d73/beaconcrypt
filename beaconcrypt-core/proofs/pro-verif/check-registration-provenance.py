#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Check exact T0 signature provenance and its scoped source-lifting interface."""

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

SOURCE_SHA256 = {
    "beaconcrypt/src/beacon.rs": "b07624435c15761d86749064cd6fd30f6a0fefcd246b485f0be80dee79d24698",
    "beaconcrypt/src/server.rs": "bede4addf22f32ead26815a2680aac04312b782d3449ccb931a9635433e9ab72",
    "beaconcrypt-core/src/pqxdh.rs": "cbb38e9d71b9f67c9c77c99ee34c834d8687cf4a1439a6965a360bb992f5eded",
}


def digest(text):
    return hashlib.sha256("".join(FS.uncommented(text).split()).encode()).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE, source_root=None):
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
