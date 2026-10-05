#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Run the open CTX definitional/differential controls, never security claims."""

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
SPEC = importlib.util.spec_from_file_location(
    "ctx_differential_base", HERE / "check-free-schedule.py"
)
FS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(FS)
LIBRARIES = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "aead-commitment-negative-control.pvl",
    "fs-aead-differential.pvl",
)
MODEL_SHA256 = "9220b7b264236e47b8d226d4fcad4f76d2040c15e61bea6f6937ec6cbe62730b"
WEAK_SHA256 = "f0257f9a5f6a2f9badbe6fcbe5b679a62c525d197ff30ecbd11c566ac5ddda63"


@dataclass(frozen=True)
class Target:
    name: str
    cls: str
    query: str
    result: str
    process: str

    @property
    def results(self):
        return (self.result,)

    def expected_traces(self):
        return int(self.cls == "differential")


TARGETS = (
    Target(
        "CTX-open",
        "definitional",
        "fs-aead-differential-ctx.pv",
        "not event(FsAeadDifferentContextsOpened) is true.",
        "FsAeadWithCtx",
    ),
    Target(
        "CTX-open-no-commitment",
        "differential",
        "fs-aead-differential-no-ctx.pv",
        "not event(FsAeadDifferentContextsOpened) is false.",
        "FsAeadWithoutCtx",
    ),
)


def digest(text):
    return hashlib.sha256(
        FS.uncommented(text)
        .replace(" ", "")
        .replace("\n", "")
        .replace("\t", "")
        .replace("\r", "")
        .encode()
    ).hexdigest()


def validate_targets(targets=TARGETS, directory=HERE):
    if tuple(targets) != TARGETS:
        raise ValueError("open CTX classes, verdicts or target roster changed")
    if {p.name for p in directory.glob("fs-aead-differential-*.pv")} != {
        t.query for t in targets
    }:
        raise ValueError("open CTX query roster is incomplete")
    if digest((directory / "fs-aead-differential.pvl").read_text()) != MODEL_SHA256:
        raise ValueError("review the changed open CTX input/verification process")
    weak = (
        (directory / "aead-commitment-negative-control.pvl")
        .read_text()
        .split("fun weak_aead_left_opening()", 1)[1]
        .split("event WeakAeadMultiOpened(", 1)[0]
    )
    if digest(weak) != WEAK_SHA256:
        raise ValueError("review the changed deliberate multi-opening fixture")
    for name in LIBRARIES:
        if not (directory / name).is_file():
            raise ValueError("missing open CTX library " + name)
    for target in targets:
        expected = (
            "query event(FsAeadDifferentContextsOpened()). process "
            + target.process
            + "()"
        )
        if digest((directory / target.query).read_text()) != digest(expected):
            raise ValueError("open CTX query or process changed")


def run(args, logdir):
    rows = []
    failures = []
    args.lock.parent.mkdir(parents=True, exist_ok=True)
    for target in TARGETS:
        paths = [HERE / name for name in (*LIBRARIES, target.query)]
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
    print("Open CTX controls: 2 checked targets, 0 protocol security claims.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--address-space-kib", type=int, default=10485760)
    parser.add_argument(
        "--lock", type=Path, default=Path("/tmp/bc-arc-scratch/proverif.lock")
    )
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    validate_targets()
    if not 0 < args.timeout <= 1800 or not 0 < args.address_space_kib <= 10485760:
        parser.error("retain the approved 1800-second and 10-GiB maximum caps")
    if args.check_only:
        print("Open CTX manifest: 2 targets, 0 protocol security claims.")
        return
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(args, args.log_dir)
    else:
        directory = Path(tempfile.mkdtemp(prefix="beaconcrypt-open-ctx-"))
        print("Open CTX logs: " + str(directory), flush=True)
        run(args, directory)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, IndexError) as error:
        print("open CTX check failed: " + str(error), file=sys.stderr)
        sys.exit(1)
