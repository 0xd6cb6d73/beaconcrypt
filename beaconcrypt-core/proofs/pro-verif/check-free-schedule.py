#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Run and check the free-schedule (fs) ProVerif scenarios, one query per run.

Every target is one ProVerif process with one query, run serially. The checker
requires the exact expected RESULT line or lines of the target's class, both in
the primary output and in the verification summary. It rejects "cannot be
proved", unknown or inconclusive results, unconfirmed traces, errors and
warnings, and it requires exactly one reconstructed trace for every FALSE
result. Classes: security (TRUE, counted as evidence), definitional (TRUE by
construction, never counted), witness (FALSE with a trace: the event is
reachable), control (FALSE with a trace on a negative-control mutant) and
limitation (FALSE with a trace: documented expected consequence of an owner
decision). Every result is a symbolic result for a bounded process, never a
computational bound.
"""

import argparse
from dataclasses import dataclass
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import tempfile
import threading
import time

HERE = Path(__file__).resolve().parent

CLASSES = ("security", "definitional", "witness", "control", "limitation")
TRUE_CLASSES = ("security", "definitional")

# Shared loader of every fs target, in this order, before the scenario libraries.
COMMON_LOADER = (
    "production-transcript-interface.pvl",
    "crypto.pvl",
    "extraction/lib.pvl",
    "fs-common.pvl",
)

# fs-registration: the consumed-set and binding libraries, then the processes.
CONSUMED = "fs-registration-consumed.pvl"
NOCHECK = "fs-control-nocheck.pvl"
BINDING = "fs-registration-binding.pvl"
UKS = "fs-control-uks.pvl"
REGISTRATION_PROCESS = "fs-registration.pvl"
# Security results run at K_reg = 3; witnesses, controls, definitional checks and
# limitations run at the smallest bound that exhibits them.
REGISTRATION_SECURITY_BOUND = 3

A1 = "inj-event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) ==> inj-event(FsServerCommitted(obj_1,s,b,init_1,kid,root_1,ad,p))"
A1_NON_INJECTIVE = "event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) ==> event(FsServerCommitted(obj_1,s,b,init_1,kid,root_1,ad,p))"
A2 = "event(FsServerAccepted(obj_1,s,ed_public(k),init_1,rid,root_1)) ==> event(FsBeaconStarted(s2,ed_public(k),init_1,rid)) || attacker(k)"
R1 = "event(FsServerAccepted(obj_1,s,b,i1,rid,r1))@i && event(FsServerAccepted(obj_1,s,b,i2,rid,r2))@j ==> i = j"
R1_PRIME = "event(FsServerAccepted(obj_1,s,ed_public(k),i1,rid1,r1))@i && event(FsServerAccepted(obj_1,s,ed_public(k),i2,rid2,r2))@j ==> i = j || attacker(k)"
R2 = "event(FsServerReplayRejected(obj_1,s,b,rid)) ==> event(FsServerAccepted(obj_1,s,b,init_1,rid,root_1))"
R3 = "not (event(FsServerReplayRejected(obj_1,s,ed_public(k),rid)) && event(FsBeaconStarted(s,ed_public(k),init_1,rid)))"
R4 = "event(FsBeaconStarted(s2,b,init_1,rid)) && event(FsServerAccepted(o1,s,b,i1,rid,r1))@i && event(FsServerAccepted(o2,s,b,i2,rid,r2))@j ==> i = j"
R5 = "event(FsServerAcceptFailed(obj_1,s,b,rid))@i && event(FsServerAccepted(obj_1,s,b,init_1,rid,root_1))@j ==> i > j"
S3_SERVER = "event(FsServerCommitted(obj_1,s,ed_public(k),init_1,kid,root_1,ad,p)) && attacker(root_1) ==> attacker(k)"
S3_BEACON = (
    "not (event(FsBeaconEstablished(s,b,init_1,kid,root_1,ad,p)) && attacker(root_1))"
)
W1 = "not event(FsBeaconEstablished(s,b,init_1,fs_kid(1),root_1,ad,p))"
W2 = "not event(FsBeaconEstablished(s,b,init_1,fs_kid(2),root_1,ad,p))"
W3 = "not (event(FsServerAccepted(obj_1,s,ed_public(k),init_1,rid,root_1)) && attacker(k))"


@dataclass(frozen=True)
class Target:
    name: str
    scenario: str
    cls: str
    bound: int
    consumed: str
    binding: str
    query: str
    results: tuple

    def libraries(self):
        if self.scenario != "fs-registration":
            raise ValueError(f"unknown fs scenario: {self.scenario}")
        return COMMON_LOADER + (
            self.consumed,
            self.binding,
            REGISTRATION_PROCESS,
            f"fs-registration-k{self.bound}.pvl",
        )

    def expected_traces(self):
        return 0 if self.cls in TRUE_CLASSES else 1


def registration(name, cls, bound, query, results, consumed=CONSUMED, binding=BINDING):
    return Target(
        name, "fs-registration", cls, bound, consumed, binding, query, tuple(results)
    )


TARGETS = (
    registration("A1", "security", 3, "fs-registration-a1.pv", [A1 + " is true."]),
    registration("A2", "security", 3, "fs-registration-a2.pv", [A2 + " is true."]),
    registration("R1", "security", 3, "fs-registration-r1.pv", [R1 + " is true."]),
    registration(
        "R1'", "security", 3, "fs-registration-r1prime.pv", [R1_PRIME + " is true."]
    ),
    registration(
        "S3-server",
        "security",
        3,
        "fs-registration-s3-server.pv",
        [S3_SERVER + " is true."],
    ),
    registration(
        "S3-beacon",
        "security",
        3,
        "fs-registration-s3-beacon.pv",
        [S3_BEACON + " is true."],
    ),
    registration("R2", "definitional", 2, "fs-registration-r2.pv", [R2 + " is true."]),
    registration("R3", "witness", 2, "fs-registration-r3.pv", [R3 + " is false."]),
    registration("R5", "witness", 2, "fs-registration-r5.pv", [R5 + " is false."]),
    registration("W1", "witness", 1, "fs-registration-w1.pv", [W1 + " is false."]),
    registration("W2", "witness", 2, "fs-registration-w2.pv", [W2 + " is false."]),
    registration("W3", "witness", 1, "fs-registration-w3.pv", [W3 + " is false."]),
    registration("R4", "limitation", 1, "fs-registration-r4.pv", [R4 + " is false."]),
    registration(
        "C-NOCHECK",
        "control",
        2,
        "fs-registration-r1.pv",
        [R1 + " is false."],
        consumed=NOCHECK,
    ),
    registration(
        "C-UKS",
        "control",
        1,
        "fs-registration-a1.pv",
        [A1 + " is false.", "(even " + A1_NON_INJECTIVE + " is false.)"],
        binding=UKS,
    ),
)

FORBIDDEN = (
    "cannot be proved",
    "is unknown",
    "is inconclusive",
    "I could not confirm",
)


def validate_targets(targets=TARGETS, directory=HERE):
    """Check the manifest itself: classes, bounds, libraries and query files."""
    names = [target.name for target in targets]
    if len(set(names)) != len(names):
        raise ValueError("duplicate fs target name")
    used_queries = set()
    for target in targets:
        if target.cls not in CLASSES:
            raise ValueError(f"{target.name}: unknown class {target.cls}")
        if target.bound not in (1, 2, 3):
            raise ValueError(f"{target.name}: unsupported bound {target.bound}")
        if target.cls == "security" and target.bound != REGISTRATION_SECURITY_BOUND:
            raise ValueError(f"{target.name}: security results run at K_reg = 3")
        mutants = [
            lib for lib in (target.consumed, target.binding) if lib in (NOCHECK, UKS)
        ]
        if target.consumed not in (CONSUMED, NOCHECK) or target.binding not in (
            BINDING,
            UKS,
        ):
            raise ValueError(f"{target.name}: unknown scenario library")
        if (target.cls == "control") != (len(mutants) == 1):
            raise ValueError(
                f"{target.name}: a control loads exactly one mutant, others none"
            )
        if not target.results:
            raise ValueError(f"{target.name}: no expected result")
        verdict = " is true." if target.cls in TRUE_CLASSES else " is false."
        if not target.results[0].endswith(verdict):
            raise ValueError(f"{target.name}: result polarity does not match its class")
        for line in target.results:
            if any(word in line for word in FORBIDDEN):
                raise ValueError(
                    f"{target.name}: an inconclusive result is never expected"
                )
        for library in target.libraries():
            if not (directory / library).is_file():
                raise ValueError(f"{target.name}: missing library {library}")
        if not (directory / target.query).is_file():
            raise ValueError(f"{target.name}: missing query file {target.query}")
        used_queries.add(target.query)
    present = {path.name for path in directory.glob("fs-registration-*.pv")}
    if present != used_queries:
        raise ValueError(
            f"fs query files and targets differ: unused={sorted(present - used_queries)} "
            f"missing={sorted(used_queries - present)}"
        )


def check_output(output, target):
    """Require exactly the expected results of one single-query run."""
    for word in FORBIDDEN:
        if word in output:
            raise ValueError(f"{target.name}: ProVerif output contains '{word}'")
    if re.search(r"^(Error|Warning)", output, re.M):
        raise ValueError(f"{target.name}: ProVerif reported an error or warning")
    if output.count("Verification summary:") != 1:
        raise ValueError(f"{target.name}: missing or duplicated verification summary")
    primary, summary = output.split("Verification summary:")
    results = re.findall(r"^RESULT (.+)$", primary, re.M)
    reported = re.findall(r"^Query (.+)$", summary, re.M)
    if results != list(target.results) or reported != [target.results[0]]:
        raise ValueError(
            f"{target.name}: exact query/verdict mismatch\nexpected={list(target.results)!r}\n"
            f"primary={results!r}\nsummary={reported!r}"
        )
    if primary.count("A trace has been found.") != target.expected_traces():
        raise ValueError(f"{target.name}: reconstructed trace count changed")


def command(proverif, target, directory=HERE):
    arguments = [proverif]
    for library in target.libraries():
        arguments.extend(["-lib", str(directory / library)])
    arguments.append(str(directory / target.query))
    return arguments


def run_process(arguments, log_path, timeout, address_space_kib):
    """Run one process; return (seconds, peak RSS in KiB, exit code, timed out)."""

    def limit():
        if address_space_kib:
            bytes_limit = address_space_kib * 1024
            resource.setrlimit(resource.RLIMIT_AS, (bytes_limit, bytes_limit))

    timed_out = threading.Event()
    start = time.monotonic()
    with open(log_path, "w") as log:
        process = subprocess.Popen(
            arguments, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limit
        )

        def expire():
            timed_out.set()
            process.kill()

        timer = threading.Timer(timeout, expire)
        timer.start()
        try:
            _, status, usage = os.wait4(process.pid, 0)
        finally:
            timer.cancel()
    seconds = time.monotonic() - start
    process.returncode = os.waitstatus_to_exitcode(status)
    return seconds, usage.ru_maxrss, process.returncode, timed_out.is_set()


def check_target(proverif, target, logdir, timeout, address_space_kib):
    log_path = logdir / (re.sub(r"[^A-Za-z0-9]+", "-", target.name).strip("-") + ".log")
    seconds, peak, returncode, timed_out = run_process(
        command(proverif, target), log_path, timeout, address_space_kib
    )
    if timed_out:
        raise ValueError(f"{target.name}: timeout after {timeout} s ({log_path})")
    if returncode:
        raise ValueError(f"{target.name}: ProVerif exited {returncode} ({log_path})")
    check_output(log_path.read_text(), target)
    return seconds, peak


def run(proverif, targets, logdir, timeout, address_space_kib, results_path):
    validate_targets()
    rows = []
    failures = []
    for target in targets:
        try:
            seconds, peak = check_target(
                proverif, target, logdir, timeout, address_space_kib
            )
        except ValueError as error:
            failures.append(str(error))
            print(f"FAILED {target.name}: {error}", flush=True)
            continue
        verdict = "TRUE" if target.cls in TRUE_CLASSES else "FALSE"
        rows.append((target, verdict, seconds, peak))
        print(
            f"{target.name}: {target.cls}, K_reg = {target.bound}: {verdict} as expected "
            f"in {seconds:.2f} s, peak RSS {peak} KiB",
            flush=True,
        )
    if results_path:
        with open(results_path, "w") as output:
            output.write("target\tclass\tbound\tverdict\tseconds\tpeak_rss_kib\n")
            for target, verdict, seconds, peak in rows:
                output.write(
                    f"{target.name}\t{target.cls}\tK_reg={target.bound}\t{verdict}\t"
                    f"{seconds:.2f}\t{peak}\n"
                )
    if failures:
        raise SystemExit("fs ProVerif check failed:\n" + "\n".join(failures))
    total = sum(row[2] for row in rows)
    evidence = sum(1 for row in rows if row[0].cls == "security")
    print(
        f"fs ProVerif targets: {len(rows)} exact results ({evidence} security results counted "
        f"as evidence) in {total:.1f} s of serial ProVerif time; symbolic and bounded, not "
        "computational bounds."
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proverif", default="proverif")
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per target")
    parser.add_argument(
        "--address-space-kib",
        type=int,
        default=0,
        help="address-space cap per ProVerif run in KiB, as for ulimit -v (0: none)",
    )
    parser.add_argument("--log-dir", type=Path)
    parser.add_argument("--results", type=Path, help="write a TSV of times and peaks")
    parser.add_argument(
        "--only", action="append", default=[], help="run only this target"
    )
    parser.add_argument("--list", action="store_true", help="list the targets and exit")
    args = parser.parse_args()
    validate_targets()
    if args.list:
        for target in TARGETS:
            libraries = " ".join(target.libraries()[len(COMMON_LOADER) :])
            print(
                f"{target.name}\t{target.cls}\tK_reg={target.bound}\t{target.query}\t{libraries}"
            )
        return
    targets = TARGETS
    if args.only:
        unknown = set(args.only) - {target.name for target in TARGETS}
        if unknown:
            parser.error(f"unknown target: {sorted(unknown)}")
        targets = tuple(target for target in TARGETS if target.name in args.only)
    if args.log_dir:
        args.log_dir.mkdir(parents=True, exist_ok=True)
        run(
            args.proverif,
            targets,
            args.log_dir,
            args.timeout,
            args.address_space_kib,
            args.results,
        )
    else:
        with tempfile.TemporaryDirectory(prefix="beaconcrypt-fs-logs-") as directory:
            run(
                args.proverif,
                targets,
                Path(directory),
                args.timeout,
                args.address_space_kib,
                args.results,
            )


if __name__ == "__main__":
    sys.exit(main())
