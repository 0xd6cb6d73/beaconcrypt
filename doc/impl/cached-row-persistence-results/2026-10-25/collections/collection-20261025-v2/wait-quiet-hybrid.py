"""Collect declared axes only after root authorization; idle without a lease until quiet."""

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from hybrid_guard import (
    COORD,
    check_build,
    compare_sample,
    digest,
    state,
    utc,
    write_new,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--authorized", action="store_true")
    args = parser.parse_args()
    if not args.authorized:
        parser.error(
            "root must authorize execution after validation, commit, and release-build gates"
        )
    plan_bytes = args.plan.read_bytes()
    plan_sha256 = hashlib.sha256(plan_bytes).hexdigest()
    plan = json.loads(plan_bytes)
    directory = Path(plan["collection_directory"])
    limits = plan["limits"]
    check_build(plan)
    retained = []
    with (
        (directory / "collection.lock").open("a") as lock,
        (directory / "collection-events.jsonl").open("a") as events,
    ):
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)

        def record(event, **fields):
            value = {"event": event, "time_utc": utc(), **fields}
            events.write(json.dumps(value, allow_nan=False) + "\n")
            events.flush()
            print(json.dumps(value), flush=True)

        record("watcher_start", plan_sha256=plan_sha256)
        for index, axis in enumerate(plan["axes"]):
            for attempt in range(1, limits["maximum_attempts_per_axis"] + 1):
                if digest(args.plan) != plan_sha256:
                    raise RuntimeError("collection plan changed")
                name = f"axis-{index+1:02d}-{axis['backend']}-peers-{axis['peers']}-attempt-{attempt:02d}"
                attempt_directory = directory / name
                receipt = attempt_directory / "attempt.json"
                reservation_receipt = directory / (name + "-reservation.json")
                if receipt.exists():
                    result = json.loads(receipt.read_text())
                    if result.get("plan_sha256") != plan_sha256:
                        raise RuntimeError(
                            "prior attempt used a different collection plan"
                        )
                    if result["status"] == "retained":
                        if (
                            digest(attempt_directory / "report.json")
                            != result["report_sha256"]
                        ):
                            raise RuntimeError("retained report changed")
                        if (
                            digest(attempt_directory / "summary.json")
                            != result["summary_sha256"]
                        ):
                            raise RuntimeError("retained summary changed")
                        retained.append(result)
                        record(
                            "reuse_retained",
                            axis_index=index,
                            attempt=attempt,
                            directory=str(attempt_directory),
                        )
                        break
                    if result["status"] != "discarded_interference":
                        raise RuntimeError(
                            "prior hard failure requires investigation, not automatic retry"
                        )
                    continue
                if reservation_receipt.exists():
                    result = json.loads(reservation_receipt.read_text())
                    if result.get("plan_sha256") != plan_sha256:
                        raise RuntimeError(
                            "prior reservation used a different collection plan"
                        )
                    if result["exit_code"] != 75:
                        raise RuntimeError(
                            "prior reservation/runner hard failure requires investigation"
                        )
                    continue
                if attempt_directory.exists():
                    # A killed guard has no complete monitoring receipt, regardless of any output timings.
                    record(
                        "discard_incomplete_attempt",
                        axis_index=index,
                        attempt=attempt,
                        directory=str(attempt_directory),
                    )
                    continue
                previous = None
                quiet_since = None
                deadline = time.monotonic() + limits["passive_wait_seconds"]
                record(
                    "passive_wait_start", axis_index=index, axis=axis, attempt=attempt
                )
                while True:
                    now = compare_sample(
                        state(
                            directory,
                            instrumentation=plan["measurement_policy"][
                                "instrumentation_identity"
                            ],
                        ),
                        previous,
                        limits["maximum_sample_gap_seconds"],
                        plan["cpu_limits"],
                    )
                    previous = now
                    free = now["disk_free_bytes"]
                    if axis["backend"] == "postgres":
                        fs = os.statvfs(plan["postgres_cluster"]["data_directory"])
                        free = min(free, fs.f_bavail * fs.f_frsize)
                    now["checks"]["sufficient_disk_space"] = (
                        free >= limits["minimum_disk_free_bytes"]
                    )
                    now["quiet"] = all(now["checks"].values())
                    if not now["quiet"]:
                        quiet_since = None
                    elif quiet_since is None:
                        quiet_since = time.monotonic()
                    # Retain full passive samples without flooding terminal output.
                    events.write(
                        json.dumps(
                            {
                                "event": "passive_sample",
                                "axis_index": index,
                                "attempt": attempt,
                                **now,
                            }
                        )
                        + "\n"
                    )
                    events.flush()
                    if (
                        quiet_since is not None
                        and time.monotonic() - quiet_since
                        >= limits["passive_quiet_seconds"]
                    ):
                        break
                    if time.monotonic() >= deadline:
                        raise RuntimeError(
                            "predeclared passive wait limit reached; no measurement started"
                        )
                    time.sleep(limits["sample_seconds"])
                check_build(plan)
                if digest(args.plan) != plan_sha256:
                    raise RuntimeError("collection plan changed before reservation")
                command = [
                    COORD,
                    "lease",
                    "mem",
                    "codex",
                    "19800",
                    "hybrid-persistence-benchmark-please-no-lean",
                    "--eta",
                    "50m",
                    "--wait-max",
                    "60",
                    "--",
                    sys.executable,
                    str(directory / "run-quiet-hybrid.py"),
                    "--plan",
                    str(args.plan.resolve()),
                    "--axis-index",
                    str(index),
                    "--attempt",
                    str(attempt),
                    "--authorized",
                    "--plan-sha256",
                    plan_sha256,
                    "--baseline-memory-sequence",
                    now["memory_ticket_sequence"],
                    "--baseline-lean-sequence",
                    now["lean_ticket_sequence"],
                ]
                record(
                    "reservation_requested",
                    axis_index=index,
                    axis=axis,
                    attempt=attempt,
                    command=command,
                )
                with (directory / (name + "-lease.log")).open("x") as log:
                    code = subprocess.run(
                        command, stdout=log, stderr=subprocess.STDOUT
                    ).returncode
                write_new(
                    reservation_receipt,
                    {
                        "exit_code": code,
                        "time_utc": utc(),
                        "axis_index": index,
                        "attempt": attempt,
                        "plan_sha256": plan_sha256,
                    },
                )
                record(
                    "reservation_finished",
                    axis_index=index,
                    attempt=attempt,
                    exit_code=code,
                )
                if digest(args.plan) != plan_sha256:
                    raise RuntimeError("collection plan changed while runner executed")
                if code == 0:
                    result = json.loads(receipt.read_text())
                    if (
                        result["status"] != "retained"
                        or result.get("plan_sha256") != plan_sha256
                    ):
                        raise RuntimeError("runner success lacks retained receipt")
                    retained.append(result)
                    break
                if code != 75:
                    raise RuntimeError(
                        "hard failure; stop collection without timing-based retries"
                    )
            else:
                raise RuntimeError(
                    "maximum interference attempts reached for axis " + str(axis)
                )
        if len(retained) != len(plan["axes"]):
            raise RuntimeError("incomplete collection")
        write_new(
            directory / "collection-retained.json",
            {
                "completed_utc": utc(),
                "plan_sha256": plan_sha256,
                "reports": retained,
            },
        )
        record("collection_complete", reports=len(retained))


if __name__ == "__main__":
    main()
