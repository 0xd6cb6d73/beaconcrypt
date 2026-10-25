"""Freeze a new collection plan after validation/build/commit; never runs a benchmark."""

import argparse
import json
from pathlib import Path
import shutil
import shlex
from hybrid_guard import (
    COORD,
    CPU_LIMITS,
    check_build,
    command,
    digest,
    utc,
    write_new,
    matches_instrumentation,
    processes,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-receipt", type=Path, required=True)
    parser.add_argument("--collection-directory", type=Path, required=True)
    parser.add_argument("--validation-receipt", type=Path, required=True)
    parser.add_argument(
        "--measurement-policy",
        type=Path,
        default=Path(__file__).with_name("quiet-vm-policy.json"),
    )
    parser.add_argument(
        "--workspace",
        type=Path,
        default=Path("/home/user/worktrees/beaconcrypt-row-persistence"),
    )
    parser.add_argument(
        "--postgres-cluster",
        type=Path,
        default=Path(__file__).with_name("postgres-cluster.json"),
    )
    args = parser.parse_args()
    destination = args.collection_directory.resolve()
    owner = command([COORD, "registry", "owner", str(destination)])
    if not owner.startswith("codex\t"):
        raise RuntimeError("collection must be under owned codex scratch")
    receipt = json.loads(args.build_receipt.read_text())
    cluster = json.loads(args.postgres_cluster.read_text())
    policy = json.loads(args.measurement_policy.read_text())
    superseded = Path(policy["supersedes_campaign"]).resolve()
    if destination == superseded or destination.is_relative_to(superseded):
        raise RuntimeError(
            "the superseded campaign is immutable; choose a new collection directory"
        )
    if policy["benchmark_binary_sha256"] != receipt["binary_sha256"]:
        raise RuntimeError(
            "revised campaign must use the same predeclared benchmark binary"
        )
    revision = args.measurement_policy.with_name("collection-policy-revision.json")
    if digest(revision) != policy["revision_record_sha256"]:
        raise RuntimeError("policy revision record changed")
    identity = policy["instrumentation_identity"]
    if not matches_instrumentation(processes().get(identity["pid"], {}), identity):
        raise RuntimeError("predeclared controller process identity no longer matches")
    plan = {
        "schema_version": 1,
        "status": "prepared; execution requires root authorization",
        "created_utc": utc(),
        "measurement_policy": policy,
        "measurement_policy_sha256": digest(args.measurement_policy),
        "workspace": str(args.workspace.resolve()),
        "collection_directory": str(destination),
        "binary": str(
            (
                args.workspace.resolve() / "target/release/examples/persistence_bench"
            ).resolve()
        ),
        "build_receipt": receipt,
        "build_receipt_path": str(args.build_receipt.resolve()),
        "build_receipt_sha256": digest(args.build_receipt),
        "validation_receipt_path": str(args.validation_receipt.resolve()),
        "validation_receipt_sha256": digest(args.validation_receipt),
        "postgres_cluster": cluster,
        "postgres_port": int(
            dict(part.split("=", 1) for part in shlex.split(cluster["dsn"]))["port"]
        ),
        "postgres_start_arguments": [
            "-D",
            cluster["data_directory"],
            "-c",
            "unix_socket_directories=",
        ],
        "postgres_binary_sha256": digest(
            Path(cluster["binary_directory"]) / "postgres"
        ),
        "postgres_config_sha256": {
            name: digest(Path(cluster["data_directory"]) / name)
            for name in ("postgresql.conf", "postgresql.auto.conf", "pg_hba.conf")
        },
        "axes": [
            {"backend": backend, "peers": peers}
            for backend, peers in [
                ("sqlite", 1),
                ("postgres", 1),
                ("postgres", 100),
                ("sqlite", 100),
                ("sqlite", 1000),
                ("postgres", 1000),
            ]
        ],
        "workload_arguments": [
            "--trials",
            "3",
            "--extra-registrations",
            "0",
            "--small-bytes",
            "1024",
            "--small-messages",
            "1024",
            "--large-bytes",
            "65536",
            "--large-messages",
            "128",
            "--mixed-messages",
            "1024",
            "--large-every",
            "16",
            "--burst-chunk-bytes",
            "512000",
            "--burst-chunks",
            "64,256,512",
            "--warmup-messages",
            "16",
        ],
        "limits": {
            "passive_quiet_seconds": 180,
            "reserved_quiet_seconds": 60,
            "sample_seconds": 5,
            "maximum_sample_gap_seconds": 10,
            "passive_wait_seconds": 43200,
            "axis_seconds": 2700,
            "maximum_attempts_per_axis": 3,
            "minimum_disk_free_bytes": 50 * 1024**3,
        },
        "cpu_limits": CPU_LIMITS,
        "cpu_definition": "Per-process /proc/PID/stat utime+stime deltas divided by SC_CLK_TCK and monotonic CPU-window elapsed seconds; 1 core is one CPU-second per wall second. PID+start_ticks identify processes. Only exact benchmark/owned-PostgreSQL identities and the predeclared exact controller PID/start_ticks/executable/cgroup are exempt; controller CPU is recorded distinctly on the same anchors and remains subject to counter continuity and complete-baseline validation. No controller descendants or other Codex processes are exempt. A previous verified exemption survives only for the same identity becoming a zombie. New processes born since the CPU anchor's uptime tick count from zero. Newly observed older processes without baselines fail the guard; processes exiting wholly unobserved remain a sampling limitation. Rate gates apply to intervals >=1 second, ordinarily five seconds. An older stored anchor covers short start/finish samples, so CPU windows can overlap and must not be summed. Startup/provenance is before the reserved CPU-quiet interval; settling resets the CPU anchor. System steal uses aggregate /proc/stat steal jiffies and is recorded without a veto because the physical host runs active Kubernetes workloads; swap uses pswpin+pswpout page deltas, with page size recorded and its existing threshold unchanged.",
        "retry_policy": "Fixed axis order; retain the first complete validated uncontaminated report. Retry the entire same axis from fresh fixtures only after observed interference, a monitor gap, or reservation contention. At most three attempts per axis. Exit on hard failure or runtime limit; never select by timing. Preserve every failed/interrupted attempt and its receipts.",
        "comparison": "Three arms paired within each report; rotations balance positions over three trials. Cross-backend and cross-peer windows are separate observations, not a randomized cross-window experiment.",
        "monitor_limits": "Quiet VM, not an exclusive physical host. Five-second snapshots enforce named-heavy-process vetoes, generic outside-process CPU thresholds, swap thresholds, and monotonic memory/Lean ticket sequences. The exact controller process is separately recorded instrumentation; host steal is recorded but not a veto. This is not proof of zero sub-sample or below-threshold activity, hidden processes, or host/hypervisor noise. System CPU, steal, swap and disk counters are system-wide.",
    }
    check_build(plan)
    destination.mkdir(parents=False)
    for name in (
        "hybrid_guard.py",
        "prepare-quiet-hybrid.py",
        "run-quiet-hybrid.py",
        "wait-quiet-hybrid.py",
        "test_hybrid_guard.py",
    ):
        shutil.copy2(Path(__file__).with_name(name), destination / name)
    shutil.copy2(
        args.workspace / "beaconcrypt/examples/persistence_bench/summarize.py",
        destination / "summarize.py",
    )
    shutil.copy2(args.build_receipt, destination / "build-receipt.json")
    shutil.copy2(args.validation_receipt, destination / "validation-receipt.json")
    shutil.copy2(args.measurement_policy, destination / "quiet-vm-policy.json")
    shutil.copy2(revision, destination / "collection-policy-revision.json")
    plan["machinery_sha256"] = {
        path.name: digest(path) for path in destination.glob("*.py")
    }
    plan["machinery_sha256"].update(
        {
            name: digest(destination / name)
            for name in ("quiet-vm-policy.json", "collection-policy-revision.json")
        }
    )
    write_new(destination / "collection-plan.json", plan)
    print(
        "Prepared only; no daemon, lease, watcher, or measurement started:",
        destination / "collection-plan.json",
    )


if __name__ == "__main__":
    main()
