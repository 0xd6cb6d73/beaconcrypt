"""Execute exactly one declared axis inside a sole full-budget lease after authorization."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

from hybrid_guard import (
    HEAVY,
    check_build,
    command,
    compare_sample,
    digest,
    processes,
    postgres_sockets,
    same_scope,
    state,
    utc,
    write_new,
)


class Interference(RuntimeError):
    pass


def stop_child(process):
    if process is not None and process.poll() is None:
        process.terminate()
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--axis-index", type=int, required=True)
    parser.add_argument("--attempt", type=int, required=True)
    parser.add_argument("--baseline-memory-sequence", type=int, required=True)
    parser.add_argument("--baseline-lean-sequence", type=int, required=True)
    parser.add_argument("--plan-sha256", required=True)
    parser.add_argument("--authorized", action="store_true")
    args = parser.parse_args()
    if not args.authorized:
        parser.error(
            "root must authorize execution after validation, commit, and release-build gates"
        )
    plan_bytes = args.plan.read_bytes()
    import hashlib

    if hashlib.sha256(plan_bytes).hexdigest() != args.plan_sha256:
        raise RuntimeError("collection plan changed before runner launch")
    plan = json.loads(plan_bytes)
    scope = os.environ.get("COORD_LEASE_SCOPE")
    if not scope or "hybrid-persistence-benchmark" not in scope:
        raise RuntimeError("requires the coordinated full-budget benchmark lease")
    limits = plan["limits"]
    if (
        not 0 <= args.axis_index < len(plan["axes"])
        or not 1 <= args.attempt <= limits["maximum_attempts_per_axis"]
    ):
        parser.error("undeclared axis or attempt")
    check_build(plan)
    workspace = Path(plan["workspace"])
    axis = plan["axes"][args.axis_index]
    collection = Path(plan["collection_directory"])
    target = (
        collection
        / f"axis-{args.axis_index + 1:02d}-{axis['backend']}-peers-{axis['peers']}-attempt-{args.attempt:02d}"
    )
    target.mkdir()
    fixture_directory = target / "fixtures"
    fixture_directory.mkdir()
    cluster = plan["postgres_cluster"]
    data = Path(cluster["data_directory"]).resolve()
    pg_bin = Path(cluster["binary_directory"])
    pgctl = str(pg_bin / "pg_ctl")
    postgres = None
    pg_process = None
    pg_log = None
    baseline_schemas = None
    child = None
    previous = None
    cpu_anchors = []
    outcome = {
        "axis_index": args.axis_index,
        "axis": axis,
        "attempt": args.attempt,
        "started_utc": utc(),
        "scope": scope,
        "status": "failed",
        "directory": str(target),
        "plan_sha256": args.plan_sha256,
        "binary_sha256": plan["build_receipt"]["binary_sha256"],
    }
    environment = os.environ.copy()
    environment["PATH"] = (
        "/home/user/.rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:"
        + environment["PATH"]
    )
    environment["RUSTFLAGS"] = "-C linker-features=-lld"

    def psql(sql):
        return command(
            [
                str(pg_bin / "psql"),
                "-XAt",
                cluster["dsn"],
                "-v",
                "ON_ERROR_STOP=1",
                "-c",
                sql,
            ],
            timeout=30,
        )

    def schema_names():
        return set(
            psql(
                "SELECT nspname FROM pg_namespace WHERE nspname ~ '^bcbench_[0-9a-f]{32}$' ORDER BY nspname"
            ).splitlines()
        )

    with (
        (target / "quiet-window.jsonl").open("x") as journal,
        (target / "server-control.log").open("x") as server_log,
    ):

        def record(event, **fields):
            journal.write(
                json.dumps({"event": event, **fields}, allow_nan=False) + "\n"
            )
            journal.flush()

        def sample(event, compare=True, gap_limit=None, **fields):
            nonlocal previous
            value = state(
                fixture_directory,
                scope,
                postgres,
                child.pid if child else None,
                plan["binary"],
                instrumentation=plan["measurement_policy"]["instrumentation_identity"],
            )
            if compare:
                anchor = next(
                    (
                        old
                        for old in reversed(cpu_anchors)
                        if value["monotonic_seconds"] - old["monotonic_seconds"]
                        >= plan["cpu_limits"]["minimum_interval_seconds"]
                    ),
                    None,
                )
                compare_sample(
                    value,
                    previous,
                    (
                        gap_limit
                        if gap_limit is not None
                        else limits["maximum_sample_gap_seconds"]
                    ),
                    plan["cpu_limits"],
                    cpu_previous=anchor,
                    check_cpu=event != "settling_start",
                )
            if event == "settling_start":
                cpu_anchors.clear()
            cpu_anchors.append(value)
            del cpu_anchors[:-3]
            value["checks"]["sufficient_disk_space"] = (
                value["disk_free_bytes"] >= limits["minimum_disk_free_bytes"]
            )
            if postgres:
                fs = os.statvfs(data)
                value["postgres_disk_free_bytes"] = fs.f_bavail * fs.f_frsize
                value["checks"]["sufficient_postgres_disk_space"] = (
                    value["postgres_disk_free_bytes"]
                    >= limits["minimum_disk_free_bytes"]
                )
            value["quiet"] = all(value["checks"].values())
            record(event, **fields, **value)
            previous = value
            if not value["quiet"]:
                raise Interference(
                    "quiet checks failed: "
                    + ", ".join(k for k, v in value["checks"].items() if not v)
                )
            return value

        try:
            initial = sample(
                "reservation", monitored_process_names=sorted(HEAVY), compare=False
            )
            if (
                int(initial["memory_ticket_sequence"])
                != args.baseline_memory_sequence + 1
                or int(initial["lean_ticket_sequence"]) != args.baseline_lean_sequence
            ):
                raise Interference(
                    "competing ticket requested between passive quiet check and reservation"
                )
            if axis["backend"] == "postgres":
                if not (data / "BC_TEST_CLUSTER_ONLY").is_file():
                    raise RuntimeError("owned ephemeral PostgreSQL marker missing")
                if digest(pg_bin / "postgres") != plan["postgres_binary_sha256"]:
                    raise RuntimeError("PostgreSQL executable changed")
                if command(["stat", "-f", "-c", "%T", str(data)]) in ("tmpfs", "ramfs"):
                    raise RuntimeError(
                        "PostgreSQL data directory must be persistent storage"
                    )
                for name, expected in plan["postgres_config_sha256"].items():
                    if digest(data / name) != expected:
                        raise RuntimeError("PostgreSQL configuration changed: " + name)
                status = subprocess.run(
                    [pgctl, "status", "-D", str(data)],
                    stdout=server_log,
                    stderr=subprocess.STDOUT,
                ).returncode
                if status != 3:
                    raise RuntimeError(
                        "owned PostgreSQL must be stopped before this attempt"
                    )
                pg_log = (target / "postgres.log").open("x")
                startup = [str(pg_bin / "postgres"), *plan["postgres_start_arguments"]]
                record("postgres_start_requested", command=startup, time_utc=utc())
                pg_process = subprocess.Popen(
                    startup, stdout=pg_log, stderr=subprocess.STDOUT
                )
                deadline = time.monotonic() + 30
                while True:
                    if pg_process.poll() is not None:
                        raise RuntimeError("owned PostgreSQL process failed to start")
                    process = processes().get(pg_process.pid, {})
                    if process.get("executable") == str(
                        pg_bin / "postgres"
                    ) and same_scope(process, scope):
                        postgres = {
                            "pid": pg_process.pid,
                            "start_ticks": process["start_ticks"],
                            "executable": str(pg_bin / "postgres"),
                            "port": plan["postgres_port"],
                        }
                        sockets = postgres_sockets(postgres, None)
                        if (
                            sockets["owned_listener"]
                            and subprocess.run(
                                [
                                    str(pg_bin / "pg_isready"),
                                    "-h",
                                    "127.0.0.1",
                                    "-p",
                                    str(plan["postgres_port"]),
                                ],
                                stdout=server_log,
                                stderr=subprocess.STDOUT,
                            ).returncode
                            == 0
                        ):
                            break
                    if time.monotonic() >= deadline:
                        raise RuntimeError(
                            "owned PostgreSQL readiness deadline exceeded"
                        )
                    time.sleep(0.1)
                if Path(psql("SHOW data_directory")).resolve() != data:
                    raise RuntimeError(
                        "connected to unexpected PostgreSQL data directory"
                    )
                if (
                    psql(
                        "SELECT count(*) FROM pg_stat_activity WHERE backend_type='client backend' AND pid<>pg_backend_pid()"
                    )
                    != "0"
                ):
                    raise Interference(
                        "unexpected PostgreSQL client before measurement"
                    )
                settings = json.loads(
                    psql(
                        "SELECT json_agg(json_build_object('name',name,'setting',setting,'unit',unit,'source',source,'pending_restart',pending_restart) ORDER BY name) FROM pg_settings"
                    )
                )
                indexed = {item["name"]: item["setting"] for item in settings}
                for name in ("fsync", "synchronous_commit", "full_page_writes"):
                    if indexed[name] != "on":
                        raise RuntimeError("PostgreSQL durability disabled: " + name)
                if indexed["default_transaction_isolation"] != "read committed":
                    raise RuntimeError("unexpected PostgreSQL transaction isolation")
                if indexed["unix_socket_directories"] != "":
                    raise RuntimeError(
                        "Unix sockets must be disabled for TCP ownership monitoring"
                    )
                baseline_schemas = schema_names()
                write_new(
                    target / "postgres-provenance.json",
                    {
                        "settings": settings,
                        "version": psql("SELECT version()"),
                        "data_directory": str(data),
                        "postmaster": postgres,
                        "scope": scope,
                        "startup_command": startup,
                        "existing_fixture_schemas": sorted(baseline_schemas),
                        "pg_controldata": command(
                            [str(pg_bin / "pg_controldata"), str(data)]
                        ),
                        "mount": json.loads(
                            command(
                                [
                                    "findmnt",
                                    "-J",
                                    "-T",
                                    str(data),
                                    "-o",
                                    "TARGET,SOURCE,FSTYPE,OPTIONS",
                                ]
                            )
                        ),
                        "configuration": {
                            name: (data / name).read_text()
                            for name in plan["postgres_config_sha256"]
                        },
                    },
                )
                environment["BEACONCRYPT_BENCH_POSTGRES"] = cluster["dsn"]
            else:
                environment.pop("BEACONCRYPT_BENCH_POSTGRES", None)
            write_new(
                target / "environment-preflight.json",
                {
                    "utc": utc(),
                    "binary_sha256": digest(plan["binary"]),
                    "source_commit": plan["build_receipt"]["source_commit"],
                    "guard_sha256": digest(__file__),
                    "scope": scope,
                    "affinity": sorted(os.sched_getaffinity(0)),
                    "sqlite_mount": json.loads(
                        command(
                            [
                                "findmnt",
                                "-J",
                                "-T",
                                str(fixture_directory),
                                "-o",
                                "TARGET,SOURCE,FSTYPE,OPTIONS",
                            ]
                        )
                    ),
                    "block_devices": json.loads(
                        command(
                            ["lsblk", "-J", "-o", "NAME,MODEL,ROTA,TYPE,MOUNTPOINTS"]
                        )
                    ),
                    "thermal_readings": {
                        str(path): path.read_text().strip()
                        for pattern in (
                            "/sys/class/thermal/thermal_zone*/temp",
                            "/sys/class/hwmon/hwmon*/temp*_input",
                        )
                        for path in map(Path, __import__("glob").glob(pattern))
                        if os.access(path, os.R_OK)
                    },
                },
            )
            # Startup and provenance are outside the quiet minute; still reject tickets requested since reservation.
            sample("settling_start", gap_limit=float("inf"))
            quiet_since = time.monotonic()
            while time.monotonic() - quiet_since < limits["reserved_quiet_seconds"]:
                time.sleep(limits["sample_seconds"])
                sample("settling")
            report_path = target / "report.json"
            cmd = [
                plan["binary"],
                "--run",
                "--output",
                str(report_path),
                "--backend",
                axis["backend"],
                "--peers",
                str(axis["peers"]),
                "--database-directory",
                str(fixture_directory),
                *plan["workload_arguments"],
            ]
            start = sample("start", command=cmd)
            outcome["measurement_start_utc"] = start["time_utc"]
            started = time.monotonic()
            with (target / "benchmark.log").open("x") as output:
                child = subprocess.Popen(
                    cmd,
                    cwd=workspace,
                    env=environment,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                )
                while True:
                    try:
                        child.wait(timeout=limits["sample_seconds"])
                        break
                    except subprocess.TimeoutExpired:
                        sample("sample")
                        if time.monotonic() - started > limits["axis_seconds"]:
                            raise RuntimeError(
                                "predeclared axis runtime limit exceeded"
                            )
            final = sample("finish", exit_code=child.returncode)
            outcome["measurement_finish_utc"] = final["time_utc"]
            if child.returncode:
                raise RuntimeError(f"benchmark exited {child.returncode}")
            check_build(plan)
            if digest(args.plan) != args.plan_sha256:
                raise RuntimeError("collection plan changed during measurement")
            if postgres:
                for name, expected in plan["postgres_config_sha256"].items():
                    if digest(data / name) != expected:
                        raise RuntimeError(
                            "PostgreSQL configuration changed during measurement: "
                            + name
                        )
            spec = importlib.util.spec_from_file_location(
                "hybrid_summary", collection / "summarize.py"
            )
            summary_module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(summary_module)
            raw = json.loads(report_path.read_text())
            expected_config = {
                "backend": axis["backend"],
                "peer_counts": [axis["peers"]],
                "active_peers": None,
            }
            options = plan["workload_arguments"]
            for flag, value in zip(options[::2], options[1::2]):
                key = flag.removeprefix("--").replace("-", "_")
                expected_config[key] = (
                    [int(part) for part in value.split(",")]
                    if key == "burst_chunks"
                    else int(value)
                )
            if (
                raw.get("backend") != axis["backend"]
                or raw.get("config") != expected_config
            ):
                raise RuntimeError("completed report does not match declared axis")
            summary = summary_module.summarize(raw)
            summary.update(
                input_path=str(report_path), input_sha256=digest(report_path)
            )
            write_new(target / "summary.json", summary)
            (target / "summary.md").write_text(summary_module.markdown(summary) + "\n")
            outcome.update(
                status="retained",
                report_sha256=digest(report_path),
                summary_sha256=digest(target / "summary.json"),
                trials=3,
                arms=raw["arms"],
            )
        except Interference as error:
            outcome.update(status="discarded_interference", reason=str(error))
        except BaseException as error:
            outcome.update(status="failed", reason=f"{type(error).__name__}: {error}")
        finally:
            try:
                stop_child(child)
            except BaseException as error:
                outcome.update(status="failed", child_shutdown_error=str(error))
            if pg_process is not None and pg_process.poll() is None:
                try:
                    actual = processes().get(pg_process.pid, {})
                    if (
                        postgres is None
                        and actual.get("executable") == str(pg_bin / "postgres")
                        and same_scope(actual, scope)
                    ):
                        postgres = {
                            "pid": pg_process.pid,
                            "start_ticks": actual["start_ticks"],
                            "executable": str(pg_bin / "postgres"),
                            "port": plan["postgres_port"],
                        }
                    if (
                        not postgres
                        or actual.get("start_ticks") != postgres["start_ticks"]
                        or actual.get("executable") != postgres["executable"]
                        or not same_scope(actual, scope)
                    ):
                        raise RuntimeError(
                            "refusing shutdown: owned postmaster identity is unverified"
                        )
                    # Signal only the child we created, never the server currently named by a data-directory pidfile.
                    pg_process.send_signal(signal.SIGINT)
                    try:
                        pg_process.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        pg_process.send_signal(signal.SIGQUIT)
                        pg_process.wait(timeout=30)
                    record(
                        "postgres_stopped",
                        pid=pg_process.pid,
                        exit_code=pg_process.returncode,
                        time_utc=utc(),
                    )
                except BaseException as error:
                    outcome.update(status="failed", shutdown_error=str(error))
            if pg_log is not None:
                pg_log.close()
            # No schema-difference deletion: concurrent/foreign schema ownership is not inferable.
            # Successful fixtures clean themselves; interrupted schemas remain for separately reviewed cleanup.
            outcome["interrupted_schema_policy"] = (
                "Preserved; no SQL schema cleanup by the guard"
            )
            if digest(args.plan) != args.plan_sha256:
                outcome.update(
                    status="failed",
                    reason="collection plan changed before final receipt",
                )
            outcome["finished_utc"] = utc()
            record("attempt_complete", **outcome)
            write_new(target / "attempt.json", outcome)
    print(json.dumps(outcome), flush=True)
    return (
        0
        if outcome["status"] == "retained"
        else 75 if outcome["status"] == "discarded_interference" else 1
    )


if __name__ == "__main__":
    sys.exit(main())
