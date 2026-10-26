"""Shared receipt/quiet-state checks. Importing this module starts no work."""

import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

COORD = "/tmp/bc-coord/coord.sh"
LEASES = Path("/tmp/bc-coord/leases")
CPU_LIMITS = {
    "minimum_interval_seconds": 1.0,
    "outside_process_cores": 0.25,
    "outside_aggregate_cores": 0.5,
    "system_steal_cores": 0.25,
    "swap_pages_per_second": 256,
}
HEAVY = {
    "cargo",
    "cargo-mutants",
    "cargo-nextest",
    "rustc",
    "rust-lld",
    "ld",
    "ld.lld",
    "lean",
    "lake",
    "proverif",
    "go",
    "zig",
    "cc",
    "gcc",
    "clang",
    "cc1",
    "cc1plus",
    "compile",
    "link",
    "make",
    "ninja",
    "nix",
    "nix-build",
    "nix-store",
    "nix-collect-gar",
    "hax-driver",
    "hax-engine",
    "hax-rustc-drive",
    "dune",
    "ocamlopt",
    "ocamlc",
    "postgres",
    "postmaster",
    "persistence_ben",
}


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path):
    with Path(path).open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def command(args, cwd=None, timeout=15):
    result = subprocess.run(
        args, cwd=cwd, capture_output=True, text=True, timeout=timeout, check=True
    )
    return result.stdout.strip()


def write_new(path, value):
    with Path(path).open("x") as output:
        json.dump(value, output, indent=2, allow_nan=False)
        output.write("\n")


def check_build(plan):
    workspace = Path(plan["workspace"])
    receipt = plan["build_receipt"]
    if command(["git", "status", "--porcelain"], workspace):
        raise RuntimeError("source worktree is dirty")
    if command(["git", "rev-parse", "HEAD"], workspace) != receipt["source_commit"]:
        raise RuntimeError("source commit no longer matches build receipt")
    if digest(plan["binary"]) != receipt["binary_sha256"]:
        raise RuntimeError("release binary no longer matches build receipt")
    if not receipt.get("source_sha256"):
        raise RuntimeError("build receipt lacks source hashes")
    for relative, expected in receipt["source_sha256"].items():
        if digest(workspace / relative) != expected:
            raise RuntimeError("compiled source changed: " + relative)
    for relative, expected in plan.get("machinery_sha256", {}).items():
        if digest(Path(plan["collection_directory"]) / relative) != expected:
            raise RuntimeError("collection machinery changed: " + relative)


def processes():
    result = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
            comm = (entry / "comm").read_text().strip()
            process = {
                "pid": int(entry.name),
                "ppid": int(fields[1]),
                "comm": comm,
                "state": fields[0],
                "start_ticks": int(fields[19]),
                "cpu_ticks": int(fields[11]) + int(fields[12]),
            }
            # CPU accounting covers every visible process, including unknown names and zombies.
            # Identity metadata can be unavailable for another user's process or a kernel thread.
            try:
                process["cgroup"] = (entry / "cgroup").read_text()
                process["executable"] = os.readlink(entry / "exe")
            except (FileNotFoundError, ProcessLookupError, PermissionError):
                pass
            result[int(entry.name)] = process
        except (FileNotFoundError, ProcessLookupError):
            continue
        except PermissionError:
            # Fail closed if visible process CPU accounting itself is inaccessible.
            result[int(entry.name)] = {
                "pid": int(entry.name),
                "comm": "unreadable process accounting",
                "cpu_unreadable": True,
            }
    return result


def same_scope(process, scope):
    return bool(scope) and any(
        line.rsplit(":", 1)[-1].rstrip("/").endswith("/" + scope)
        for line in process.get("cgroup", "").splitlines()
    )


def socket_inodes(pid):
    result = set()
    if pid is None:
        return result
    try:
        entries = list((Path("/proc") / str(pid) / "fd").iterdir())
    except FileNotFoundError:
        return result
    for entry in entries:
        try:
            target = os.readlink(entry)
            if target.startswith("socket:["):
                result.add(int(target[8:-1]))
        except FileNotFoundError:
            continue
    return result


def postgres_sockets(postgres, benchmark_pid):
    def tcp():
        clients, listeners = {}, {}
        for table in ("tcp", "tcp6"):
            for line in (Path("/proc/net") / table).read_text().splitlines()[1:]:
                fields = line.split()
                inode = int(fields[9])
                if not inode:
                    continue
                local = int(fields[1].rsplit(":", 1)[1], 16)
                remote = int(fields[2].rsplit(":", 1)[1], 16)
                value = {
                    "table": table,
                    "local": fields[1],
                    "remote": fields[2],
                    "state": fields[3],
                    "inode": inode,
                }
                if remote == postgres["port"] and fields[3] not in ("06", "07", "0A"):
                    clients[inode] = value
                if local == postgres["port"] and fields[3] == "0A":
                    listeners[inode] = value
        return clients, listeners

    before_clients, before_listeners = tcp()
    client_fds = socket_inodes(benchmark_pid)
    master_fds = socket_inodes(postgres["pid"])
    after_clients, after_listeners = tcp()
    # Connections must survive both snapshots around the FD read; closed sockets cannot produce a false owner failure.
    stable_clients = before_clients.keys() & after_clients.keys()
    stable_listeners = before_listeners.keys() & after_listeners.keys()
    return {
        "client_sockets": [after_clients[inode] for inode in sorted(stable_clients)],
        "foreign_client_sockets": [
            after_clients[inode] for inode in sorted(stable_clients - client_fds)
        ],
        "listeners": [after_listeners[inode] for inode in sorted(stable_listeners)],
        "owned_listener": bool(stable_listeners) and stable_listeners <= master_fds,
    }


def state(workspace, scope=None, postgres=None, benchmark_pid=None, binary=None):
    ledger = command([COORD, "lease", "list"])
    active = [line for line in ledger.splitlines() if line.startswith("lease\t")]
    waiters = [
        line for line in ledger.splitlines() if line.startswith(("wait\t", "leanq\t"))
    ]
    uptime_seconds = float(Path("/proc/uptime").read_text().split()[0])
    all_processes = processes()
    master = all_processes.get(postgres["pid"], {}) if postgres else {}
    master_valid = bool(postgres) and (
        master.get("start_ticks") == postgres["start_ticks"]
        and master.get("executable") == postgres["executable"]
        and same_scope(master, scope)
    )
    exempt, competing, process_cpu = [], [], []
    for pid, process in all_processes.items():
        approved = False
        if same_scope(process, scope):
            if pid == benchmark_pid and process.get("executable") == binary:
                approved = True
            if master_valid and process.get("executable") == postgres["executable"]:
                # PostgreSQL server children have the owned postmaster as parent; no blanket comm exemption.
                approved = (
                    pid == postgres["pid"]
                    and process.get("start_ticks") == postgres["start_ticks"]
                ) or process.get("ppid") == postgres["pid"]
        if approved:
            exempt.append(process)
        elif process.get("state") != "Z" and (
            process["comm"] in HEAVY or process.get("cpu_unreadable")
        ):
            competing.append(process)
        if not process.get("cpu_unreadable"):
            process_cpu.append(
                {
                    key: process[key]
                    for key in ("pid", "comm", "state", "start_ticks", "cpu_ticks")
                }
                | {"exempt": approved}
            )
    own_lease = (
        len(active) == 1
        and scope
        and scope in active[0]
        and active[0].split("\t")[2:4] == ["codex", "19800"]
    )
    leases_ok = bool(own_lease) if scope else not active
    checks = {
        "lease_reservation": leases_ok,
        "no_waiters": not waiters,
        "no_lean_slots": "lean slots: 0 of 4 busy" in ledger,
        "no_proverif_lock": "proverif.lock: free" in ledger,
        "no_pvmatrix": "pvmatrix: none" in ledger,
        "no_integration_lease": "integration lease: free" in ledger,
        "no_competing_recognized_processes": not competing,
        "process_cpu_accounting_available": not any(
            p.get("cpu_unreadable") for p in all_processes.values()
        ),
    }
    if postgres:
        checks["owned_postmaster_live"] = master_valid
        sockets = postgres_sockets(postgres, benchmark_pid)
        checks["only_owned_postgres_clients"] = not sockets["foreign_client_sockets"]
        checks["owned_postgres_listener"] = sockets["owned_listener"]
    else:
        sockets = None
    fs = os.statvfs(workspace)
    vmstat = Path("/proc/vmstat").read_text()
    swap = dict(
        line.split()
        for line in vmstat.splitlines()
        if line.startswith(("pswpin ", "pswpout "))
    )
    cpu_stat = Path("/proc/stat").read_text()
    cpu_total = next(
        line for line in cpu_stat.splitlines() if line.startswith("cpu ")
    ).split()[1:]
    return {
        "time_utc": utc(),
        "time_unix": time.time(),
        "monotonic_seconds": time.monotonic(),
        "quiet": all(checks.values()),
        "checks": checks,
        "leases": ledger,
        "waiters": waiters,
        "memory_ticket_sequence": (LEASES / ".seq").read_text().strip(),
        "lean_ticket_sequence": (LEASES / "leanq/.seq").read_text().strip(),
        "heavy_processes": competing,
        "authorized_processes": exempt,
        "process_cpu": process_cpu,
        "cpu_clock_ticks_per_second": os.sysconf("SC_CLK_TCK"),
        "uptime_seconds": uptime_seconds,
        "system_steal_ticks": int(cpu_total[7]),
        "swap_in_pages": int(swap["pswpin"]),
        "swap_out_pages": int(swap["pswpout"]),
        "page_size_bytes": os.sysconf("SC_PAGE_SIZE"),
        "postgres_sockets": sockets,
        "loadavg": Path("/proc/loadavg").read_text().strip(),
        "meminfo": Path("/proc/meminfo").read_text(),
        "vmstat": vmstat,
        "cpu_stat": cpu_stat,
        "diskstats": Path("/proc/diskstats").read_text(),
        "disk_free_bytes": fs.f_bavail * fs.f_frsize,
    }


def compare_sample(
    sample, previous, max_gap, cpu_limits=None, cpu_previous=None, check_cpu=True
):
    if previous:
        for kind in ("memory", "lean"):
            key = kind + "_ticket_sequence"
            sample["checks"]["no_new_" + kind + "_ticket"] = (
                sample[key] == previous[key]
            )
        sample["gap_seconds"] = (
            sample["monotonic_seconds"] - previous["monotonic_seconds"]
        )
        sample["checks"]["bounded_monitor_gap"] = sample["gap_seconds"] <= max_gap
        if check_cpu:
            anchor = cpu_previous or previous
            cpu_usage(
                sample,
                anchor,
                cpu_limits or CPU_LIMITS,
                sample["monotonic_seconds"] - anchor["monotonic_seconds"],
            )
        else:
            sample["cpu_usage"] = {
                "enforced": False,
                "reason": "startup/provenance before the reserved quiet interval",
            }
    sample["quiet"] = all(sample["checks"].values())
    return sample


def cpu_usage(sample, previous, limits, elapsed=None):
    elapsed = sample["gap_seconds"] if elapsed is None else elapsed
    ticks = sample["cpu_clock_ticks_per_second"]
    valid = (
        elapsed > 0 and ticks > 0 and ticks == previous["cpu_clock_ticks_per_second"]
    )
    prior = {(p["pid"], p["start_ticks"]): p for p in previous["process_cpu"]}
    outside = []
    newly_seen_older = []
    for process in sample["process_cpu"]:
        old = prior.get((process["pid"], process["start_ticks"]))
        if process["exempt"] or old and old["exempt"] and process["state"] == "Z":
            continue
        if old is None:
            if process["start_ticks"] < int(previous["uptime_seconds"] * ticks):
                newly_seen_older.append(
                    {"pid": process["pid"], "start_ticks": process["start_ticks"]}
                )
                continue
            old_ticks = 0
        else:
            old_ticks = old["cpu_ticks"]
        delta = process["cpu_ticks"] - old_ticks
        valid = valid and delta >= 0
        if delta > 0:
            outside.append(
                {
                    "pid": process["pid"],
                    "start_ticks": process["start_ticks"],
                    "comm": process["comm"],
                    "cpu_ticks": delta,
                    "cores": (
                        delta / ticks / elapsed if elapsed > 0 and ticks > 0 else None
                    ),
                }
            )
    steal = sample["system_steal_ticks"] - previous["system_steal_ticks"]
    swap_in = sample["swap_in_pages"] - previous["swap_in_pages"]
    swap_out = sample["swap_out_pages"] - previous["swap_out_pages"]
    valid = valid and min(steal, swap_in, swap_out) >= 0
    sample["checks"]["cpu_counter_continuity"] = valid
    sample["checks"]["cpu_baselines_complete"] = not newly_seen_older
    enforced = valid and elapsed >= limits["minimum_interval_seconds"]
    largest = max((p["cores"] for p in outside if p["cores"] is not None), default=0)
    total = sum(p["cores"] for p in outside if p["cores"] is not None)
    steal_rate = steal / ticks / elapsed if valid else None
    swap_rate = (swap_in + swap_out) / elapsed if valid else None
    if enforced:
        sample["checks"].update(
            {
                "outside_per_process_cpu_below_limit": largest
                < limits["outside_process_cores"],
                "outside_aggregate_cpu_below_limit": total
                < limits["outside_aggregate_cores"],
                "system_steal_below_limit": steal_rate < limits["system_steal_cores"],
                "system_swap_below_limit": swap_rate < limits["swap_pages_per_second"],
            }
        )
    sample["cpu_usage"] = {
        "interval_seconds": elapsed,
        "interval_start_monotonic": previous.get("monotonic_seconds"),
        "interval_finish_monotonic": sample.get("monotonic_seconds"),
        "limits": limits,
        "enforced": enforced,
        "outside_processes": sorted(
            outside, key=lambda p: p["cores"] or 0, reverse=True
        ),
        "outside_max_process_cores": largest,
        "outside_aggregate_cores": total,
        "system_steal_ticks_delta": steal,
        "system_steal_cores": steal_rate,
        "swap_in_pages_delta": swap_in,
        "swap_out_pages_delta": swap_out,
        "swap_pages_per_second": swap_rate,
        "newly_seen_older_processes_without_delta": newly_seen_older,
    }
