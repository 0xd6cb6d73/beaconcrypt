#!/usr/bin/env python3
# SPDX-License-Identifier: 0BSD
"""Validate and summarize one persistence_bench JSON report; standard library only."""

import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value, name, minimum=0):
    require(type(value) is int and value >= minimum, f"invalid {name}: {value!r}")
    return value


def close(actual, expected, name):
    require(
        type(actual) in (int, float)
        and math.isfinite(actual)
        and math.isclose(actual, expected, rel_tol=1e-9, abs_tol=1e-9),
        f"inconsistent {name}: {actual!r}, expected {expected!r}",
    )


def unique_positive(values, name):
    require(isinstance(values, list) and values, f"missing {name}")
    for value in values:
        integer(value, name, 1)
    require(len(set(values)) == len(values), f"duplicate {name}")
    return values


def matrix(config):
    peers = unique_positive(config["peer_counts"], "peer_counts")
    bursts = unique_positive(config["burst_chunks"], "burst_chunks")
    trials = integer(config["trials"], "trials", 1)
    integer(config["extra_registrations"], "extra_registrations")
    if config["active_peers"] is not None:
        integer(config["active_peers"], "active_peers", 1)
    for name in (
        "small_bytes",
        "large_bytes",
        "burst_chunk_bytes",
        "small_messages",
        "large_messages",
        "mixed_messages",
        "large_every",
    ):
        integer(config[name], name, 1)
    small = config["small_messages"]
    large = config["large_messages"]
    mixed = config["mixed_messages"]
    large_part = mixed // config["large_every"]
    cases = {
        "small_stream": (small, small * config["small_bytes"]),
        "large_stream": (large, large * config["large_bytes"]),
        "mixed_stream": (
            mixed,
            large_part * config["large_bytes"]
            + (mixed - large_part) * config["small_bytes"],
        ),
    }
    for count in bursts:
        cases[f"burst_{count}"] = (count, count * config["burst_chunk_bytes"])
    expected = {
        (peer, trial, scenario, direction)
        for peer in peers
        for trial in range(1, trials + 1)
        for scenario in cases
        for direction in ("send", "receive")
    }
    return peers, trials, cases, expected


def validate_counters(database, version):
    names = [
        "reads",
        "writes",
        "transactions",
        "value_bytes_read",
        "value_bytes_written",
        "head_bytes_read",
    ]
    if version == 2:
        names += [
            "loads",
            "expects",
            "stores",
            "network_exchanges",
            "sql_calls",
            "validation_bytes_sent",
            "validation_rows",
            "value_bytes_expected",
        ]
    for name in names:
        integer(database[name], f"database.{name}")


def validate_fixtures(report, arms, peers, trials):
    expected = {
        (peer, trial, arm)
        for peer in peers
        for trial in range(1, trials + 1)
        for arm in arms
    }
    seen = set()
    lineages = set()
    for fixture in report["fixtures"]:
        key = (fixture["peers"], fixture["trial"], fixture["arm"])
        require(
            key in expected and key not in seen,
            f"unexpected or duplicate fixture: {key!r}",
        )
        seen.add(key)
        lineage = fixture["lineage"]
        require(
            isinstance(lineage, list)
            and len(lineage) == 32
            and all(type(value) is int and 0 <= value <= 255 for value in lineage),
            "invalid fixture lineage",
        )
        require(tuple(lineage) not in lineages, "reused independent fixture lineage")
        lineages.add(tuple(lineage))
        active = min(
            report["config"]["active_peers"] or fixture["peers"], fixture["peers"]
        )
        cached = active if fixture["arm"] == "cached_row" else None
        require(
            fixture["cache_capacity"] == cached
            and fixture["cached_peers_at_measurement_start"] == cached,
            "cache was not fully warmed or capacity mismatches",
        )
        for phase in ("cold_open_database", "cache_fill_database", "warm_database"):
            validate_counters(fixture[phase], 2)
    require(seen == expected, f"missing fixtures: {sorted(expected - seen)!r}")


def validate_arm(result, arms, version):
    messages = integer(result["messages"], "messages", 1)
    duration = integer(result["server_batch_ns"], "server_batch_ns", 1)
    plaintext = integer(result["plaintext_bytes"], "plaintext_bytes", 1)
    integer(result["wire_bytes"], "wire_bytes", plaintext)
    require(result["outputs_verified"] is True, "outputs were not verified")
    require(
        integer(result["pair_order"], "pair_order") in range(len(arms)),
        "invalid pair_order",
    )
    latencies = result["operation_latencies_ns"]
    require(
        isinstance(latencies, list) and len(latencies) == messages,
        "latency count mismatch",
    )
    for value in latencies:
        integer(value, "operation latency", 1)
    total = sum(latencies)
    require(result["sum_operation_ns"] == total, "operation latency sum mismatch")
    require(total <= duration, "sum of operation durations exceeds batch duration")
    ordered = sorted(latencies)
    latency = result["latency_ns"]
    for label, expected in (
        ("min", ordered[0]),
        ("max", ordered[-1]),
        ("mean", total / messages),
        ("p50", ordered[(messages * 50 + 99) // 100 - 1]),
        ("p95", ordered[(messages * 95 + 99) // 100 - 1]),
        ("p99", ordered[(messages * 99 + 99) // 100 - 1]),
    ):
        close(latency[label], expected, f"latency {label}")
    seconds = duration / 1e9
    operations = messages / seconds
    mib = plaintext / 1_048_576 / seconds
    close(result["operations_per_second"], operations, "operations_per_second")
    close(result["plaintext_mib_per_second"], mib, "plaintext_mib_per_second")
    database = result["database"]
    validate_counters(database, version)
    return {
        "server_batch_ns": duration,
        "operations_per_second": operations,
        "plaintext_mib_per_second": mib,
        "latency_ns": latency,
        "database": database,
    }


def summarize(report):
    version = integer(report["schema_version"], "schema_version")
    if version == 3:
        return summarize_concurrent(report)
    require(version in (1, 2), "unsupported report schema")
    require(report["status"] == "complete", "report is not complete")
    config = report["config"]
    arms = ("snapshot", "row") if version == 1 else ("snapshot", "row", "cached_row")
    comparisons = [("snapshot", "row")]
    if version == 2:
        require(report["arms"] == list(arms), "invalid configured arms")
        require(
            report["backend"] in ("sqlite", "postgres")
            and report["backend"] == config["backend"],
            "mismatched backend",
        )
        comparisons.extend((("snapshot", "cached_row"), ("row", "cached_row")))
    peers, trials, cases, expected = matrix(config)
    if version == 2:
        validate_fixtures(report, arms, peers, trials)
    results = report["results"]
    require(isinstance(results, list) and results, "empty result matrix")
    pairs = {}
    for result in results:
        arm = result["arm"]
        require(arm in arms, f"unknown arm {arm!r}")
        peer = integer(result["peers"], "peers", 1)
        trial = integer(result["trial"], "trial", 1)
        key = (peer, trial, result["scenario"], result["direction"])
        require(key in expected, f"unexpected matrix entry {key!r}")
        pair = pairs.setdefault(key, {})
        require(arm not in pair, f"duplicate {arm} arm for {key!r}")
        messages, plaintext = cases[result["scenario"]]
        active = min(config["active_peers"] or peer, peer)
        for field, value in (
            ("messages", messages),
            ("plaintext_bytes", plaintext),
            ("active_peers", active),
            ("touched_peers", min(active, messages)),
            ("consumed_registrations", peer + config["extra_registrations"]),
        ):
            require(
                type(result[field]) is int and result[field] == value,
                f"mismatched {field} in {key!r}/{arm}",
            )
        pair[arm] = (result, validate_arm(result, arms, version))
    missing = expected - pairs.keys()
    require(not missing, f"missing matrix entries: {sorted(missing)!r}")
    groups = []
    for peer in peers:
        for scenario in cases:
            for direction in ("send", "receive"):
                entries = []
                for trial in range(1, trials + 1):
                    key = (peer, trial, scenario, direction)
                    pair = pairs[key]
                    require(set(pair) == set(arms), f"missing paired arm: {key!r}")
                    snapshot = pair["snapshot"][0]
                    require(
                        {pair[arm][0]["pair_order"] for arm in arms}
                        == set(range(len(arms))),
                        f"invalid paired order for {key!r}",
                    )
                    require(
                        len({pair[arm][0]["wire_bytes"] for arm in arms}) == 1,
                        f"wire byte mismatch: {key!r}",
                    )
                    order = sorted(arms, key=lambda arm: pair[arm][0]["pair_order"])
                    entry = {
                        "trial": trial,
                        "first_arm": order[0],
                        **{arm: pair[arm][1] for arm in arms},
                    }
                    for numerator, denominator in comparisons:
                        entry[f"{numerator}_over_{denominator}_batch_ratio"] = (
                            pair[numerator][0]["server_batch_ns"]
                            / pair[denominator][0]["server_batch_ns"]
                        )
                    if version == 2:
                        entry["arm_order"] = order
                    entries.append(entry)
                ratio_summaries = {}
                for numerator, denominator in comparisons:
                    name = f"{numerator}_over_{denominator}"
                    ratios = [entry[f"{name}_batch_ratio"] for entry in entries]
                    ratio_summaries[name] = {
                        "count": len(ratios),
                        "median": statistics.median(ratios),
                        "min": min(ratios),
                        "max": max(ratios),
                    }
                groups.append(
                    {
                        "peers": peer,
                        "active_peers": snapshot["active_peers"],
                        "touched_peers": snapshot["touched_peers"],
                        "consumed_registrations": snapshot["consumed_registrations"],
                        "scenario": scenario,
                        "direction": direction,
                        "messages": snapshot["messages"],
                        "plaintext_bytes": snapshot["plaintext_bytes"],
                        "wire_bytes": snapshot["wire_bytes"],
                        "trials": entries,
                        "paired_batch_ratio": ratio_summaries["snapshot_over_row"],
                        **(
                            {"paired_batch_ratios": ratio_summaries}
                            if version == 2
                            else {}
                        ),
                    }
                )
    return {
        "schema_version": version,
        "input_schema_version": report["schema_version"],
        "config": config,
        "source_environment": report.get("environment", {}),
        "ratio_definition": "snapshot batch duration / row batch duration; above 1 means the row batch finished sooner in this paired trial",
        "latency_definition": "Per-trial operation percentiles; trials are never pooled",
        "storage_definition": "Logical SQL value/head/expected bytes, not physical disk or network I/O or cumulative WAL writes",
        **(
            {
                "arms": list(arms),
                "backend": report["backend"],
                "fixtures": report["fixtures"],
                "comparison_definition": "For each numerator_over_denominator comparison, divide paired batch durations; above 1 means denominator finished sooner",
            }
            if version == 2
            else {}
        ),
        "groups": groups,
    }


def markdown(summary):
    if summary["schema_version"] == 3:
        return markdown_concurrent(summary)
    if summary["schema_version"] == 2:
        return markdown_three_arms(summary)
    lines = [
        "# Native persistence benchmark report",
        "",
        f"Input: `{summary['input_path']}`",
        "",
        f"Input SHA-256: `{summary['input_sha256']}`",
        "",
        "Ratios divide snapshot batch duration by row batch duration. A ratio above 1 means the row batch finished sooner in that paired trial. Latency percentiles remain separate for every trial; no latency samples are pooled.",
        "",
        "Storage counters describe logical SQL values and snapshot head reads. They are not physical disk I/O measurements. The benchmark omits the application request/result journal and transport.",
        "",
    ]
    for group in summary["groups"]:
        lines.extend(
            [
                f"## {group['scenario']} / {group['direction']} / {group['peers']} peers",
                "",
                f"Eligible/touched peers: {group['active_peers']}/{group['touched_peers']}; consumed registrations: {group['consumed_registrations']}; messages: {group['messages']}; plaintext bytes: {group['plaintext_bytes']}; wire bytes: {group['wire_bytes']}.",
                "",
                "| Trial | First arm | Snapshot / row batch ms | Snapshot / row ops/s | Snapshot / row MiB/s | Snapshot p95 / p99 µs | Row p95 / p99 µs | Batch ratio |",
                "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for entry in group["trials"]:
            snapshot, row = entry["snapshot"], entry["row"]
            lines.append(
                f"| {entry['trial']} | {entry['first_arm']} | "
                f"{snapshot['server_batch_ns'] / 1e6:.3f} / {row['server_batch_ns'] / 1e6:.3f} | "
                f"{snapshot['operations_per_second']:.1f} / {row['operations_per_second']:.1f} | "
                f"{snapshot['plaintext_mib_per_second']:.2f} / {row['plaintext_mib_per_second']:.2f} | "
                f"{snapshot['latency_ns']['p95'] / 1e3:.3f} / {snapshot['latency_ns']['p99'] / 1e3:.3f} | "
                f"{row['latency_ns']['p95'] / 1e3:.3f} / {row['latency_ns']['p99'] / 1e3:.3f} | "
                f"{entry['snapshot_over_row_batch_ratio']:.3f} |"
            )
        ratio = group["paired_batch_ratio"]
        lines.extend(
            [
                "",
                f"Paired batch ratio: median **{ratio['median']:.3f}**, range {ratio['min']:.3f}–{ratio['max']:.3f}, {ratio['count']} trials.",
                "",
                "| Trial | Snapshot logical value bytes read / written | Row logical value bytes read / written | Snapshot head bytes read |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for entry in group["trials"]:
            snapshot, row = entry["snapshot"]["database"], entry["row"]["database"]
            lines.append(
                f"| {entry['trial']} | {snapshot['value_bytes_read']} / {snapshot['value_bytes_written']} | "
                f"{row['value_bytes_read']} / {row['value_bytes_written']} | {snapshot['head_bytes_read']} |"
            )
        lines.append("")
    return "\n".join(lines)


def markdown_three_arms(summary):
    lines = [
        "# Native persistence benchmark report",
        "",
        f"Input: `{summary['input_path']}`",
        "",
        f"Input SHA-256: `{summary['input_sha256']}`",
        "",
        f"Backend: **{summary['backend']}**. Ratios divide paired batch durations; above 1 means the denominator arm finished sooner. Latencies remain per trial, never pooled. Logical bytes and query exchanges are not physical I/O or network packet counts. Application request/result journaling and provider transport are excluded.",
        "",
    ]
    for group in summary["groups"]:
        lines.extend(
            [
                f"## {group['scenario']} / {group['direction']} / {group['peers']} peers",
                "",
                f"Eligible/touched peers: {group['active_peers']}/{group['touched_peers']}; consumed registrations: {group['consumed_registrations']}; messages: {group['messages']}; plaintext bytes: {group['plaintext_bytes']}; wire bytes: {group['wire_bytes']}.",
                "",
                "| Trial | Order | Arm | Batch ms | Ops/s | MiB/s | p95 / p99 / max µs |",
                "| ---: | ---: | --- | ---: | ---: | ---: | ---: |",
            ]
        )
        for entry in group["trials"]:
            for order, arm in enumerate(entry["arm_order"]):
                value = entry[arm]
                tail = value["latency_ns"]
                lines.append(
                    f"| {entry['trial']} | {order} | {arm} | {value['server_batch_ns']/1e6:.3f} | {value['operations_per_second']:.1f} | {value['plaintext_mib_per_second']:.2f} | {tail['p95']/1e3:.3f} / {tail['p99']/1e3:.3f} / {tail['max']/1e3:.3f} |"
                )
        lines.extend(
            [
                "",
                "| Trial | Snapshot / row | Snapshot / cached row | Row / cached row |",
                "| ---: | ---: | ---: | ---: |",
            ]
        )
        for entry in group["trials"]:
            lines.append(
                f"| {entry['trial']} | {entry['snapshot_over_row_batch_ratio']:.3f} | {entry['snapshot_over_cached_row_batch_ratio']:.3f} | {entry['row_over_cached_row_batch_ratio']:.3f} |"
            )
        lines.extend(
            [
                "",
                "| Paired comparison | Median | Min | Max | Trials |",
                "| --- | ---: | ---: | ---: | ---: |",
            ]
        )
        for name, ratio in group["paired_batch_ratios"].items():
            lines.append(
                f"| {name} | {ratio['median']:.3f} | {ratio['min']:.3f} | {ratio['max']:.3f} | {ratio['count']} |"
            )
        lines.extend(
            [
                "",
                "| Trial | Arm | Loads / expects / stores | Fetch queries / validation rows | SQL calls / TCP query exchanges | Logical value bytes read / written / expected | Commit validation bytes supplied | Head bytes read |",
                "| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
            ]
        )
        for entry in group["trials"]:
            for arm in summary["arms"]:
                value = entry[arm]["database"]
                lines.append(
                    f"| {entry['trial']} | {arm} | {value['loads']} / {value['expects']} / {value['stores']} | {value['reads']} / {value['validation_rows']} | {value['sql_calls']} / {value['network_exchanges']} | {value['value_bytes_read']} / {value['value_bytes_written']} / {value['value_bytes_expected']} | {value['validation_bytes_sent']} | {value['head_bytes_read']} |"
                )
        lines.append("")
    return "\n".join(lines)


CONCURRENT_ARMS = ("snapshot", "row", "cached_row")
STAGES = (
    "scheduler_lag_ns",
    "enqueue_backpressure_ns",
    "queue_wait_ns",
    "owner_wait_ns",
    "service_ns",
    "completion_overhead_ns",
)
POINTS = (
    "enqueue_attempt_ns",
    "enqueued_ns",
    "owner_start_ns",
    "native_start_ns",
    "native_end_ns",
    "completed_ns",
)


def concurrent_scenarios(config, concurrent):
    periods = unique_positive(concurrent["period_ms"], "period_ms")
    bursts = unique_positive(config["burst_chunks"], "burst_chunks")
    return (
        [
            name
            for period in periods
            for name in (f"small_period_{period}ms", f"mixed_period_{period}ms")
        ]
        + ["heterogeneous_mixed", "regular_large"]
        + [f"burst_{count}" for count in bursts]
    )


def concurrent_schedule(config, concurrent, peers, scenario):
    active = min(integer(config["active_peers"], "active_peers", 1), peers)
    lanes = min(integer(concurrent["workers"], "workers", 1), active)
    limit = integer(concurrent["max_offered"], "max_offered", 1)
    require(active <= limit, "active peers exceed operation budget")
    horizon = integer(concurrent["arrival_ms"], "arrival_ms", 1) * 1_000_000
    periods = [value * 1_000_000 for value in concurrent["period_ms"]]
    cadence = integer(config["large_every"], "large_every", 1)
    for key in ("small_bytes", "large_bytes", "burst_chunk_bytes"):
        integer(config[key], key, 1)
    jobs, peer_schedule = [], []

    def append(peer, sequence, at, kind):
        require(len(jobs) < limit, "offered operation limit exceeded")
        size = config[
            {
                "small": "small_bytes",
                "large": "large_bytes",
                "burst": "burst_chunk_bytes",
            }[kind]
        ]
        jobs.append(
            {
                "id": 0,
                "peer": peer,
                "peer_sequence": sequence,
                "scheduled_ns": at,
                "payload": kind,
                "flow": "send" if sequence % 2 == 0 else "receive",
                "plaintext_bytes": size,
            }
        )

    burst = scenario.startswith("burst_")
    for peer in range(active):
        if burst:
            period = phase = 0
        elif scenario == "heterogeneous_mixed":
            cohort = peer * len(periods) // active
            first = (cohort * active + len(periods) - 1) // len(periods)
            end = ((cohort + 1) * active + len(periods) - 1) // len(periods)
            period = periods[cohort]
            phase = (peer - first) * period // (end - first)
        else:
            period = (
                1_000_000_000
                if scenario == "regular_large"
                else int(scenario.rsplit("_", 1)[1][:-2]) * 1_000_000
            )
            phase = peer * period // active
        peer_schedule.append(
            {"peer": peer, "period_ns": period, "phase_ns": phase, "lane": peer % lanes}
        )
        if not burst:
            count = max(0, (horizon - 1 - phase) // period + 1)
            require(len(jobs) + count <= limit, "offered operation limit exceeded")
            for sequence in range(count):
                large = scenario == "regular_large" or (
                    not scenario.startswith("small_")
                    and (sequence // 2 + 1) % cadence == 0
                )
                append(
                    peer,
                    sequence,
                    phase + sequence * period,
                    "large" if large else "small",
                )
    if burst:
        messages = int(scenario.removeprefix("burst_"))
        for index in range(messages):
            append(index % active, index // active, 0, "burst")
        horizon = 0
    else:
        jobs.sort(
            key=lambda job: (job["scheduled_ns"], job["peer"], job["peer_sequence"])
        )
    for index, job in enumerate(jobs):
        job["id"] = index
    retained = sum(2 * job["plaintext_bytes"] + 1024 for job in jobs)
    require(
        retained
        <= integer(concurrent["max_precomputed_bytes"], "max_precomputed_bytes", 1),
        "precomputed input/output budget exceeded",
    )
    return jobs, peer_schedule, horizon, lanes


def concurrent_distribution(values):
    require(values, "empty concurrent distribution")
    ordered = sorted(values)
    return {
        "count": len(values),
        "min": ordered[0],
        "p50": ordered[(len(values) * 50 + 99) // 100 - 1],
        "p95": ordered[(len(values) * 95 + 99) // 100 - 1],
        "p99": ordered[(len(values) * 99 + 99) // 100 - 1],
        "max": ordered[-1],
        "mean": sum(values) / len(values),
    }


def concurrent_overlap(intervals):
    edges = sorted(
        edge
        for start, end in intervals
        if end > start
        for edge in ((start, 1), (end, -1))
    )
    active = peak = previous = any_active = multiple = weighted = 0
    for time, delta in edges:
        dt = time - previous
        if active > 0:
            any_active += dt
            weighted += dt * active
        if active > 1:
            multiple += dt
        active += delta
        require(active >= 0, "invalid active span accounting")
        peak = max(peak, active)
        previous = time
    require(active == 0, "unclosed active span")
    return {
        "peak": peak,
        "any_active_ns": any_active,
        "multiple_active_ns": multiple,
        "sum_active_ns": weighted,
    }


def concurrent_counters(db, backend, arm, count):
    validate_counters(db, 2)
    expected = {"transactions": count, "writes": count}
    if arm == "snapshot":
        expected.update(
            loads=0, expects=0, stores=0, value_bytes_read=0, value_bytes_expected=0
        )
        if backend == "postgres":
            expected.update(
                reads=0,
                network_exchanges=count,
                sql_calls=count,
                validation_rows=count,
                validation_bytes_sent=72 * count,
                head_bytes_read=0,
            )
        else:
            expected.update(
                reads=count,
                network_exchanges=0,
                sql_calls=4 * count,
                validation_rows=0,
                validation_bytes_sent=0,
                head_bytes_read=72 * count,
            )
    else:
        cached = arm == "cached_row"
        expected.update(
            reads=0 if cached else count,
            loads=0 if cached else count,
            expects=count if cached else 0,
            stores=count,
            validation_rows=count,
            head_bytes_read=0,
        )
        expected.update(
            network_exchanges=(
                (1 if cached else 2) * count if backend == "postgres" else 0
            ),
            sql_calls=(
                (1 if cached else 2) * count
                if backend == "postgres"
                else (4 if cached else 5) * count
            ),
        )
        expected["value_bytes_read" if cached else "value_bytes_expected"] = 0
        require(
            db["validation_bytes_sent"]
            == db["value_bytes_expected" if cached else "value_bytes_read"],
            "predecessor validation byte mismatch",
        )
    for key, value in expected.items():
        require(
            db[key] == value, f"concurrent {arm} {key}: expected {value}, got {db[key]}"
        )
    require(
        (db["value_bytes_written"] > 0) == (count > 0),
        "missing or extra committed value bytes",
    )


def validate_concurrent_result(result, report, jobs, peer_schedule, horizon, lanes):
    arm, backend = result["arm"], report["backend"]
    config, concurrent = report["config"], report["concurrency"]
    require(
        result["status"] == "complete"
        and result["outputs_verified"] is True
        and result["failures"] == [],
        "failed or unverified concurrent result",
    )
    require(
        result["direction"] == "duplex"
        and result["scheduled"] == jobs
        and result["peer_schedule"] == peer_schedule,
        "offered workload changed",
    )
    for job in result["scheduled"]:
        for key in ("id", "peer", "peer_sequence", "scheduled_ns", "plaintext_bytes"):
            integer(job[key], "scheduled." + key)
    count = len(jobs)
    active = len(peer_schedule)
    owners = 1 if arm == "snapshot" else lanes
    deadline = integer(concurrent["deadline_ms"], "deadline_ms", 1) * 1_000_000
    drain = integer(concurrent["drain_ms"], "drain_ms", 1) * 1_000_000
    plaintext = sum(job["plaintext_bytes"] for job in jobs)
    for key, expected in (
        ("offered", count),
        ("messages", count),
        ("active_peers", active),
        ("touched_peers", len({job["peer"] for job in jobs})),
        ("plaintext_bytes", plaintext),
        ("planned_horizon_ns", horizon),
        ("deadline_budget_ns", deadline),
        ("drain_budget_ns", drain),
        ("logical_feeder_lanes", lanes),
        ("owner_workers", owners),
    ):
        require(
            type(result[key]) is int and result[key] == expected,
            f"inconsistent concurrent {key}",
        )
    integer(result["wire_bytes"], "wire_bytes", plaintext)
    observations = result["observations"]
    require(len(observations) == count, "omitted offered callback")
    seen, owner_spans, native_spans = set(), [], []
    by_peer, by_worker = {}, {worker: [] for worker in range(owners)}
    stages = {key: [] for key in STAGES + ("response_ns", "deadline_lag_ns")}
    on_time = 0
    for observation in observations:
        identifier = integer(observation["id"], "callback id")
        require(
            identifier < count and identifier not in seen,
            "duplicate or unknown callback",
        )
        seen.add(identifier)
        job = jobs[identifier]
        lane = job["peer"] % lanes
        owner = 0 if arm == "snapshot" else lane
        for key in ("peer", "lane", "worker", "conflicts", "retries", "attempts"):
            integer(observation[key], "observation." + key)
        require(
            observation["peer"] == job["peer"]
            and observation["lane"] == lane
            and observation["worker"] == owner,
            "callback ownership mismatch",
        )
        require(
            observation["outcome"] == "completed"
            and observation.get("error") is None
            and observation["conflicts"] == observation["retries"] == 0
            and observation["attempts"] == 1,
            "failed or retried native callback",
        )
        timing = observation["timing"]
        points = [job["scheduled_ns"]] + [integer(timing[key], key) for key in POINTS]
        require(
            all(a <= b for a, b in zip(points, points[1:])),
            "callback stage order or planned arrival violated",
        )
        metrics = dict(zip(STAGES, (b - a for a, b in zip(points, points[1:]))))
        response = points[-1] - points[0]
        metrics.update(
            response_ns=response,
            deadline_lag_ns=max(0, response - deadline),
            deadline_met=response <= deadline,
        )
        require(
            observation["metrics"] == metrics, "callback metric decomposition mismatch"
        )
        for key in STAGES + ("response_ns", "deadline_lag_ns"):
            integer(observation["metrics"][key], "metric." + key)
        require(
            type(observation["metrics"]["deadline_met"]) is bool,
            "deadline classification must be boolean",
        )
        for key in stages:
            stages[key].append(metrics[key])
        on_time += metrics["deadline_met"]
        owner_spans.append((timing["owner_start_ns"], timing["completed_ns"]))
        native_spans.append((timing["native_start_ns"], timing["native_end_ns"]))
        by_peer.setdefault(job["peer"], []).append((job["peer_sequence"], timing))
        by_worker[owner].append((identifier, timing))
    require(seen == set(range(count)), "offered callback missing")
    for values in by_peer.values():
        values.sort(key=lambda value: value[0])
        require(
            [value[0] for value in values] == list(range(len(values))),
            "peer sequence omission",
        )
        require(
            all(
                a[1]["completed_ns"] <= b[1]["owner_start_ns"]
                for a, b in zip(values, values[1:])
            ),
            "peer FIFO violated",
        )
    duration = max(end for _, end in owner_spans)
    require(
        result["server_batch_ns"] == duration
        and duration > 0
        and duration <= horizon + drain,
        "batch completion or drain bound mismatch",
    )
    seconds = duration / 1e9
    close(
        result["operations_per_second"],
        count / seconds,
        "concurrent completion throughput",
    )
    close(
        result["plaintext_mib_per_second"],
        plaintext / 1_048_576 / seconds,
        "concurrent plaintext throughput",
    )
    queues = result["queues"]
    require(len(queues) == owners, "queue ownership count mismatch")
    for index, queue in enumerate(queues):
        for capacity_key, setting_key, high_key in (
            ("capacity", "queue_capacity", "high_water_jobs"),
            ("byte_capacity", "queue_bytes", "high_water_bytes"),
        ):
            total = integer(concurrent[setting_key], setting_key, 1)
            expected = total // owners + int(index < total % owners)
            require(
                integer(queue[capacity_key], capacity_key, 1) == expected
                and integer(queue[high_key], high_key) <= expected,
                "bounded queue limit violated",
            )
    expected_load = [
        {
            "lane": lane,
            "offered": sum(job["peer"] % lanes == lane for job in jobs),
            "plaintext_bytes": sum(
                job["plaintext_bytes"] for job in jobs if job["peer"] % lanes == lane
            ),
        }
        for lane in range(lanes)
    ]
    require(result["lane_load"] == expected_load, "offered lane load mismatch")
    workers = result["workers"]
    require(
        len(workers) == owners
        and {worker["worker"] for worker in workers} == set(range(owners)),
        "duplicate or missing owner worker",
    )
    db_spans, total_database = [], None
    for worker in workers:
        identifier = worker["worker"]
        peers = (
            list(range(active))
            if arm == "snapshot"
            else list(range(identifier, active, lanes))
        )
        require(worker["peers"] == peers, "worker peer partition mismatch")
        cached = len(peers) if arm == "cached_row" else None
        require(
            worker["cached_peers"] == worker["cache_capacity"] == cached,
            "cache is not warm/bounded as declared",
        )
        for field in ("cold_open_database", "warm_database"):
            validate_counters(worker[field], 2)
        values = sorted(
            by_worker[identifier], key=lambda item: item[1]["owner_start_ns"]
        )
        require(
            all(
                a[1]["completed_ns"] <= b[1]["owner_start_ns"]
                for a, b in zip(values, values[1:])
            ),
            "one owner ran overlapping callbacks",
        )
        concurrent_counters(worker["database"], backend, arm, len(values))
        if total_database is None:
            total_database = {key: 0 for key in worker["database"]}
        require(
            set(worker["database"]) == set(total_database),
            "worker counter schema differs",
        )
        for key, value in worker["database"].items():
            total_database[key] += value
        expected_kinds = (
            {"snapshot_commit": len(values)}
            if arm == "snapshot"
            else {
                "row_commit": len(values),
                **({"row_load": len(values)} if arm == "row" else {}),
            }
        )
        kinds = {key: 0 for key in expected_kinds}
        span_index = 0
        previous_end = 0
        for span in sorted(worker["db_spans"], key=lambda value: value["start_ns"]):
            start = integer(span["start_ns"], "DB span start")
            end = integer(span["end_ns"], "DB span end")
            require(
                previous_end <= start <= end, "database spans overlap on one connection"
            )
            previous_end = end
            while (
                span_index < len(values)
                and values[span_index][1]["native_end_ns"] < end
            ):
                span_index += 1
            require(
                span_index < len(values)
                and values[span_index][1]["native_start_ns"]
                <= start
                <= end
                <= values[span_index][1]["native_end_ns"],
                "database span outside native callback",
            )
            require(span["kind"] in kinds, "unexpected measured database call kind")
            kinds[span["kind"]] += 1
            db_spans.append((start, end))
        require(kinds == expected_kinds, "missing or extra database call spans")
    overlaps = {
        "owner": concurrent_overlap(owner_spans),
        "native": concurrent_overlap(native_spans),
        "database_client_call": concurrent_overlap(db_spans),
    }
    require(
        result["overlap"] == overlaps, "overlap telemetry differs from raw intervals"
    )
    require(
        all(value["peak"] <= owners for value in overlaps.values()),
        "overlap exceeds owner count",
    )

    def breakdown(key):
        partitions = {}
        for observation in observations:
            partitions.setdefault(str(key(jobs[observation["id"]])), []).append(
                observation["metrics"]
            )
        return {
            label: {
                "offered": len(values),
                "deadline_met": sum(value["deadline_met"] for value in values),
                "response_ns": concurrent_distribution(
                    [value["response_ns"] for value in values]
                ),
                "service_ns": concurrent_distribution(
                    [value["service_ns"] for value in values]
                ),
            }
            for label, values in sorted(partitions.items())
        }

    return {
        "server_batch_ns": duration,
        "operations_per_second": count / seconds,
        "plaintext_mib_per_second": plaintext / 1_048_576 / seconds,
        "offered": count,
        "completed": count,
        "deadline_met": on_time,
        "deadline_missed": count - on_time,
        "deadline_success_fraction": on_time / count,
        "callback_latency_ns": {
            key: concurrent_distribution(values) for key, values in stages.items()
        },
        "by_flow": breakdown(lambda job: job["flow"]),
        "by_payload": breakdown(lambda job: job["payload"]),
        "by_peer_period_ns": breakdown(
            lambda job: peer_schedule[job["peer"]]["period_ns"]
        ),
        "overlap": overlaps,
        "database": total_database,
        "queues": queues,
        "owner_workers": owners,
        "logical_feeder_lanes": lanes,
    }


def summarize_concurrent(report):
    require(report["status"] == "complete", "concurrent report is incomplete or failed")
    require(report["arms"] == list(CONCURRENT_ARMS), "invalid concurrent arms")
    config, concurrent = report["config"], report["concurrency"]
    require(
        report["backend"] in ("sqlite", "postgres")
        and report["backend"] == config["backend"],
        "backend mismatch",
    )
    peers = unique_positive(config["peer_counts"], "peer_counts")
    trials = integer(config["trials"], "trials", 1)
    scenarios = concurrent_scenarios(config, concurrent)
    schedules = {
        (peer, scenario): concurrent_schedule(config, concurrent, peer, scenario)
        for peer in peers
        for scenario in scenarios
    }
    expected = {
        (peer, trial, scenario, arm)
        for peer in peers
        for trial in range(1, trials + 1)
        for scenario in scenarios
        for arm in CONCURRENT_ARMS
    }
    fixture_expected = {
        (peer, trial, arm)
        for peer in peers
        for trial in range(1, trials + 1)
        for arm in CONCURRENT_ARMS
    }
    fixture_seen, lineages = set(), set()
    for fixture in report["fixtures"]:
        key = (fixture["peers"], fixture["trial"], fixture["arm"])
        lineage = fixture["lineage"]
        require(
            key in fixture_expected and key not in fixture_seen,
            "duplicate/unexpected concurrent fixture",
        )
        require(
            isinstance(lineage, list)
            and len(lineage) == 32
            and all(type(value) is int and 0 <= value <= 255 for value in lineage),
            "invalid fixture lineage",
        )
        require(tuple(lineage) not in lineages, "reused fixture lineage")
        fixture_seen.add(key)
        lineages.add(tuple(lineage))
    require(fixture_seen == fixture_expected, "missing concurrent fixture")
    results = {}
    for result in report["results"]:
        integer(result["peers"], "result peers", 1)
        integer(result["trial"], "result trial", 1)
        key = (result["peers"], result["trial"], result["scenario"], result["arm"])
        require(
            key in expected and key not in results,
            "unexpected or duplicate concurrent result",
        )
        results[key] = (
            result,
            validate_concurrent_result(result, report, *schedules[key[0], key[2]]),
        )
    require(set(results) == expected, "missing concurrent matrix result")
    groups = []
    for peer in peers:
        for scenario in scenarios:
            entries = []
            for trial in range(1, trials + 1):
                paired = {
                    arm: results[peer, trial, scenario, arm] for arm in CONCURRENT_ARMS
                }
                require(
                    {
                        integer(value[0]["pair_order"], "pair_order")
                        for value in paired.values()
                    }
                    == {0, 1, 2},
                    "invalid concurrent arm order",
                )
                require(
                    len({value[0]["wire_bytes"] for value in paired.values()}) == 1,
                    "paired wire sizes differ",
                )
                entry = {
                    "trial": trial,
                    "arm_order": sorted(
                        CONCURRENT_ARMS, key=lambda arm: paired[arm][0]["pair_order"]
                    ),
                    **{arm: pair[1] for arm, pair in paired.items()},
                }
                for numerator, denominator in (
                    ("snapshot", "row"),
                    ("snapshot", "cached_row"),
                    ("row", "cached_row"),
                ):
                    entry[f"{numerator}_over_{denominator}_batch_ratio"] = (
                        paired[numerator][1]["server_batch_ns"]
                        / paired[denominator][1]["server_batch_ns"]
                    )
                entries.append(entry)
            ratios = {}
            for name in (
                "snapshot_over_row",
                "snapshot_over_cached_row",
                "row_over_cached_row",
            ):
                values = [entry[name + "_batch_ratio"] for entry in entries]
                ratios[name] = {
                    "count": trials,
                    "median": statistics.median(values),
                    "min": min(values),
                    "max": max(values),
                }
            jobs, peer_schedule, horizon, _ = schedules[peer, scenario]
            groups.append(
                {
                    "peers": peer,
                    "active_peers": len(peer_schedule),
                    "scenario": scenario,
                    "direction": "duplex",
                    "offered": len(jobs),
                    "plaintext_bytes": sum(job["plaintext_bytes"] for job in jobs),
                    "planned_horizon_ns": horizon,
                    "peer_schedule": peer_schedule,
                    "trials": entries,
                    "paired_batch_ratios": ratios,
                }
            )
    return {
        "schema_version": 3,
        "input_schema_version": 3,
        "backend": report["backend"],
        "arms": list(CONCURRENT_ARMS),
        "config": config,
        "concurrency": concurrent,
        "source_environment": report.get("environment", {}),
        "groups": groups,
        "latency_definition": "Planned arrival to durable completion includes scheduler lag, blocked admission, queue waiting for an owner worker, owner dispatch overhead, native API service, and completion overhead. Deadlines classify completions; no cancellation/retry is hidden. Per-trial operation distributions are never pooled across trials.",
        "owner_timing_definition": "queue_wait_ns measures admission to owner dequeue, including waiting for the serial owner. owner_wait_ns measures owner dequeue to native-call entry: dispatch/pre-native overhead, not mutex contention. This actor-style runtime has no separately contended owner mutex.",
        "overlap_definition": "Half-open worker/native API/database client-call intervals prove concurrent outstanding work, not physical simultaneous writes or database CPU execution.",
        "comparison_definition": "Ratios divide paired full-drain batch durations. All offered arrivals stay in the denominator; publish deadline success and queueing alongside ratios. No significance or provider end-to-end speedup claim.",
        "storage_definition": "Logical row/SQL counters and queued plaintext bytes are not physical I/O or total process memory.",
    }


def markdown_concurrent(summary):
    lines = [
        "# Concurrent durable persistence report",
        "",
        summary["latency_definition"],
        "",
        summary["owner_timing_definition"],
        "",
        summary["overlap_definition"],
        "",
        summary["comparison_definition"],
        "",
    ]
    for group in summary["groups"]:
        lines += [
            f"## {group['peers']} peers / {group['scenario']}",
            "",
            f"{group['offered']} offered callbacks and {group['plaintext_bytes']} plaintext bytes per arm; {group['active_peers']} active peers.",
            "",
            "| Trial | Arm | Batch ms | Completed/s | Deadline met/offered | Response p50 / p95 / p99 ms | Queue/owner wait p99 ms | Native API p99 ms | Peak owner / native API / DB call |",
            "|---:|---|---:|---:|---:|---:|---:|---:|---:|",
        ]
        for trial in group["trials"]:
            for arm in CONCURRENT_ARMS:
                value = trial[arm]
                latency = value["callback_latency_ns"]
                response = " / ".join(
                    f"{latency['response_ns'][key] / 1e6:.3f}"
                    for key in ("p50", "p95", "p99")
                )
                peaks = " / ".join(
                    str(value["overlap"][key]["peak"])
                    for key in ("owner", "native", "database_client_call")
                )
                lines.append(
                    f"| {trial['trial']} | {arm} | {value['server_batch_ns']/1e6:.3f} | {value['operations_per_second']:.3f} | {value['deadline_met']}/{value['offered']} | {response} | {latency['queue_wait_ns']['p99']/1e6:.3f} | {latency['service_ns']['p99']/1e6:.3f} | {peaks} |"
                )
        lines += [
            "",
            "| Trial | Snapshot/row | Snapshot/cached | Row/cached |",
            "|---:|---:|---:|---:|",
        ]
        for trial in group["trials"]:
            lines.append(
                f"| {trial['trial']} | "
                + " | ".join(
                    f"{trial[name + '_batch_ratio']:.6f}"
                    for name in (
                        "snapshot_over_row",
                        "snapshot_over_cached_row",
                        "row_over_cached_row",
                    )
                )
                + " |"
            )
        lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--format", choices=("markdown", "json"), default="markdown")
    parser.add_argument(
        "--output", type=Path, help="new output file; refuses to overwrite"
    )
    options = parser.parse_args()
    try:
        raw = options.report.read_bytes()
        summary = summarize(json.loads(raw))
        summary["input_path"] = str(options.report.resolve())
        summary["input_sha256"] = hashlib.sha256(raw).hexdigest()
        rendered = (
            json.dumps(summary, indent=2, allow_nan=False)
            if options.format == "json"
            else markdown(summary)
        )
        if options.output:
            with options.output.open("x", encoding="utf-8") as output:
                output.write(rendered + "\n")
        else:
            print(rendered)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(2, f"invalid benchmark report: {error}\n")


if __name__ == "__main__":
    main()
