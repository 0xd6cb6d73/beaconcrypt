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
