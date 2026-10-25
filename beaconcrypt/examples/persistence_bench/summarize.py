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


def validate_arm(result):
    messages = integer(result["messages"], "messages", 1)
    duration = integer(result["server_batch_ns"], "server_batch_ns", 1)
    plaintext = integer(result["plaintext_bytes"], "plaintext_bytes", 1)
    integer(result["wire_bytes"], "wire_bytes", plaintext)
    require(result["outputs_verified"] is True, "outputs were not verified")
    require(integer(result["pair_order"], "pair_order") in (0, 1), "invalid pair_order")
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
    for name in (
        "reads",
        "writes",
        "transactions",
        "value_bytes_read",
        "value_bytes_written",
        "head_bytes_read",
    ):
        integer(database[name], f"database.{name}")
    return {
        "server_batch_ns": duration,
        "operations_per_second": operations,
        "plaintext_mib_per_second": mib,
        "latency_ns": latency,
        "database": database,
    }


def summarize(report):
    require(
        integer(report["schema_version"], "schema_version") == 1,
        "unsupported report schema",
    )
    require(report["status"] == "complete", "report is not complete")
    config = report["config"]
    peers, trials, cases, expected = matrix(config)
    results = report["results"]
    require(isinstance(results, list) and results, "empty result matrix")
    pairs = {}
    for result in results:
        arm = result["arm"]
        require(arm in ("snapshot", "row"), f"unknown arm {arm!r}")
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
        pair[arm] = (result, validate_arm(result))
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
                    require(
                        set(pair) == {"snapshot", "row"}, f"missing paired arm: {key!r}"
                    )
                    snapshot, row = pair["snapshot"][0], pair["row"][0]
                    require(
                        {snapshot["pair_order"], row["pair_order"]} == {0, 1},
                        f"invalid paired order for {key!r}",
                    )
                    require(
                        snapshot["wire_bytes"] == row["wire_bytes"],
                        f"wire byte mismatch: {key!r}",
                    )
                    entries.append(
                        {
                            "trial": trial,
                            "first_arm": (
                                "snapshot" if snapshot["pair_order"] == 0 else "row"
                            ),
                            "snapshot": pair["snapshot"][1],
                            "row": pair["row"][1],
                            "snapshot_over_row_batch_ratio": snapshot["server_batch_ns"]
                            / row["server_batch_ns"],
                        }
                    )
                ratios = [entry["snapshot_over_row_batch_ratio"] for entry in entries]
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
                        "paired_batch_ratio": {
                            "count": len(ratios),
                            "median": statistics.median(ratios),
                            "min": min(ratios),
                            "max": max(ratios),
                        },
                    }
                )
    return {
        "schema_version": 1,
        "input_schema_version": report["schema_version"],
        "config": config,
        "source_environment": report.get("environment", {}),
        "ratio_definition": "snapshot batch duration / row batch duration; above 1 means the row batch finished sooner in this paired trial",
        "latency_definition": "Per-trial operation percentiles; trials are never pooled",
        "storage_definition": "Logical SQL value/head bytes, not physical disk I/O or cumulative WAL writes",
        "groups": groups,
    }


def markdown(summary):
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
