#!/usr/bin/env python3
"""Export the predeclared six-axis analysis only after root authorization.

No benchmark execution, retries, timing-based selection, or latency pooling.
Uses only the standard library and the hash-checked committed summarizer copy.
"""

import argparse
import collections
import csv
import datetime
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import statistics
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PLAN_HASH = "9bc49b4c0ac309368998e71f58c13c4e9520bf0c72c96991f5404403abe2c997"
ANALYSIS_HASH = "4450b721243b36bd544b8da3f6c9dc0139a34706aa514e5e0c2a4a58ba42f325"
BINARY_HASH = "985d56867fad436512aaff69878aa3e1c91793cc9dc00288b587c19144713b66"
ARMS = ("snapshot", "row", "cached_row")
COMPARISONS = ("snapshot_over_row", "snapshot_over_cached_row", "row_over_cached_row")
AXES = [("sqlite", 1), ("postgres", 1), ("postgres", 100), ("sqlite", 100), ("sqlite", 1000), ("postgres", 1000)]
COUNTERS = ("reads", "writes", "transactions", "loads", "expects", "stores", "network_exchanges", "sql_calls", "validation_rows", "value_bytes_read", "value_bytes_written", "head_bytes_read", "validation_bytes_sent", "value_bytes_expected")


def require(okay, message):
    if not okay:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    return json.loads(raw), digest(raw)


def distribution(values):
    require(values and all(math.isfinite(v) for v in values), "empty or nonfinite distribution")
    ordered = sorted(values)
    return {"count": len(values), "min": ordered[0], "median": statistics.median(values), "p95": ordered[math.ceil(.95 * len(values)) - 1], "max": ordered[-1]}


def counters(database, backend, arm, messages, label):
    expected = {"transactions": messages, "writes": messages}
    if arm == "snapshot":
        expected.update(loads=0, expects=0, stores=0, value_bytes_read=0, value_bytes_expected=0)
        if backend == "postgres":
            expected.update(reads=0, network_exchanges=messages, sql_calls=messages, validation_rows=messages, validation_bytes_sent=72 * messages, head_bytes_read=0)
        else:
            expected.update(reads=messages, network_exchanges=0, sql_calls=4 * messages, validation_rows=0, validation_bytes_sent=0, head_bytes_read=72 * messages)
    else:
        cached = arm == "cached_row"
        expected.update(reads=0 if cached else messages, loads=0 if cached else messages, expects=messages if cached else 0, stores=messages, validation_rows=messages, head_bytes_read=0)
        expected.update(network_exchanges=(1 if cached else 2) * messages if backend == "postgres" else 0, sql_calls=(1 if cached else 2) * messages if backend == "postgres" else (4 if cached else 5) * messages)
        expected["value_bytes_read" if cached else "value_bytes_expected"] = 0
        predecessor = database["value_bytes_expected" if cached else "value_bytes_read"]
        require(predecessor > 0 and database["validation_bytes_sent"] == predecessor, label + ": expected predecessor byte accounting")
    for name, value in expected.items():
        require(database[name] == value, f"{label}: {name}={database[name]}, expected {value}")
    require(database["value_bytes_written"] > 0, label + ": missing committed value bytes")


def noise(path, attempt):
    raw = path.read_bytes()
    events = [json.loads(line) for line in raw.splitlines() if line]
    start = [e for e in events if e["event"] == "start"]
    finish = [e for e in events if e["event"] == "finish"]
    require(len(start) == len(finish) == 1, "expected one monitored invocation")
    start, finish = start[0], finish[0]
    samples = [e for e in events if e["event"] in {"start", "sample", "finish"}]
    require(start["time_utc"] == attempt["measurement_start_utc"] and finish["time_utc"] == attempt["measurement_finish_utc"], "monitored interval mismatch")
    require(finish["exit_code"] == 0, "benchmark did not exit successfully")
    require(all(e["quiet"] is True and e["checks"] and all(e["checks"].values()) for e in events if "quiet" in e), "failed quiet-window check")
    complete = [e for e in events if e["event"] == "attempt_complete"]
    require(len(complete) == 1 and complete[0]["status"] == "retained", "incomplete monitoring receipt")
    rates = []
    boundary = 0
    for e in samples[1:]:
        usage = e["cpu_usage"]
        require(usage["enforced"] and usage["system_steal_policy"] == "record_only", "unexpected CPU-window policy")
        if usage["interval_start_monotonic"] < start["monotonic_seconds"]:
            boundary += 1
        rates.append(usage)
    require(rates, "no monitored CPU windows")
    overlaps = sum(b["interval_start_monotonic"] < a["interval_finish_monotonic"] for a, b in zip(rates, rates[1:]))
    keys = ("system_steal_cores", "instrumentation_aggregate_cores", "outside_aggregate_cores", "outside_max_process_cores", "swap_pages_per_second", "interval_seconds")
    for e in samples:
        require(e["instrumentation_identity"] == start["instrumentation_identity"], "controller identity changed")
    hz = start["cpu_clock_ticks_per_second"]
    require(hz > 0 and finish["cpu_clock_ticks_per_second"] == hz, "CPU clock mismatch")
    deltas = {key: finish[key] - start[key] for key in ("system_steal_ticks", "swap_in_pages", "swap_out_pages")}
    require(all(value >= 0 for value in deltas.values()), "system counter decreased")
    duration = finish["monotonic_seconds"] - start["monotonic_seconds"]
    require(duration > 0, "invalid monitored interval")
    return {
        "journal_sha256": digest(raw), "start_utc": start["time_utc"], "finish_utc": finish["time_utc"],
        "invocation_seconds": duration, "samples": len(samples), "cpu_windows": len(rates),
        "overlapping_cpu_windows": overlaps, "cpu_windows_starting_before_invocation": boundary,
        "all_guard_checks_passed": True, "guard_check_counts": dict(collections.Counter(k for e in samples for k in e["checks"])),
        "maximum_sample_gap_seconds": max(b["monotonic_seconds"] - a["monotonic_seconds"] for a, b in zip(samples, samples[1:])),
        "sample_distributions": {key: distribution([e[key] for e in rates]) for key in keys},
        "start_finish_cumulative_counter_deltas": deltas,
        "host_steal_cpu_seconds_from_endpoints": deltas["system_steal_ticks"] / hz,
        "controller_identity": start["instrumentation_identity"],
        "method": "Distributions are unweighted recorded CPU-window rates; overlapping windows are never summed. Start/finish steal and swap differences use cumulative counters once. The invocation includes fixture setup and verification, not only timed batches. Host-steal telemetry does not establish physical-host isolation; short-lived unobserved work and below-threshold activity remain possible.",
    }


def csv_write(path, rows):
    require(rows, "empty CSV export")
    columns = list(rows[0])
    require(all(list(row) == columns for row in rows), "inconsistent CSV columns")
    with path.open("x", newline="") as output:
        writer = csv.DictWriter(output, columns)
        writer.writeheader()
        writer.writerows(rows)


def ratio_text(value):
    return f"{value['median']:.3f} [{value['min']:.3f}, {value['max']:.3f}]"


def markdown(groups, concise):
    lines = ["# Predeclared native persistence comparisons", "", "Batch ratios compare matched trials; values above 1 mean the denominator finished sooner. Each ratio is median [minimum, maximum] across three trials. Per-trial latency percentiles are never pooled. These are component observations, with no significance or Mythic-wide speedup claim.", ""]
    if concise:
        for scenario in ("small_stream", "burst_512"):
            lines += [f"## {scenario}", "", "Batch milliseconds show the median of three batch durations for snapshot / row / cached row. The ratios are medians of paired ratios, not ratios of medians.", "", "| Backend | Peers | Direction | Batch ms S / R / C | S/R | S/C | R/C |", "|---|---:|---|---:|---:|---:|---:|"]
            for group in groups:
                if group["scenario"] != scenario:
                    continue
                durations = " / ".join(f"{statistics.median(t[a]['server_batch_ns'] for t in group['trials']) / 1e6:.3f}" for a in ARMS)
                ratios = " | ".join(ratio_text(group["paired_batch_ratios"][c]) for c in COMPARISONS)
                lines.append(f"| {group['backend']} | {group['peers']} | {group['direction']} | {durations} | {ratios} |")
            lines.append("")
    else:
        for group in groups:
            lines += [f"## {group['backend']} / {group['peers']} peers / {group['scenario']} / {group['direction']}", "", f"Each arm processes {group['messages']} messages and {group['plaintext_bytes']} plaintext bytes per trial.", "", "| Trial | Arm | Position | Batch ms | Ops/s | MiB/s | p50 / p95 / p99 μs | Loads / expects / stores | Fetches / validations / writes | Exchanges |", "|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|"]
            for trial in group["trials"]:
                for arm in ARMS:
                    value = trial[arm]; db = value["database"]
                    tail = " / ".join(f"{value['latency_ns'][key] / 1e3:.3f}" for key in ("p50", "p95", "p99"))
                    lines.append(f"| {trial['trial']} | {arm} | {trial['arm_order'].index(arm)} | {value['server_batch_ns'] / 1e6:.3f} | {value['operations_per_second']:.3f} | {value['plaintext_mib_per_second']:.3f} | {tail} | {db['loads']} / {db['expects']} / {db['stores']} | {db['reads']} / {db['validation_rows']} / {db['writes']} | {db['network_exchanges']} |")
            lines += ["", "| Trial | S/R | S/C | R/C |", "|---:|---:|---:|---:|"]
            for trial in group["trials"]:
                lines.append(f"| {trial['trial']} | " + " | ".join(f"{trial[c + '_batch_ratio']:.6f}" for c in COMPARISONS) + " |")
            lines += ["| Median [min, max] | " + " | ".join(ratio_text(group["paired_batch_ratios"][c]) for c in COMPARISONS) + " |", ""]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--collection", type=Path, required=True)
    parser.add_argument("--analysis-plan", type=Path, default=HERE / "analysis-plan.json")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--authorized-after-completion", action="store_true")
    args = parser.parse_args()
    require(args.authorized_after_completion, "root authorization after all six axes is required")
    collection = args.collection.resolve()
    plan, plan_hash = read(collection / "collection-plan.json")
    analysis, analysis_hash = read(args.analysis_plan)
    require(analysis_hash == ANALYSIS_HASH, "predeclared analysis plan changed")
    require(plan_hash == PLAN_HASH, "this exporter is pinned to the declared v2 collection")
    require(plan["build_receipt"]["binary_sha256"] == BINARY_HASH, "benchmark binary changed")
    require(collection == Path(plan["collection_directory"]).resolve(), "collection path mismatch")
    require(collection != Path(plan["measurement_policy"]["supersedes_campaign"]).resolve(), "superseded timings prohibited")
    require([(a["backend"], a["peers"]) for a in plan["axes"]] == AXES, "unexpected declared axes")
    require(analysis["timings_inspected"] is False and "72" in analysis["full_tables"], "unexpected analysis plan")
    retained, retained_hash = read(collection / "collection-retained.json")
    require(retained["plan_sha256"] == plan_hash and len(retained["reports"]) == 6, "six-axis collection is not complete")
    source = collection / "summarize.py"
    source_hash = digest(source.read_bytes())
    require(source_hash == plan["build_receipt"]["source_sha256"]["beaconcrypt/examples/persistence_bench/summarize.py"], "summarizer differs from committed build source")
    spec = importlib.util.spec_from_file_location("committed_summary", source)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    groups, batches, pairs, axes, noise_rows = [], [], [], [], []
    fixtures_seen = set()
    operations = plaintext = 0
    counter_checks = 0
    for index, entry in enumerate(retained["reports"]):
        backend, peers = AXES[index]
        require(entry["axis_index"] == index and entry["axis"] == plan["axes"][index] and entry["status"] == "retained" and entry["plan_sha256"] == plan_hash, "retained axis identity mismatch")
        directory = collection / f"axis-{index+1:02d}-{backend}-peers-{peers}-attempt-{entry['attempt']:02d}"
        require(Path(entry["directory"]).resolve() == directory, "retained directory mismatch")
        attempt, attempt_hash = read(directory / "attempt.json")
        require(attempt == entry, "retained index differs from final attempt receipt")
        # Read earlier dispositions only, never earlier timing reports.
        for n in range(1, entry["attempt"]):
            previous = collection / f"axis-{index+1:02d}-{backend}-peers-{peers}-attempt-{n:02d}" / "attempt.json"
            if previous.exists():
                prior, _ = read(previous)
                require(prior["status"] == "discarded_interference" and prior["plan_sha256"] == plan_hash, "earlier valid result or hard failure must not be bypassed")
        report, report_hash = read(directory / "report.json")
        saved, summary_hash = read(directory / "summary.json")
        require(report_hash == entry["report_sha256"] and summary_hash == entry["summary_sha256"], "report or summary hash mismatch")
        require(report["schema_version"] == 2 and report["backend"] == backend and report["config"]["peer_counts"] == [peers] and report["config"]["trials"] == 3, "unexpected report axes/schema")
        expected_config = {"backend": backend, "peer_counts": [peers], "active_peers": None}
        options = plan["workload_arguments"]
        for flag, value in zip(options[::2], options[1::2]):
            key = flag.removeprefix("--").replace("-", "_")
            expected_config[key] = list(map(int, value.split(","))) if key == "burst_chunks" else int(value)
        require(report["config"] == expected_config, "report differs from declared workload")
        summary = module.summarize(report)
        require(saved.get("input_sha256") == report_hash and {k: v for k, v in saved.items() if k not in {"input_path", "input_sha256"}} == summary, "saved summary differs from revalidated report")
        require(len(report["results"]) == 108 and len(summary["groups"]) == 12, "axis is not a complete matrix")
        for fixture in report["fixtures"]:
            lineage = tuple(fixture["lineage"])
            require(lineage not in fixtures_seen, "fixture lineage reused across axes")
            fixtures_seen.add(lineage)
            counters(fixture["warm_database"], backend, fixture["arm"], 2 * report["config"]["warmup_messages"], f"{backend}/{peers}/warm/{fixture['arm']}")
            counter_checks += 1
        for value in report["results"]:
            counters(value["database"], backend, value["arm"], value["messages"], f"{backend}/{peers}/{value['scenario']}/{value['direction']}/{value['trial']}/{value['arm']}")
            counter_checks += 1
            operations += value["messages"]; plaintext += value["plaintext_bytes"]
            row = {"backend": backend, "peers": peers, **{key: value[key] for key in ("scenario", "direction", "trial", "arm", "pair_order", "active_peers", "touched_peers", "messages", "plaintext_bytes", "wire_bytes", "server_batch_ns", "sum_operation_ns", "operations_per_second", "plaintext_mib_per_second")}}
            row.update({"latency_ns_" + key: value["latency_ns"][key] for key in ("min", "p50", "p95", "p99", "max", "mean")})
            row.update({"database_" + key: value["database"][key] for key in COUNTERS})
            batches.append(row)
        for group in summary["groups"]:
            group = {"backend": backend, **group}; groups.append(group)
            for trial in group["trials"]:
                row = {"backend": backend, "peers": peers, "scenario": group["scenario"], "direction": group["direction"], "trial": trial["trial"], "arm_order": "/".join(trial["arm_order"]), "messages_per_arm": group["messages"], "plaintext_bytes_per_arm": group["plaintext_bytes"]}
                for arm in ARMS:
                    value = trial[arm]
                    row.update({arm + "_" + k: value[k] for k in ("server_batch_ns", "operations_per_second", "plaintext_mib_per_second")})
                    row.update({arm + "_latency_ns_" + k: value["latency_ns"][k] for k in ("min", "p50", "p95", "p99", "max", "mean")})
                    row.update({arm + "_database_" + k: value["database"][k] for k in COUNTERS})
                row.update({c + "_batch_ratio": trial[c + "_batch_ratio"] for c in COMPARISONS})
                pairs.append(row)
        telemetry = noise(directory / "quiet-window.jsonl", attempt)
        axes.append({"axis_index": index, "backend": backend, "peers": peers, "attempt": entry["attempt"], "directory": str(directory), "report_sha256": report_hash, "summary_sha256": summary_hash, "attempt_sha256": attempt_hash, "noise": telemetry})
        for metric, values in telemetry["sample_distributions"].items():
            noise_rows.append({"backend": backend, "peers": peers, "metric": metric, **values})
    require((len(groups), len(pairs), len(batches), operations, plaintext) == (72, 216, 648, 324864, 47584641024), "collection total mismatch")
    groups.sort(key=lambda g: (g["backend"], g["peers"], g["scenario"], g["direction"]))
    group_rows = []
    for group in groups:
        row = {key: group[key] for key in ("backend", "peers", "scenario", "direction", "active_peers", "touched_peers", "messages", "plaintext_bytes", "wire_bytes")}
        for comparison in COMPARISONS:
            row.update({comparison + "_" + k: v for k, v in group["paired_batch_ratios"][comparison].items()})
        for pair in [p for p in pairs if (p["backend"], p["peers"], p["scenario"], p["direction"]) == (group["backend"], group["peers"], group["scenario"], group["direction"])]:
            row.update({f"trial{pair['trial']}_" + k: v for k, v in pair.items() if k not in {"backend", "peers", "scenario", "direction", "trial", "messages_per_arm", "plaintext_bytes_per_arm"}})
        group_rows.append(row)
    output = args.output.resolve()
    require(output != collection and not output.is_relative_to(collection), "export must be outside immutable collection")
    output.mkdir(parents=True, exist_ok=False)
    receipt = {"created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "analysis_plan": analysis, "analysis_plan_sha256": analysis_hash, "collection_plan_sha256": plan_hash, "retained_index_sha256": retained_hash, "summarizer_sha256": source_hash, "exporter_sha256": digest(Path(__file__).read_bytes()), "binary_sha256": BINARY_HASH, "source_commit": plan["build_receipt"]["source_commit"], "groups": 72, "paired_trial_rows": 216, "arm_batch_records": 648, "operations": operations, "plaintext_bytes": plaintext, "validated_counter_records": counter_checks, "axes": axes, "selection": "Only the predeclared retained index; no timing-based filtering or alternate attempt selection.", "statistics": "Ratios computed within matched trials; group summaries are min/median/max of those ratios. Raw per-trial percentiles remain separate. No cross-trial latency pooling or significance claims.", "counters": "Logical row API/SQL accounting only; byte metrics overlap and are not summed as traffic. Saved fetches do not imply elimination of database-side validation. SQLite sql calls snapshot/row/cached=4/5/4 per message; PostgreSQL query exchanges=1/2/1. Both row modes store one successor per successful message."}
    for name, value in (("analysis-receipt.json", receipt), ("all-groups.json", groups)):
        (output / name).write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    csv_write(output / "all-72-groups.csv", group_rows)
    csv_write(output / "paired-trials.csv", pairs)
    csv_write(output / "arm-batches.csv", batches)
    csv_write(output / "noise-distributions.csv", noise_rows)
    (output / "concise-tables.md").write_text(markdown(groups, True))
    (output / "full-tables.md").write_text(markdown(groups, False))
    (output / "SHA256SUMS").write_text("".join(digest(p.read_bytes()) + "  " + p.name + "\n" for p in sorted(output.iterdir())))
    print(json.dumps({"status": "validated and exported", "output": str(output), "groups": 72, "operations": operations, "plaintext_bytes": plaintext}))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as error:
        raise SystemExit("analysis refused: " + str(error))
