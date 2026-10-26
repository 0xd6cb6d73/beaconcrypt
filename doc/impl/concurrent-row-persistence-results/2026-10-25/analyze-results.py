#!/usr/bin/env python3
"""Export explicitly supplied retained schema-3 reports after collection finishes.

No services, builds, benchmarks, attempt discovery, or timing-based selection.
Every report is revalidated by the plan-pinned summarizer before any output.
"""

import argparse
import csv
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import statistics
import sys

ARMS = ("snapshot", "row", "cached_row")
PAIRS = (("snapshot", "row"), ("snapshot", "cached_row"), ("row", "cached_row"))
QUANTILES = ("p50", "p95", "p99")
LIMITS = (
    "All reports belong to the authoritative completed collection-retained.json set, with matching attempt receipts and completion event. This helper performs no attempt discovery or timing-based selection.",
    "Snapshot uses one serial owner and one database connection. Row and cached-row use stable peer lanes with independent owners/connections and equal total queue bounds. Snapshot/row ratios include this ownership difference; row/cached-row comparisons share the owner topology.",
    "All offered requests drain successfully. Planned-arrival response time includes scheduler backlog, blocked admission, owner-queue wait, dispatch, native API service, and completion overhead. No automatic retries or discarded overload are accepted.",
    "Periodic work is paced. Its full-batch completion rate can be arrival-limited; use deadlines, response latency and backlog to assess it rather than calling a near-equal batch duration equal capacity. Burst MB/s uses all offered plaintext bytes and full drain time.",
    "All percentiles are computed within one trial. A response-p95 ratio divides the two arms' per-trial p95 values; it is not a p95 of per-callback ratios. Across-trial aggregates summarize trial statistics or within-trial paired ratios; they never pool request latencies across trials. Ratios whose denominator is zero are null with explicit counts, not silently replaced.",
    "source_backlog_ns is computed per callback as scheduler_lag_ns + enqueue_backpressure_ns before taking percentiles. Percentiles of stages cannot be added to obtain a response percentile.",
    "queue_wait_ns includes waiting for the serial owner. owner_wait_ns is dequeue-to-native dispatch overhead, not a separate contended owner mutex. Native API service includes database work; database client spans and overlap are not pure crypto or physical database CPU/write concurrency.",
    "Overlapping interval durations are reported as unions by the validated summarizer, never added as wall time. Logical SQL counters and plaintext bytes are not physical I/O. No significance, cross-window causal comparison, or Mythic end-to-end speedup is inferred.",
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_module(path):
    spec = importlib.util.spec_from_file_location("concurrent_analysis_summary", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def statistics_of_trials(values):
    present = [value for value in values if value is not None]
    return {
        "count": len(present),
        "undefined_count": len(values) - len(present),
        "min": min(present) if present else None,
        "median": statistics.median(present) if present else None,
        "max": max(present) if present else None,
    }


def flatten(prefix, mapping, target):
    for key, value in mapping.items():
        name = prefix + key
        if isinstance(value, dict):
            flatten(name + "_", value, target)
        else:
            target[name] = value


def derived_latencies(observations, summary_module):
    metrics = [entry["metrics"] for entry in observations]
    return {
        key: summary_module.concurrent_distribution(values)
        for key, values in {
            "response_ns": [value["response_ns"] for value in metrics],
            "source_backlog_ns": [
                value["scheduler_lag_ns"] + value["enqueue_backpressure_ns"]
                for value in metrics
            ],
            "scheduler_lag_ns": [value["scheduler_lag_ns"] for value in metrics],
            "enqueue_backpressure_ns": [
                value["enqueue_backpressure_ns"] for value in metrics
            ],
            "queue_wait_ns": [value["queue_wait_ns"] for value in metrics],
            "owner_dispatch_ns": [value["owner_wait_ns"] for value in metrics],
            "native_service_ns": [value["service_ns"] for value in metrics],
            "completion_overhead_ns": [
                value["completion_overhead_ns"] for value in metrics
            ],
            "deadline_lag_ns": [value["deadline_lag_ns"] for value in metrics],
        }.items()
    }


def analyze(validated, summary_module):
    """Pure transform of (raw report, independently validated summary) pairs."""
    arm_rows, cohort_rows, ratio_rows, groups = [], [], [], []
    report_count = 0
    for report, summary in validated:
        report_count += 1
        raw_by_key = {
            (value["peers"], value["scenario"], value["trial"], value["arm"]): value
            for value in report["results"]
        }
        backend = report["backend"]
        for group in summary["groups"]:
            common = {
                "backend": backend,
                "registered_peers": group["peers"],
                "active_peers": group["active_peers"],
                "scenario": group["scenario"],
            }
            group_rows, group_ratios = [], []
            for trial in group["trials"]:
                paired = {}
                for arm in ARMS:
                    raw = raw_by_key[
                        group["peers"], group["scenario"], trial["trial"], arm
                    ]
                    value = trial[arm]
                    jobs = {job["id"]: job for job in raw["scheduled"]}
                    periods = {
                        entry["peer"]: entry["period_ns"]
                        for entry in group["peer_schedule"]
                    }
                    duration = value["server_batch_ns"]
                    horizon = group["planned_horizon_ns"]
                    last_arrival = max(job["scheduled_ns"] for job in jobs.values())
                    burst = group["scenario"].startswith("burst_")
                    row = {
                        **common,
                        "trial": trial["trial"],
                        "arm": arm,
                        "arm_order": trial["arm_order"].index(arm),
                        "owner_workers": value["owner_workers"],
                        "logical_feeder_lanes": value["logical_feeder_lanes"],
                        "touched_peers": raw["touched_peers"],
                        "offered": value["offered"],
                        "completed": value["completed"],
                        "plaintext_bytes": group["plaintext_bytes"],
                        "wire_bytes": raw["wire_bytes"],
                        "planned_horizon_ns": horizon,
                        "last_planned_arrival_ns": last_arrival,
                        "deadline_budget_ns": raw["deadline_budget_ns"],
                        "drain_budget_ns": raw["drain_budget_ns"],
                        "server_batch_ns": duration,
                        "drain_after_last_arrival_ns": max(0, duration - last_arrival),
                        "backlog_after_offer_window_ns": max(0, duration - horizon),
                        "deadline_met": value["deadline_met"],
                        "deadline_missed": value["deadline_missed"],
                        "deadline_success_fraction": value["deadline_success_fraction"],
                        "completed_per_second_full_batch": value[
                            "operations_per_second"
                        ],
                        "plaintext_mb_per_second_full_batch": group["plaintext_bytes"]
                        / (duration / 1e9)
                        / 1_000_000,
                        "plaintext_mib_per_second_full_batch": value[
                            "plaintext_mib_per_second"
                        ],
                        "burst_mb_per_second": (
                            group["plaintext_bytes"] / (duration / 1e9) / 1_000_000
                            if burst
                            else None
                        ),
                        "rate_interpretation": (
                            "burst drain"
                            if burst
                            else "paced completion; may be arrival-limited"
                        ),
                    }
                    flatten(
                        "", derived_latencies(raw["observations"], summary_module), row
                    )
                    flatten("database_", value["database"], row)
                    for name, stats in value["overlap"].items():
                        flatten("overlap_" + name + "_", stats, row)
                        row["overlap_" + name + "_multiple_fraction_of_batch"] = (
                            stats["multiple_active_ns"] / duration
                        )
                    row["queue_high_water_jobs_sum"] = sum(
                        queue["high_water_jobs"] for queue in value["queues"]
                    )
                    row["queue_high_water_bytes_sum"] = sum(
                        queue["high_water_bytes"] for queue in value["queues"]
                    )
                    row["queue_high_water_interpretation"] = (
                        "sum of per-queue maxima; not a simultaneous total high-water mark"
                    )
                    for field in (
                        "network_exchanges",
                        "sql_calls",
                        "loads",
                        "expects",
                        "stores",
                    ):
                        row["database_" + field + "_per_completed"] = (
                            value["database"][field] / value["completed"]
                        )
                    paired[arm] = row
                    arm_rows.append(row)
                    group_rows.append(row)
                    partitions = {}
                    for observation in raw["observations"]:
                        job = jobs[observation["id"]]
                        period, flow, payload = (
                            periods[job["peer"]],
                            job["flow"],
                            job["payload"],
                        )
                        for key in (
                            ("period", period, "all", "all"),
                            ("flow", "all", flow, "all"),
                            ("payload", "all", "all", payload),
                            ("period_flow_payload", period, flow, payload),
                        ):
                            partitions.setdefault(key, []).append(observation)
                    for (kind, period, flow, payload), entries in sorted(
                        partitions.items(), key=lambda item: str(item[0])
                    ):
                        cohort = {
                            **common,
                            "trial": trial["trial"],
                            "arm": arm,
                            "cohort_kind": kind,
                            "period_ns": period,
                            "flow": flow,
                            "payload": payload,
                            "offered": len(entries),
                            "completed": len(entries),
                            "plaintext_bytes": sum(
                                jobs[entry["id"]]["plaintext_bytes"]
                                for entry in entries
                            ),
                            "deadline_met": sum(
                                entry["metrics"]["deadline_met"] for entry in entries
                            ),
                        }
                        cohort["deadline_success_fraction"] = (
                            cohort["deadline_met"] / cohort["offered"]
                        )
                        flatten("", derived_latencies(entries, summary_module), cohort)
                        cohort_rows.append(cohort)
                for numerator, denominator in PAIRS:
                    first, second = paired[numerator], paired[denominator]
                    comparison = numerator + "_over_" + denominator
                    for metric in (
                        "server_batch_ns",
                        "drain_after_last_arrival_ns",
                        "backlog_after_offer_window_ns",
                        *("response_ns_" + q for q in QUANTILES),
                        "native_service_ns_p95",
                        "queue_wait_ns_p95",
                        "source_backlog_ns_p95",
                    ):
                        entry = {
                            **common,
                            "trial": trial["trial"],
                            "comparison": comparison,
                            "metric": metric,
                            "numerator": first[metric],
                            "denominator": second[metric],
                            "ratio": (
                                first[metric] / second[metric]
                                if second[metric]
                                else None
                            ),
                            "denominator_zero": second[metric] == 0,
                            "numerator_owner_workers": first["owner_workers"],
                            "denominator_owner_workers": second["owner_workers"],
                            "deadline_success_fraction_difference": first[
                                "deadline_success_fraction"
                            ]
                            - second["deadline_success_fraction"],
                        }
                        ratio_rows.append(entry)
                        group_ratios.append(entry)
            aggregates = []
            for comparison in (a + "_over_" + b for a, b in PAIRS):
                metrics = sorted({row["metric"] for row in group_ratios})
                for metric in metrics:
                    values = [
                        row["ratio"]
                        for row in group_ratios
                        if row["comparison"] == comparison and row["metric"] == metric
                    ]
                    aggregates.append(
                        {
                            "comparison": comparison,
                            "metric": metric,
                            **statistics_of_trials(values),
                        }
                    )
            trial_statistics = {}
            fields = (
                "deadline_success_fraction",
                "server_batch_ns",
                "backlog_after_offer_window_ns",
                "burst_mb_per_second",
                *("response_ns_" + q for q in QUANTILES),
                "source_backlog_ns_p95",
                "queue_wait_ns_p95",
                "native_service_ns_p95",
                "overlap_native_peak",
                "overlap_database_client_call_peak",
            )
            for arm in ARMS:
                trial_statistics[arm] = {
                    field: statistics_of_trials(
                        [row[field] for row in group_rows if row["arm"] == arm]
                    )
                    for field in fields
                }
            groups.append(
                {
                    **common,
                    "offered_per_arm_trial": group["offered"],
                    "plaintext_bytes_per_arm_trial": group["plaintext_bytes"],
                    "planned_horizon_ns": group["planned_horizon_ns"],
                    "peer_schedule": group["peer_schedule"],
                    "paired_trial_ratios": aggregates,
                    "statistics_across_trials_not_pooled": trial_statistics,
                }
            )
        # The iterator will decode the next axis only after these references
        # to the preceding report have been released. Derived rows are small.
        del report, summary, raw_by_key, raw, jobs, partitions, entries, observation
    return (
        {
            "schema_version": 1,
            "input_schema_version": 3,
            "definitions": list(LIMITS),
            "report_count": report_count,
            "group_count": len(groups),
            "arm_trial_rows": len(arm_rows),
            "paired_metric_rows": len(ratio_rows),
            "cohort_rows": len(cohort_rows),
            "total_completed_callbacks_across_all_arms_trials": sum(
                row["completed"] for row in arm_rows
            ),
            "total_plaintext_bytes_across_all_arms_trials": sum(
                row["plaintext_bytes"] for row in arm_rows
            ),
            "groups": groups,
        },
        arm_rows,
        ratio_rows,
        cohort_rows,
    )


def validate_inputs(plan_path, reports, summarizer_path):
    plan_raw = plan_path.read_bytes()
    plan = json.loads(plan_raw)
    require(
        plan["machinery_sha256"]["summarize.py"]
        == digest(summarizer_path.read_bytes()),
        "summarizer does not match frozen collection plan",
    )
    module = load_module(summarizer_path)
    expected = {(axis["backend"], axis["peers"]) for axis in plan["axes"]}
    require(
        expected and len(expected) == len(plan["axes"]) == len(reports),
        "report count or declared axes are duplicate/incomplete",
    )
    retained_path = plan_path.parent / "collection-retained.json"
    retained_raw = retained_path.read_bytes()
    retained = json.loads(retained_raw)
    require(
        retained["plan_sha256"] == digest(plan_raw)
        and isinstance(retained["completed_utc"], str)
        and datetime.datetime.fromisoformat(retained["completed_utc"]).tzinfo
        is not None
        and len(retained["reports"]) == len(expected),
        "authoritative collection is incomplete or belongs to another plan",
    )
    published = {}
    for selected in retained["reports"]:
        index = selected["axis_index"]
        require(
            type(index) is int
            and 0 <= index < len(plan["axes"])
            and selected["axis"] == plan["axes"][index]
            and selected["status"] == "retained"
            and selected["plan_sha256"] == digest(plan_raw)
            and selected["binary_sha256"] == plan["build_receipt"]["binary_sha256"]
            and type(selected["attempt"]) is int
            and selected["attempt"] > 0,
            "invalid authoritative retained attempt",
        )
        axis = selected["axis"]["backend"], selected["axis"]["peers"]
        require(axis not in published, "duplicate authoritative retained axis")
        # Preserve the authoritative relative attempt path when an entire archive
        # is relocated. Never search for another attempt or open the old root.
        relative = Path(selected["directory"]).relative_to(plan["collection_directory"])
        require(
            len(relative.parts) == 1 and relative.name not in {".", ".."},
            "invalid retained attempt directory",
        )
        published[axis] = (
            selected,
            (plan_path.parent / relative / "report.json").resolve(),
        )
    require(set(published) == expected, "authoritative retained axes are incomplete")
    events_path = plan_path.parent / "collection-events.jsonl"
    events_hash = hashlib.sha256()
    watcher_seen = completion_seen = False
    with events_path.open("rb") as stream:
        for line in stream:
            events_hash.update(line)
            if not line.strip():
                continue
            event = json.loads(line)
            if event.get("event") == "watcher_start":
                require(
                    event["plan_sha256"] == digest(plan_raw),
                    "collection watcher plan mismatch",
                )
                watcher_seen = True
            elif event.get("event") == "collection_complete":
                require(
                    type(event.get("reports")) is int
                    and event["reports"] == len(expected),
                    "collection completion count mismatch",
                )
                completion_seen = True
    require(
        watcher_seen and completion_seen,
        "collection completion event is absent or inconsistent",
    )
    inputs = []

    def validated_axes():
        # Each raw JSON tree lives for one axis, not the whole six-axis campaign.
        seen = set()
        for path in reports:
            raw = path.read_bytes()
            report = json.loads(raw)
            require(
                len(report["config"]["peer_counts"]) == 1,
                "each retained report must contain exactly one registered-population axis",
            )
            axis = report["backend"], report["config"]["peer_counts"][0]
            require(
                axis in expected and axis not in seen,
                "unexpected or duplicate retained axis",
            )
            seen.add(axis)
            attempt_path = path.parent / "attempt.json"
            attempt_raw = attempt_path.read_bytes()
            attempt = json.loads(attempt_raw)
            require(
                attempt["status"] == "retained",
                "attempt was not retained by the collection guard",
            )
            selected, selected_path = published[axis]
            require(
                attempt == selected and path.resolve() == selected_path,
                "supplied report is not the authoritative retained attempt",
            )
            require(
                type(attempt["axis_index"]) is int
                and 0 <= attempt["axis_index"] < len(plan["axes"])
                and attempt["axis"] == {"backend": axis[0], "peers": axis[1]}
                and plan["axes"][attempt["axis_index"]] == attempt["axis"],
                "attempt axis differs from plan/report",
            )
            require(
                attempt["plan_sha256"] == digest(plan_raw)
                and attempt["binary_sha256"] == plan["build_receipt"]["binary_sha256"],
                "attempt source/plan binding mismatch",
            )
            require(
                attempt["report_sha256"] == digest(raw), "retained report hash differs"
            )
            require(
                report["schema_version"] == 3
                and report["config"]
                == {
                    **plan["expected_config"],
                    "backend": axis[0],
                    "peer_counts": [axis[1]],
                }
                and report["concurrency"] == plan["expected_concurrency"],
                "report workload differs from declared plan",
            )
            summary = module.summarize(report)
            stored_path = path.parent / "summary.json"
            stored_raw = stored_path.read_bytes()
            stored = json.loads(stored_raw)
            require(
                attempt["summary_sha256"] == digest(stored_raw)
                and stored.pop("input_sha256") == digest(raw),
                "retained summary hash/input mismatch",
            )
            stored.pop("input_path")
            require(
                stored == summary, "recomputed summary differs from retained summary"
            )
            inputs.append(
                {
                    "backend": axis[0],
                    "registered_peers": axis[1],
                    "report_path": str(path.resolve()),
                    "report_sha256": digest(raw),
                    "attempt_path": str(attempt_path.resolve()),
                    "attempt_sha256": digest(attempt_raw),
                    "summary_sha256": digest(stored_raw),
                }
            )
            del raw, stored_raw, stored
            yield report, summary
            del report, summary
        require(seen == expected, "missing retained axis")

    return (
        module,
        validated_axes(),
        {
            "plan_path": str(plan_path.resolve()),
            "plan_sha256": digest(plan_raw),
            "retained_manifest_path": str(retained_path.resolve()),
            "retained_manifest_sha256": digest(retained_raw),
            "collection_events_path": str(events_path.resolve()),
            "collection_events_sha256": events_hash.hexdigest(),
            "summarizer_path": str(summarizer_path.resolve()),
            "summarizer_sha256": digest(summarizer_path.read_bytes()),
            "binary_sha256": plan["build_receipt"]["binary_sha256"],
            "inputs": inputs,
        },
    )


def csv_file(path, rows):
    fields = list(dict.fromkeys(key for row in rows for key in row))
    with path.open("x", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def tables(rows):
    text = [
        "# Concurrent persistence analysis",
        "",
        *[paragraph + "\n" for paragraph in LIMITS],
        "Per-trial values below use milliseconds; throughput uses decimal MB/s. Complete numeric values and all cohort breakdowns are in the CSV files.",
        "",
    ]
    keys = list(
        dict.fromkeys(
            (row["backend"], row["registered_peers"], row["scenario"]) for row in rows
        )
    )
    for backend, peers, scenario in keys:
        selected = [
            row
            for row in rows
            if (row["backend"], row["registered_peers"], row["scenario"])
            == (backend, peers, scenario)
        ]
        text += [
            f"## {backend}: {peers} registered peers, {selected[0]['active_peers']} active / {scenario}",
            "",
            "| Trial | Arm | Offered/drained | Deadline met | Response p50/p95/p99 ms | Source backlog p95 ms | Owner queue p95 ms | Native API p95 ms | Native/DB peak | DB exchanges/SQL calls per callback | Drain after last arrival ms | Burst MB/s |",
            "|---:|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|",
        ]
        for row in selected:
            response = "/".join(
                f"{row['response_ns_' + q] / 1e6:.3f}" for q in QUANTILES
            )
            burst_rate = (
                "—"
                if row["burst_mb_per_second"] is None
                else f"{row['burst_mb_per_second']:.3f}"
            )
            text.append(
                f"| {row['trial']} | {row['arm']} | {row['offered']}/{row['completed']} | {row['deadline_met']}/{row['offered']} | {response} | {row['source_backlog_ns_p95']/1e6:.3f} | {row['queue_wait_ns_p95']/1e6:.3f} | {row['native_service_ns_p95']/1e6:.3f} | {row['overlap_native_peak']}/{row['overlap_database_client_call_peak']} | {row['database_network_exchanges_per_completed']:.0f}/{row['database_sql_calls_per_completed']:.0f} | {row['drain_after_last_arrival_ns']/1e6:.3f} | {burst_rate} |"
            )
        text.append("")
    return "\n".join(text)


def write_outputs(output, result, arms, ratios, cohorts, receipt):
    output.mkdir(parents=False, exist_ok=False)
    (output / "analysis.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n"
    )
    (output / "input-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    csv_file(output / "arm-trials.csv", arms)
    csv_file(output / "paired-trial-ratios.csv", ratios)
    csv_file(
        output / "paired-ratio-summary.csv",
        [
            {
                **{
                    key: group[key]
                    for key in (
                        "backend",
                        "registered_peers",
                        "active_peers",
                        "scenario",
                    )
                },
                **ratio,
            }
            for group in result["groups"]
            for ratio in group["paired_trial_ratios"]
        ],
    )
    csv_file(output / "cohort-trials.csv", cohorts)
    (output / "tables.md").write_text(tables(arms) + "\n")
    (output / "README.md").write_text(
        "\n\n".join(LIMITS)
        + "\n\nanalysis.json contains min/median/max summaries of matched trial ratios and trial statistics. arm-trials.csv contains each arm/trial's stages, deadlines, workload, drain, counters and overlap. paired-trial-ratios.csv preserves every ratio operand and paired-ratio-summary.csv summarizes those matched ratios; cohort-trials.csv includes marginal and joint period/flow/payload groups, which overlap and must not be summed across cohort kinds. tables.md shows per-trial values without pooling. input-receipt.json binds all retained inputs, the plan, summarizer and this exporter.\n"
    )
    manifest = "".join(
        digest(path.read_bytes()) + "  " + path.name + "\n"
        for path in sorted(output.iterdir())
    )
    (output / "SHA256SUMS").write_text(manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument(
        "--report",
        required=True,
        action="append",
        type=Path,
        help="explicit retained report.json; repeat for every declared axis",
    )
    parser.add_argument(
        "--summarizer",
        type=Path,
        help="default: summarize.py beside the frozen collection plan",
    )
    parser.add_argument("--output", required=True, type=Path, help="new directory only")
    args = parser.parse_args()
    require(not args.output.exists(), "output directory already exists")
    summary_path = args.summarizer or args.plan.parent / "summarize.py"
    module, validated, receipt = validate_inputs(args.plan, args.report, summary_path)
    result, arms, ratios, cohorts = analyze(validated, module)
    receipt.update(
        exporter_path=str(Path(__file__).resolve()),
        exporter_sha256=digest(Path(__file__).read_bytes()),
    )
    write_outputs(args.output, result, arms, ratios, cohorts, receipt)
    print(
        json.dumps(
            {
                key: result[key]
                for key in (
                    "report_count",
                    "group_count",
                    "arm_trial_rows",
                    "paired_metric_rows",
                    "cohort_rows",
                    "total_completed_callbacks_across_all_arms_trials",
                    "total_plaintext_bytes_across_all_arms_trials",
                )
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError, IndexError) as error:
        print("invalid concurrent analysis input: " + str(error), file=sys.stderr)
        sys.exit(2)
