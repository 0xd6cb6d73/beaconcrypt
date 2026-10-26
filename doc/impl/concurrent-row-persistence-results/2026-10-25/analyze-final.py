#!/usr/bin/env python3
"""Analyze the five explicitly retained primary axes after the user stopped SQLite 1000."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


def file_hash(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output or root / "analysis-final"
    spec = importlib.util.spec_from_file_location("analysis_engine", root / "analyze-results.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    require = helper.require
    require(not output.exists(), "output directory already exists")
    selected = [
        ("collection-20261025", "axis-02-postgres-peers-1-attempt-02", "postgres", 1),
        ("collection-20261025", "axis-03-postgres-peers-100-attempt-01", "postgres", 100),
        ("collection-sqlite-wait-v2", "axis-01-sqlite-peers-1-attempt-01", "sqlite", 1),
        ("collection-sqlite-wait-v2", "axis-02-sqlite-peers-100-attempt-01", "sqlite", 100),
    ]
    final = root / "collection-postgres-final"
    final_report = final / "axis-01-postgres-peers-1000-attempt-01" / "report.json"
    module, final_validated, final_receipt = helper.validate_inputs(
        final / "collection-plan.json", [final_report], final / "summarize.py"
    )
    plans = {}
    campaign_receipts = []
    for name in ["collection-20261025", "collection-sqlite-wait-v2", "collection-postgres-final"]:
        directory = root / name
        path = directory / "collection-plan.json"
        plan = json.loads(path.read_bytes())
        plans[name] = plan
        require(plan["machinery_sha256"]["summarize.py"] == final_receipt["summarizer_sha256"],
                "all selected axes must use the unchanged summarizer")
        require(file_hash(directory / "summarize.py") == final_receipt["summarizer_sha256"],
                "campaign summarizer changed")
        campaign_receipts.append({
            "campaign": name,
            "scope": "completed declared one-axis collection" if name == "collection-postgres-final"
                     else "selected individually retained axes from an incomplete/stopped campaign",
            "plan_path": str(path.relative_to(root)), "plan_sha256": file_hash(path),
            "source_commit": plan["build_receipt"]["source_commit"],
            "binary_sha256": plan["build_receipt"]["binary_sha256"],
            "source_sha256": plan["build_receipt"]["source_sha256"],
            "cpu_limits": plan["cpu_limits"],
            "collection_events_sha256": file_hash(directory / "collection-events.jsonl"),
            "authoritative_completed_collection": name == "collection-postgres-final",
        })
    before = plans["collection-20261025"]["build_receipt"]["source_sha256"]
    after = plans["collection-sqlite-wait-v2"]["build_receipt"]["source_sha256"]
    require(before.keys() == after.keys(), "source inventory changed between builds")
    changed = [name for name in before if before[name] != after[name]]
    require(after == plans["collection-postgres-final"]["build_receipt"]["source_sha256"],
            "last two campaigns do not share the same source inventory")
    receipt = {
        "selection": "Five primary axes explicitly selected after the user stopped SQLite 1000; no timing-based selection or fabricated campaign completion.",
        "excluded": "Original SQLite1 is historical. Failed/interrupted/stopped SQLite1000 attempts are not primary observations.",
        "campaigns": campaign_receipts,
        "changed_source_files_between_builds": changed,
        "user_stop_receipt": {
            "path": "collection-sqlite-wait-v2/USER-DIRECTED-STOP.json",
            "sha256": file_hash(root / "collection-sqlite-wait-v2/USER-DIRECTED-STOP.json"),
        },
        "completed_final_campaign_validation": final_receipt,
        "inputs_from_incomplete_campaigns": [],
        "engine_path": "analyze-results.py", "engine_sha256": file_hash(root / "analyze-results.py"),
        "wrapper_path": str(Path(__file__).resolve()), "wrapper_sha256": file_hash(Path(__file__)),
    }

    def validated():
        for campaign, attempt_name, backend, peers in selected:
            directory = root / campaign
            path = directory / attempt_name / "report.json"
            plan = plans[campaign]
            attempt_path = path.parent / "attempt.json"
            attempt = json.loads(attempt_path.read_bytes())
            require(attempt["status"] == "retained", "selected attempt was not retained")
            require(attempt["axis"] == {"backend": backend, "peers": peers}
                    and plan["axes"][attempt["axis_index"]] == attempt["axis"], "axis mismatch")
            require(Path(attempt["directory"]).relative_to(plan["collection_directory"]) == Path(attempt_name),
                    "attempt directory mismatch")
            require(attempt["plan_sha256"] == file_hash(directory / "collection-plan.json")
                    and attempt["binary_sha256"] == plan["build_receipt"]["binary_sha256"],
                    "attempt plan/build binding mismatch")
            raw = path.read_bytes()
            raw_hash = helper.digest(raw)
            require(raw_hash == attempt["report_sha256"], "retained raw hash mismatch")
            report = json.loads(raw)
            del raw
            require(report["schema_version"] == 3 and report["backend"] == backend
                    and report["config"] == {**plan["expected_config"], "backend": backend, "peer_counts": [peers]}
                    and report["concurrency"] == plan["expected_concurrency"], "declared workload mismatch")
            summary = module.summarize(report)
            summary_path = path.parent / "summary.json"
            require(file_hash(summary_path) == attempt["summary_sha256"], "stored summary hash mismatch")
            stored = json.loads(summary_path.read_bytes())
            require(stored.pop("input_sha256") == raw_hash, "stored summary input mismatch")
            stored.pop("input_path")
            require(stored == summary, "fresh summary differs from stored summary")
            del stored
            receipt["inputs_from_incomplete_campaigns"].append({
                "campaign": campaign, "backend": backend, "registered_peers": peers,
                "report_path": str(path.relative_to(root)), "report_sha256": raw_hash,
                "attempt_path": str(attempt_path.relative_to(root)), "attempt_sha256": file_hash(attempt_path),
                "summary_sha256": attempt["summary_sha256"], "retained_attempt": attempt,
            })
            print(f"Validated {backend}/{peers} from retained {campaign}/{attempt_name}", flush=True)
            yield report, summary
            del report, summary
        yield from final_validated

    helper.LIMITS = (
        "Five explicit primary axes are used: PostgreSQL 1/100/1000 and SQLite 1/100. The first four are individually retained complete reports from two incomplete/stopped campaigns; only the final PostgreSQL campaign has a complete collection index. SQLite 1000 was stopped at the user's direction and is excluded. No campaign completion is fabricated and no timing-based attempt selection is performed.",
        *helper.LIMITS[1:],
        "Old PostgreSQL 1/100 use source e26909a; SQLite 1/100 and PostgreSQL 1000 use 77d5633d. The change raises only SQLite busy waiting from 5 to 600 seconds, with its settings test/documentation. PostgreSQL and common/library implementation are unchanged. Preserve both builds and separate collection windows.",
        "The final PostgreSQL 1000 window permits outside VM CPU below 1 core per process and 2 cores aggregate; earlier retained windows used 0.25 and 0.5. Host steal remains recorded only. These policy differences preclude claiming a controlled cross-window scaling experiment or an isolated physical host.",
    )
    result, arms, ratios, cohorts = helper.analyze(validated(), module)
    require((result["report_count"], result["group_count"], result["arm_trial_rows"],
             result["total_completed_callbacks_across_all_arms_trials"]) == (5, 65, 585, 1270800),
            "unexpected final matrix/cardinality")
    measured = []
    for backend, peers in [("postgres", 1), ("postgres", 100), ("sqlite", 1), ("sqlite", 100), ("postgres", 1000)]:
        for arm in helper.ARMS:
            rows = [row for row in arms if (row["backend"], row["registered_peers"], row["arm"]) == (backend, peers, arm)]
            exchanges = sorted({row["database_network_exchanges_per_completed"] for row in rows})
            require(exchanges == ([{"snapshot": 1, "row": 2, "cached_row": 1}[arm]] if backend == "postgres" else [0]),
                    "unexpected measured warm database exchange counts")
            measured.append({
                "backend": backend, "registered_peers": peers, "arm": arm,
                "active_peers": sorted({row["active_peers"] for row in rows}),
                "owner_workers": sorted({row["owner_workers"] for row in rows}),
                "network_exchanges_per_completed": exchanges,
                "loads_per_completed": sorted({row["database_loads_per_completed"] for row in rows}),
                "expects_per_completed": sorted({row["database_expects_per_completed"] for row in rows}),
                "peak_owner": max(row["overlap_owner_peak"] for row in rows),
                "peak_native": max(row["overlap_native_peak"] for row in rows),
                "peak_database_client_calls": max(row["overlap_database_client_call_peak"] for row in rows),
            })
    receipt["measured_counters_and_concurrency"] = measured
    helper.write_outputs(output, result, arms, ratios, cohorts, receipt)
    print(json.dumps({key: result[key] for key in (
        "report_count", "group_count", "arm_trial_rows", "paired_metric_rows", "cohort_rows",
        "total_completed_callbacks_across_all_arms_trials", "total_plaintext_bytes_across_all_arms_trials",
    )}, indent=2), flush=True)
    print(json.dumps({"output": str(output), "changed_source_files": changed,
                      "measured_counters_and_concurrency": measured}, indent=2), flush=True)


if __name__ == "__main__":
    main()
