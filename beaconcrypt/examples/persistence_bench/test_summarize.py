# SPDX-License-Identifier: 0BSD
"""Synthetic schema/validation tests only; these values are not performance results."""

import copy
import unittest

from summarize import markdown, matrix, summarize


def synthetic_report():
    config = {
        "peer_counts": [2],
        "trials": 3,
        "extra_registrations": 1,
        "active_peers": None,
        "small_bytes": 4,
        "small_messages": 2,
        "large_bytes": 8,
        "large_messages": 1,
        "mixed_messages": 4,
        "large_every": 2,
        "burst_chunk_bytes": 16,
        "burst_chunks": [2],
    }
    _, _, cases, expected = matrix(config)
    results = []
    for peers, trial, scenario, direction in sorted(expected):
        messages, plaintext = cases[scenario]
        for arm, factor in (("snapshot", 100), ("row", 50)):
            if arm == "snapshot":
                factor *= 2 ** (trial - 1)
            duration = messages * factor
            results.append(
                {
                    "arm": arm,
                    "peers": peers,
                    "trial": trial,
                    "scenario": scenario,
                    "direction": direction,
                    "active_peers": peers,
                    "touched_peers": min(peers, messages),
                    "consumed_registrations": 3,
                    "messages": messages,
                    "plaintext_bytes": plaintext,
                    "wire_bytes": plaintext + messages,
                    "server_batch_ns": duration,
                    "sum_operation_ns": messages * 5,
                    "operation_latencies_ns": [5] * messages,
                    "latency_ns": {
                        "min": 5,
                        "p50": 5,
                        "p95": 5,
                        "p99": 5,
                        "max": 5,
                        "mean": 5,
                    },
                    "operations_per_second": messages / (duration / 1e9),
                    "plaintext_mib_per_second": plaintext
                    / 1_048_576
                    / (duration / 1e9),
                    "outputs_verified": True,
                    "pair_order": int(arm == "row"),
                    "database": {
                        "reads": messages,
                        "writes": messages,
                        "transactions": messages,
                        "value_bytes_read": 0,
                        "value_bytes_written": 1,
                        "head_bytes_read": 0,
                    },
                }
            )
    return {
        "schema_version": 1,
        "status": "complete",
        "config": config,
        "results": results,
    }


class SummaryTests(unittest.TestCase):
    def test_complete_pairs_preserve_trials_and_ratios(self):
        result = summarize(synthetic_report())
        self.assertEqual(len(result["groups"]), 8)
        for group in result["groups"]:
            self.assertEqual(
                group["paired_batch_ratio"],
                {"count": 3, "median": 4, "min": 2, "max": 8},
            )
            self.assertEqual(len(group["trials"]), 3)
            self.assertEqual(group["trials"][0]["row"]["latency_ns"]["p99"], 5)

    def test_missing_single_arm_or_entire_pair_is_rejected(self):
        for count in (1, 2):
            report = synthetic_report()
            del report["results"][:count]
            with (
                self.subTest(count=count),
                self.assertRaisesRegex(ValueError, "missing"),
            ):
                summarize(report)

    def test_mismatched_axes_zero_duration_and_incomplete_run_are_rejected(self):
        for field, value in (
            ("active_peers", 1),
            ("touched_peers", 0),
            ("wire_bytes", 999),
            ("server_batch_ns", 0),
        ):
            report = synthetic_report()
            report["results"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                summarize(report)
        report = synthetic_report()
        report["status"] = "running"
        with self.assertRaisesRegex(ValueError, "not complete"):
            summarize(report)

    def test_duplicate_arm_and_inconsistent_tail_latency_are_rejected(self):
        report = synthetic_report()
        report["results"].append(copy.deepcopy(report["results"][0]))
        with self.assertRaisesRegex(ValueError, "duplicate"):
            summarize(report)
        report = synthetic_report()
        report["results"][0]["latency_ns"]["p99"] = 6
        with self.assertRaisesRegex(ValueError, "latency p99"):
            summarize(report)

    def test_three_arms_preserve_legacy_ratio_and_every_tail(self):
        report = synthetic_three_arm_report()
        result = summarize(report)
        self.assertEqual(result["backend"], "postgres")
        for group in result["groups"]:
            ratios = group["paired_batch_ratios"]
            self.assertEqual(ratios["snapshot_over_row"], group["paired_batch_ratio"])
            self.assertEqual(
                ratios["snapshot_over_cached_row"],
                {"count": 3, "median": 8, "min": 4, "max": 16},
            )
            self.assertEqual(
                ratios["row_over_cached_row"],
                {"count": 3, "median": 2, "min": 2, "max": 2},
            )
            for entry in group["trials"]:
                self.assertEqual(len(set(entry["arm_order"])), 3)
                self.assertEqual(entry["cached_row"]["latency_ns"]["p99"], 5)
        result.update(
            input_path="synthetic (not a measurement)", input_sha256="fixture"
        )
        rendered = markdown(result)
        self.assertIn("snapshot_over_cached_row", rendered)
        self.assertIn("TCP query exchanges", rendered)

    def test_three_arm_missing_cached_or_bad_order_backend_counter_is_rejected(self):
        report = synthetic_three_arm_report()
        report["results"] = [
            entry for entry in report["results"] if entry["arm"] != "cached_row"
        ]
        with self.assertRaisesRegex(ValueError, "missing paired arm"):
            summarize(report)
        for mutation in (
            lambda report: report.update(backend="sqlite"),
            lambda report: report["results"][0].update(pair_order=3),
            lambda report: report["results"][0]["database"].update(
                network_exchanges=-1
            ),
        ):
            report = synthetic_three_arm_report()
            mutation(report)
            with self.assertRaises(ValueError):
                summarize(report)

    def test_missing_fixture_reused_lineage_and_incomplete_warm_cache_are_rejected(
        self,
    ):
        for mutation in (
            lambda report: report["fixtures"].pop(),
            lambda report: report["fixtures"][1].update(
                lineage=report["fixtures"][0]["lineage"]
            ),
            lambda report: next(
                fixture
                for fixture in report["fixtures"]
                if fixture["arm"] == "cached_row"
            ).update(cached_peers_at_measurement_start=0),
        ):
            report = synthetic_three_arm_report()
            mutation(report)
            with self.assertRaises(ValueError):
                summarize(report)


def synthetic_three_arm_report():
    report = synthetic_report()
    report.update(
        schema_version=2, arms=["snapshot", "row", "cached_row"], backend="postgres"
    )
    report["config"]["backend"] = "postgres"
    added = []
    for entry in report["results"]:
        entry["database"].update(
            loads=0,
            expects=0,
            stores=0,
            network_exchanges=1,
            sql_calls=1,
            validation_bytes_sent=0,
            validation_rows=0,
            value_bytes_expected=0,
        )
        if entry["arm"] == "row":
            cached = copy.deepcopy(entry)
            cached.update(arm="cached_row", pair_order=2)
            cached["server_batch_ns"] //= 2
            cached["operations_per_second"] *= 2
            cached["plaintext_mib_per_second"] *= 2
            added.append(cached)
    report["results"].extend(added)
    report["fixtures"] = []
    for peer in report["config"]["peer_counts"]:
        for trial in range(1, report["config"]["trials"] + 1):
            for arm in report["arms"]:
                counts = {key: 0 for key in report["results"][0]["database"]}
                cached = peer if arm == "cached_row" else None
                report["fixtures"].append(
                    {
                        "arm": arm,
                        "peers": peer,
                        "trial": trial,
                        "lineage": [len(report["fixtures"]) + 1] * 32,
                        "cache_capacity": cached,
                        "cached_peers_at_measurement_start": cached,
                        "cold_open_database": counts.copy(),
                        "cache_fill_database": counts.copy(),
                        "warm_database": counts.copy(),
                    }
                )
    return report


if __name__ == "__main__":
    unittest.main()
