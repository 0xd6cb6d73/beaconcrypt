# SPDX-License-Identifier: 0BSD
"""Synthetic schema/validation tests only; these values are not performance results."""

import copy
import unittest

from summarize import matrix, summarize


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


if __name__ == "__main__":
    unittest.main()
