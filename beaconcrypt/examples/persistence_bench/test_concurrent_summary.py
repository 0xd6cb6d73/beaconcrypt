"""Synthetic concurrent accounting cases; no measurements or native calls."""

import copy
import unittest

from summarize import (
    CONCURRENT_ARMS,
    POINTS,
    STAGES,
    concurrent_overlap,
    concurrent_scenarios,
    concurrent_schedule,
    markdown,
    summarize,
)


def counters(backend, arm, count):
    value = dict.fromkeys(
        (
            "reads",
            "writes",
            "transactions",
            "loads",
            "expects",
            "stores",
            "network_exchanges",
            "sql_calls",
            "validation_rows",
            "value_bytes_read",
            "value_bytes_written",
            "head_bytes_read",
            "validation_bytes_sent",
            "value_bytes_expected",
        ),
        0,
    )
    value.update(writes=count, transactions=count, value_bytes_written=count * 200)
    if arm == "snapshot":
        if backend == "sqlite":
            value.update(reads=count, sql_calls=count * 4, head_bytes_read=count * 72)
        else:
            value.update(
                sql_calls=count,
                network_exchanges=count,
                validation_rows=count,
                validation_bytes_sent=count * 72,
            )
    else:
        cached = arm == "cached_row"
        value.update(
            stores=count, validation_rows=count, validation_bytes_sent=count * 180
        )
        value["expects" if cached else "loads"] = count
        value["value_bytes_expected" if cached else "value_bytes_read"] = count * 180
        value["reads"] = 0 if cached else count
        value["sql_calls"] = count * (
            (1 if cached else 2) if backend == "postgres" else (4 if cached else 5)
        )
        value["network_exchanges"] = (
            count * (1 if cached else 2) if backend == "postgres" else 0
        )
    return value


def report(backend="sqlite"):
    config = {
        "backend": backend,
        "peer_counts": [2],
        "trials": 3,
        "active_peers": 2,
        "small_bytes": 4,
        "large_bytes": 16,
        "burst_chunk_bytes": 32,
        "large_every": 2,
        "burst_chunks": [5],
    }
    concurrent = {
        "workers": 2,
        "period_ms": [1],
        "arrival_ms": 4,
        "queue_capacity": 8,
        "queue_bytes": 256,
        "deadline_ms": 1,
        "drain_ms": 100,
        "max_offered": 32,
        "max_precomputed_bytes": 1_000_000,
    }
    result = {
        "schema_version": 3,
        "status": "complete",
        "backend": backend,
        "arms": list(CONCURRENT_ARMS),
        "config": config,
        "concurrency": concurrent,
        "fixtures": [],
        "results": [],
    }
    for trial in range(1, 4):
        for order, arm in enumerate(CONCURRENT_ARMS):
            result["fixtures"].append(
                {
                    "peers": 2,
                    "trial": trial,
                    "arm": arm,
                    "lineage": [trial * 3 + order] * 32,
                }
            )
            for scenario in concurrent_scenarios(config, concurrent):
                jobs, phases, horizon, lanes = concurrent_schedule(
                    config, concurrent, 2, scenario
                )
                owners = 1 if arm == "snapshot" else lanes
                owner_end = [0] * owners
                span_lists = [[] for _ in range(owners)]
                observations = []
                service = {
                    "snapshot": 3_000_000,
                    "row": 2_000_000,
                    "cached_row": 1_000_000,
                }[arm] * trial
                for job in jobs:
                    owner = 0 if owners == 1 else job["peer"] % lanes
                    attempt = job["scheduled_ns"] + 3
                    enqueued = attempt + 5
                    owner_start = max(enqueued + 5, owner_end[owner])
                    native_start = owner_start + 7
                    native_end = native_start + service
                    completed = native_end + 3
                    points = [
                        job["scheduled_ns"],
                        attempt,
                        enqueued,
                        owner_start,
                        native_start,
                        native_end,
                        completed,
                    ]
                    timing = dict(zip(POINTS, points[1:]))
                    metrics = dict(
                        zip(STAGES, (b - a for a, b in zip(points, points[1:])))
                    )
                    response = completed - job["scheduled_ns"]
                    metrics.update(
                        response_ns=response,
                        deadline_lag_ns=max(0, response - 1_000_000),
                        deadline_met=response <= 1_000_000,
                    )
                    observations.append(
                        {
                            "id": job["id"],
                            "peer": job["peer"],
                            "lane": job["peer"] % lanes,
                            "worker": owner,
                            "timing": timing,
                            "metrics": metrics,
                            "outcome": "completed",
                            "attempts": 1,
                            "retries": 0,
                            "conflicts": 0,
                        }
                    )
                    if arm == "row":
                        span_lists[owner].append(
                            {
                                "kind": "row_load",
                                "start_ns": native_start + 1,
                                "end_ns": native_start + service // 4,
                            }
                        )
                    span_lists[owner].append(
                        {
                            "kind": (
                                "snapshot_commit" if arm == "snapshot" else "row_commit"
                            ),
                            "start_ns": native_start + service * 3 // 4,
                            "end_ns": native_end - 1,
                        }
                    )
                    owner_end[owner] = completed
                duration = max(owner_end)
                workers = []
                for owner in range(owners):
                    peers = list(range(2)) if owners == 1 else [owner]
                    count = sum(value["worker"] == owner for value in observations)
                    cached = len(peers) if arm == "cached_row" else None
                    workers.append(
                        {
                            "worker": owner,
                            "peers": peers,
                            "cached_peers": cached,
                            "cache_capacity": cached,
                            "database": counters(backend, arm, count),
                            "cold_open_database": counters(backend, arm, 0),
                            "warm_database": counters(backend, arm, 0),
                            "db_spans": span_lists[owner],
                        }
                    )
                raw = {
                    "arm": arm,
                    "trial": trial,
                    "pair_order": order,
                    "peers": 2,
                    "active_peers": 2,
                    "touched_peers": len({job["peer"] for job in jobs}),
                    "scenario": scenario,
                    "direction": "duplex",
                    "offered": len(jobs),
                    "messages": len(jobs),
                    "plaintext_bytes": sum(job["plaintext_bytes"] for job in jobs),
                    "wire_bytes": sum(job["plaintext_bytes"] + 100 for job in jobs),
                    "planned_horizon_ns": horizon,
                    "deadline_budget_ns": 1_000_000,
                    "drain_budget_ns": 100_000_000,
                    "scheduled": jobs,
                    "peer_schedule": phases,
                    "observations": observations,
                    "failures": [],
                    "workers": workers,
                    "logical_feeder_lanes": lanes,
                    "owner_workers": owners,
                    "server_batch_ns": duration,
                    "outputs_verified": True,
                    "status": "complete",
                }
                raw["lane_load"] = [
                    {
                        "lane": lane,
                        "offered": sum(job["peer"] % lanes == lane for job in jobs),
                        "plaintext_bytes": sum(
                            job["plaintext_bytes"]
                            for job in jobs
                            if job["peer"] % lanes == lane
                        ),
                    }
                    for lane in range(lanes)
                ]
                raw["queues"] = [
                    {
                        "capacity": 8 // owners,
                        "byte_capacity": 256 // owners,
                        "high_water_jobs": min(len(jobs), 8 // owners),
                        "high_water_bytes": min(
                            sum(job["plaintext_bytes"] for job in jobs), 256 // owners
                        ),
                    }
                    for _ in range(owners)
                ]
                raw["operations_per_second"] = len(jobs) / (duration / 1e9)
                raw["plaintext_mib_per_second"] = (
                    raw["plaintext_bytes"] / 1_048_576 / (duration / 1e9)
                )
                raw["overlap"] = {
                    "owner": concurrent_overlap(
                        [
                            (
                                value["timing"]["owner_start_ns"],
                                value["timing"]["completed_ns"],
                            )
                            for value in observations
                        ]
                    ),
                    "native": concurrent_overlap(
                        [
                            (
                                value["timing"]["native_start_ns"],
                                value["timing"]["native_end_ns"],
                            )
                            for value in observations
                        ]
                    ),
                    "database_client_call": concurrent_overlap(
                        [
                            (span["start_ns"], span["end_ns"])
                            for spans in span_lists
                            for span in spans
                        ]
                    ),
                }
                result["results"].append(raw)
    return result


class ConcurrentSummaryTests(unittest.TestCase):
    def test_complete_matrix_preserves_trials_deadlines_and_actual_overlap(self):
        for backend in ("sqlite", "postgres"):
            summary = summarize(report(backend))
            self.assertEqual(len(summary["groups"]), 5)
            for group in summary["groups"]:
                self.assertEqual(len(group["trials"]), 3)
                for trial in group["trials"]:
                    self.assertEqual(trial["snapshot"]["overlap"]["native"]["peak"], 1)
                    self.assertEqual(
                        trial["row"]["overlap"]["native"]["peak"],
                        1 if group["scenario"] == "regular_large" else 2,
                    )
                    for arm in CONCURRENT_ARMS:
                        value = trial[arm]
                        self.assertEqual(
                            value["offered"],
                            value["deadline_met"] + value["deadline_missed"],
                        )
                        self.assertEqual(
                            value["callback_latency_ns"]["response_ns"]["count"],
                            group["offered"],
                        )
                        self.assertEqual(
                            sum(flow["offered"] for flow in value["by_flow"].values()),
                            group["offered"],
                        )
            rendered = markdown(summary)
            self.assertIn("Deadline met/offered", rendered)
            self.assertIn(
                "Per-trial operation distributions are never pooled", rendered
            )

    def test_missing_duplicated_or_retried_callbacks_and_missing_arm_fail(self):
        mutations = [
            lambda r: r["results"][0]["observations"].pop(),
            lambda r: r["results"][0]["observations"].__setitem__(
                1, copy.deepcopy(r["results"][0]["observations"][0])
            ),
            lambda r: r["results"][0]["observations"][0].update(retries=1),
            lambda r: r["results"].pop(),
            lambda r: r["results"][0].update(
                failures=[{"id": 0, "outcome": "cancelled"}]
            ),
        ]
        for mutate in mutations:
            with self.subTest(mutation=mutate):
                value = report()
                mutate(value)
                with self.assertRaises(ValueError):
                    summarize(value)

    def test_queue_delay_cannot_be_omitted_or_relabelled_as_service_latency(self):
        for field, change in (
            ("response_ns", -1),
            ("queue_wait_ns", 1),
            ("deadline_lag_ns", 1),
        ):
            value = report()
            observation = value["results"][0]["observations"][-1]
            observation["metrics"][field] += change
            with (
                self.subTest(field=field),
                self.assertRaisesRegex(ValueError, "decomposition"),
            ):
                summarize(value)
        value = report()
        value["results"][0]["scheduled"][0]["scheduled_ns"] = 3
        with self.assertRaisesRegex(ValueError, "offered workload"):
            summarize(value)

    def test_owner_fifo_queue_bounds_and_database_span_provenance_are_checked(self):
        for mutate in (
            lambda r: r["results"][0]["queues"][0].update(high_water_jobs=100),
            lambda r: r["results"][0]["queues"][0].update(high_water_bytes=10000),
            lambda r: r["results"][0]["observations"][0].update(worker=1),
            lambda r: r["results"][0]["workers"][0]["db_spans"][0].update(start_ns=0),
            lambda r: r["results"][0]["workers"][0]["db_spans"].pop(),
            lambda r: r["results"][0]["overlap"]["native"].update(peak=2),
        ):
            value = report()
            mutate(value)
            with self.subTest(mutation=mutate), self.assertRaises(ValueError):
                summarize(value)

    def test_last_completed_call_crossing_hard_drain_limit_invalidates_run(self):
        value = report()
        value["concurrency"]["drain_ms"] = 1
        for result in value["results"]:
            result["drain_budget_ns"] = 1_000_000
        with self.assertRaisesRegex(ValueError, "drain bound"):
            summarize(value)

    def test_snapshot_is_serial_and_cached_postgres_saves_one_fetch_exchange(self):
        value = report("postgres")
        row = next(result for result in value["results"] if result["arm"] == "row")
        cached = next(
            result for result in value["results"] if result["arm"] == "cached_row"
        )
        self.assertEqual(
            sum(worker["database"]["network_exchanges"] for worker in row["workers"]),
            row["offered"] * 2,
        )
        self.assertEqual(
            sum(
                worker["database"]["network_exchanges"] for worker in cached["workers"]
            ),
            cached["offered"],
        )
        cached["workers"][0]["database"]["loads"] = 1
        with self.assertRaisesRegex(ValueError, "loads"):
            summarize(value)

    def test_half_open_touching_intervals_never_invent_concurrency(self):
        self.assertEqual(
            concurrent_overlap([(0, 5), (5, 10), (4, 4)]),
            {
                "peak": 1,
                "any_active_ns": 10,
                "multiple_active_ns": 0,
                "sum_active_ns": 10,
            },
        )
        self.assertEqual(
            concurrent_overlap([(0, 7), (4, 10)]),
            {
                "peak": 2,
                "any_active_ns": 10,
                "multiple_active_ns": 3,
                "sum_active_ns": 13,
            },
        )

    def test_heterogeneous_blocks_balance_default_lanes_and_large_payload_flows(self):
        base = report()
        config = base["config"]
        settings = base["concurrency"]
        config.update(active_peers=32)
        settings.update(
            workers=8,
            period_ms=[1000, 100, 10, 5],
            max_offered=1000,
            arrival_ms=25,
            max_precomputed_bytes=10_000_000,
        )
        jobs, phases, _, _ = concurrent_schedule(
            config, settings, 32, "heterogeneous_mixed"
        )
        for lane in range(8):
            self.assertEqual(
                [row["period_ns"] for row in phases if row["lane"] == lane],
                [1_000_000_000, 100_000_000, 10_000_000, 5_000_000],
            )
        self.assertEqual(
            {job["flow"] for job in jobs if job["payload"] == "large"},
            {"send", "receive"},
        )


if __name__ == "__main__":
    unittest.main()
