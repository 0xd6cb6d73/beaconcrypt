"""Synthetic guard tests: no processes, leases, databases, or benchmarks are started."""

import copy
from pathlib import Path
import unittest
from unittest.mock import patch

import hybrid_guard as guard


class GuardTests(unittest.TestCase):
    def test_process_scan_includes_unknown_name_cpu_counters(self):
        fields = ["0"] * 24
        fields[0], fields[1], fields[11], fields[12], fields[19] = (
            "S",
            "1",
            "120",
            "30",
            "9000",
        )
        contents = {
            "stat": "111 (python3) " + " ".join(fields),
            "comm": "python3\n",
            "cgroup": "0::/user.slice/background.scope\n",
        }
        with (
            patch.object(Path, "iterdir", return_value=iter([Path("/proc/111")])),
            patch.object(Path, "read_text", lambda path: contents[path.name]),
            patch.object(guard.os, "readlink", return_value="/usr/bin/python3"),
        ):
            observed = guard.processes()
        self.assertEqual(observed[111]["comm"], "python3")
        self.assertEqual(observed[111]["cpu_ticks"], 150)
        self.assertEqual(observed[111]["start_ticks"], 9000)

    def test_new_memory_or_lean_ticket_and_monitor_gap_invalidate(self):
        initial = {
            "checks": {"base": True},
            "memory_ticket_sequence": "10",
            "lean_ticket_sequence": "20",
            "monotonic_seconds": 100,
            "cpu_clock_ticks_per_second": 100,
            "uptime_seconds": 100,
            "process_cpu": [],
            "system_steal_ticks": 0,
            "swap_in_pages": 0,
            "swap_out_pages": 0,
        }
        for changes in (
            {"memory_ticket_sequence": "11"},
            {"lean_ticket_sequence": "21"},
            {"monotonic_seconds": 111},
        ):
            current = {**copy.deepcopy(initial), "monotonic_seconds": 105, **changes}
            self.assertFalse(guard.compare_sample(current, initial, 10)["quiet"])
        self.assertTrue(
            guard.compare_sample(
                {**copy.deepcopy(initial), "monotonic_seconds": 105}, initial, 10
            )["quiet"]
        )

    @staticmethod
    def tcp_line(inode, local, remote, state="01"):
        return f" 0: 0100007F:{local:04X} 0100007F:{remote:04X} {state} 00000000:00000000 00:00000000 00000000 1000 0 {inode} 1\n"

    def test_tcp_client_fds_distinguish_foreign_connection_on_owned_server(self):
        table = (
            "header\n"
            + self.tcp_line(1001, 41000, 55439)
            + self.tcp_line(1002, 41001, 55439)
            + self.tcp_line(2000, 55439, 0, "0A")
        )

        def read(path, *args, **kwargs):
            return table if path.name == "tcp" else "header\n"

        with (
            patch.object(Path, "read_text", read),
            patch.object(
                guard,
                "socket_inodes",
                side_effect=lambda pid: {1001} if pid == 20 else {2000},
            ),
        ):
            sockets = guard.postgres_sockets({"pid": 10, "port": 55439}, 20)
        self.assertTrue(sockets["owned_listener"])
        self.assertEqual(
            [item["inode"] for item in sockets["foreign_client_sockets"]], [1002]
        )

    def test_closed_socket_between_snapshots_does_not_create_false_foreign_client(self):
        before = (
            "header\n"
            + self.tcp_line(1001, 41000, 55439)
            + self.tcp_line(2000, 55439, 0, "0A")
        )
        after = "header\n" + self.tcp_line(2000, 55439, 0, "0A")
        reads = iter([before, "header\n", after, "header\n"])
        with (
            patch.object(Path, "read_text", lambda *_: next(reads)),
            patch.object(
                guard,
                "socket_inodes",
                side_effect=lambda pid: set() if pid == 20 else {2000},
            ),
        ):
            sockets = guard.postgres_sockets({"pid": 10, "port": 55439}, 20)
        self.assertEqual(sockets["foreign_client_sockets"], [])
        self.assertTrue(sockets["owned_listener"])

    def test_scope_match_is_exact_suffix(self):
        self.assertTrue(
            guard.same_scope({"cgroup": "0::/user.slice/owned.scope\n"}, "owned.scope")
        )
        self.assertFalse(
            guard.same_scope(
                {"cgroup": "0::/user.slice/not-owned.scope\n"}, "owned.scope"
            )
        )

    @staticmethod
    def cpu_pair(before, after, **changes):
        previous = {
            "process_cpu": before,
            "cpu_clock_ticks_per_second": 100,
            "uptime_seconds": 100,
            "system_steal_ticks": 0,
            "swap_in_pages": 0,
            "swap_out_pages": 0,
        }
        sample = {
            **previous,
            "process_cpu": after,
            "checks": {},
            "gap_seconds": 5,
            **changes,
        }
        guard.cpu_usage(sample, previous, guard.CPU_LIMITS)
        return sample

    @staticmethod
    def process(pid, ticks, exempt=False, start=9000):
        return {
            "pid": pid,
            "comm": "python3",
            "start_ticks": start,
            "cpu_ticks": ticks,
            "exempt": exempt,
            "state": "S",
        }

    def test_unknown_process_at_quarter_core_is_rejected(self):
        sample = self.cpu_pair([self.process(1, 1000)], [self.process(1, 1125)])
        self.assertEqual(sample["cpu_usage"]["outside_max_process_cores"], 0.25)
        self.assertFalse(sample["checks"]["outside_per_process_cpu_below_limit"])

    def test_aggregate_unknown_cpu_and_exact_identity_exemption(self):
        before = [self.process(pid, 0) for pid in (1, 2, 3)]
        after = [self.process(pid, 100) for pid in (1, 2, 3)]
        sample = self.cpu_pair(before, after)
        self.assertTrue(sample["checks"]["outside_per_process_cpu_below_limit"])
        self.assertFalse(sample["checks"]["outside_aggregate_cpu_below_limit"])
        sample = self.cpu_pair(
            [self.process(1, 0, True)], [self.process(1, 1500, True)]
        )
        self.assertEqual(sample["cpu_usage"]["outside_aggregate_cores"], 0)
        self.assertTrue(all(sample["checks"].values()))

    def test_reused_pid_new_process_is_counted_from_zero(self):
        sample = self.cpu_pair(
            [self.process(1, 100000, start=100)], [self.process(1, 125, start=10050)]
        )
        self.assertTrue(sample["checks"]["cpu_counter_continuity"])
        self.assertEqual(sample["cpu_usage"]["outside_max_process_cores"], 0.25)
        self.assertFalse(sample["checks"]["outside_per_process_cpu_below_limit"])

    def test_steal_is_recorded_swap_is_gated_and_short_boundary_interval(self):
        sample = self.cpu_pair([], [], system_steal_ticks=1250)
        self.assertTrue(all(sample["checks"].values()))
        self.assertNotIn("system_steal_below_limit", sample["checks"])
        self.assertEqual(sample["cpu_usage"]["system_steal_cores"], 2.5)
        self.assertEqual(sample["cpu_usage"]["system_steal_policy"], "record_only")
        self.assertFalse(
            self.cpu_pair([], [], swap_in_pages=1280)["checks"][
                "system_swap_below_limit"
            ]
        )
        sample = self.cpu_pair(
            [self.process(1, 0)], [self.process(1, 20)], gap_seconds=0.2
        )
        self.assertFalse(sample["cpu_usage"]["enforced"])
        self.assertTrue(all(sample["checks"].values()))

    def test_negative_counter_delta_is_not_accepted(self):
        sample = self.cpu_pair([self.process(1, 100)], [self.process(1, 99)])
        self.assertFalse(sample["checks"]["cpu_counter_continuity"])

    def test_previous_identity_exemption_only_survives_for_a_zombie(self):
        before = self.process(1, 0, True)
        after = self.process(1, 500, False)
        self.assertFalse(
            self.cpu_pair([before], [after])["checks"][
                "outside_per_process_cpu_below_limit"
            ]
        )
        after["state"] = "Z"
        self.assertTrue(all(self.cpu_pair([before], [after])["checks"].values()))

    def test_missing_older_baseline_is_rejected(self):
        sample = self.cpu_pair([], [self.process(1, 10000, start=1)])
        self.assertFalse(sample["checks"]["cpu_baselines_complete"])

    def test_short_boundary_uses_older_cpu_anchor(self):
        base = {
            "checks": {},
            "cpu_clock_ticks_per_second": 100,
            "uptime_seconds": 100,
            "monotonic_seconds": 100,
            "memory_ticket_sequence": "1",
            "lean_ticket_sequence": "1",
            "system_steal_ticks": 0,
            "swap_in_pages": 0,
            "swap_out_pages": 0,
            "process_cpu": [self.process(1, 0)],
        }
        previous = {
            **base,
            "monotonic_seconds": 105,
            "process_cpu": [self.process(1, 125)],
        }
        current = {
            **base,
            "checks": {},
            "monotonic_seconds": 105.1,
            "process_cpu": [self.process(1, 128)],
        }
        guard.compare_sample(current, previous, 10, cpu_previous=base)
        self.assertTrue(current["cpu_usage"]["enforced"])
        self.assertAlmostEqual(current["cpu_usage"]["interval_seconds"], 5.1)
        self.assertFalse(current["checks"]["outside_per_process_cpu_below_limit"])

    def test_instrumentation_requires_all_four_exact_identity_fields(self):
        identity = {
            "pid": 1426259,
            "start_ticks": 120432725,
            "executable": "/nix/store/exact-controller/bin/.codex-wrapped",
            "cgroup": "0::/user.slice/session-111.scope",
        }
        actual = {**identity, "state": "S"}
        self.assertTrue(guard.matches_instrumentation(actual, identity))
        for changes in (
            {"pid": 1426260, "ppid": 1426259},
            {"start_ticks": 120432726},
            {"executable": "/nix/store/other-controller/bin/.codex-wrapped"},
            {"cgroup": "0::/user.slice/session-112.scope"},
            {"state": "Z"},
        ):
            with self.subTest(changes=changes):
                self.assertFalse(
                    guard.matches_instrumentation({**actual, **changes}, identity)
                )

    def test_controller_cpu_is_recorded_separately_on_the_same_interval(self):
        before = {
            **self.process(1426259, 100, True),
            "exemption_role": "instrumentation",
        }
        after = {**before, "cpu_ticks": 250}
        sample = self.cpu_pair([before], [after])
        self.assertTrue(all(sample["checks"].values()))
        self.assertEqual(sample["cpu_usage"]["outside_aggregate_cores"], 0)
        self.assertEqual(sample["cpu_usage"]["instrumentation_aggregate_cores"], 0.3)
        self.assertEqual(
            sample["cpu_usage"]["instrumentation_processes"][0]["cpu_ticks"], 150
        )
        self.assertEqual(sample["cpu_usage"]["interval_seconds"], 5)

    def test_controller_accounting_remains_fail_closed(self):
        before = {
            **self.process(1426259, 100, True),
            "exemption_role": "instrumentation",
        }
        after = {**before, "cpu_ticks": 99}
        self.assertFalse(
            self.cpu_pair([before], [after])["checks"]["cpu_counter_continuity"]
        )
        self.assertFalse(
            self.cpu_pair([], [before])["checks"]["cpu_baselines_complete"]
        )


if __name__ == "__main__":
    unittest.main()
