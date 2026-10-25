// SPDX-License-Identifier: 0BSD

use super::*;
use proptest::{prelude::*, test_runner::FileFailurePersistence};

fn config() -> ScheduleConfig {
	ScheduleConfig {
		peers: 3,
		interval_ns: 10,
		horizon_ns: 21,
		small_bytes: 4,
		large_bytes: 64,
		burst_bytes: 512,
		max_operations: 4096,
		max_plaintext_bytes: 1024 * 1024,
	}
}

#[test]
fn fixed_arrivals_are_staggered_and_stop_before_the_horizon() {
	let jobs = schedule(&config(), Workload::Small).unwrap();
	let actual: Vec<_> = jobs
		.iter()
		.map(|j| (j.peer, j.peer_sequence, j.scheduled_ns))
		.collect();
	assert_eq!(
		actual,
		[
			(0, 0, 0),
			(1, 0, 3),
			(2, 0, 6),
			(0, 1, 10),
			(1, 1, 13),
			(2, 1, 16),
			(0, 2, 20)
		]
	);
	assert_eq!(
		jobs.iter().map(|j| j.id).collect::<Vec<_>>(),
		(0..7).collect::<Vec<_>>()
	);
	assert_eq!(jobs[0].flow, Flow::Send);
	assert_eq!(jobs[3].flow, Flow::Receive);
	assert_eq!(jobs[6].flow, Flow::Send);
}

#[test]
fn burst_is_total_messages_and_preserves_round_robin_peer_fifo() {
	let jobs = schedule(&config(), Workload::Burst { messages: 7 }).unwrap();
	assert_eq!(jobs.len(), 7);
	for (id, job) in jobs.iter().enumerate() {
		assert_eq!((job.id, job.peer, job.peer_sequence), (id, id % 3, id / 3));
		assert_eq!(job.scheduled_ns, 0);
		assert_eq!(job.payload, PayloadClass::Burst);
		assert_eq!(job.plaintext_bytes, 512);
	}
	assert_eq!(
		peer_period_phase(&config(), &Workload::Burst { messages: 7 }, 1),
		Ok((0, 0))
	);
}

#[test]
fn regular_large_messages_cover_both_directions() {
	let mut configuration = config();
	configuration.peers = 1;
	configuration.horizon_ns = 80;
	let jobs = schedule(&configuration, Workload::Mixed { large_every: 2 }).unwrap();
	let large: Vec<_> = jobs
		.iter()
		.filter(|j| j.payload == PayloadClass::Large)
		.map(|j| (j.peer_sequence, j.flow, j.plaintext_bytes))
		.collect();
	assert_eq!(
		large,
		[
			(2, Flow::Send, 64),
			(3, Flow::Receive, 64),
			(6, Flow::Send, 64),
			(7, Flow::Receive, 64)
		]
	);
}

#[test]
fn regular_large_profile_retains_every_large_duplex_arrival() {
	let mut configuration = config();
	configuration.peers = 1;
	configuration.interval_ns = 1_000_000_000;
	configuration.horizon_ns = 2_000_000_001;
	configuration.large_bytes = 65_536;
	let jobs = schedule(&configuration, Workload::Large).unwrap();
	assert_eq!(
		jobs.iter().map(|job| job.scheduled_ns).collect::<Vec<_>>(),
		[0, 1_000_000_000, 2_000_000_000]
	);
	assert_eq!(
		jobs.iter().map(|job| job.flow).collect::<Vec<_>>(),
		[Flow::Send, Flow::Receive, Flow::Send]
	);
	assert!(
		jobs.iter()
			.all(|job| job.payload == PayloadClass::Large && job.plaintext_bytes == 65_536)
	);
}

#[test]
fn heterogeneous_cohorts_do_not_alias_eight_worker_lanes() {
	let mut configuration = config();
	configuration.peers = 32;
	configuration.horizon_ns = 100;
	let workload = Workload::Heterogeneous {
		periods_ns: vec![1000, 100, 10, 5],
		large_every: 16,
	};
	for lane in 0..8 {
		let periods: Vec<_> = (lane..32)
			.step_by(8)
			.map(|peer| {
				peer_period_phase(&configuration, &workload, peer)
					.unwrap()
					.0
			})
			.collect();
		assert_eq!(periods, [1000, 100, 10, 5]);
	}
	assert_eq!(
		peer_period_phase(&configuration, &workload, 7),
		Ok((1000, 875))
	);
	assert_eq!(
		peer_period_phase(&configuration, &workload, 15),
		Ok((100, 87))
	);
	assert_eq!(peer_period_phase(&configuration, &workload, 31), Ok((5, 4)));
}

#[test]
fn uneven_cohorts_and_subnanosecond_phase_quantization_remain_ordered() {
	let mut configuration = config();
	configuration.peers = 5;
	configuration.horizon_ns = 10;
	let workload = Workload::Heterogeneous {
		periods_ns: vec![4, 2],
		large_every: 1,
	};
	let periods: Vec<_> = (0..5)
		.map(|p| peer_period_phase(&configuration, &workload, p).unwrap())
		.collect();
	assert_eq!(periods, [(4, 0), (4, 1), (4, 2), (2, 0), (2, 1)]);
	let jobs = schedule(&configuration, workload).unwrap();
	assert!(
		jobs.windows(2)
			.all(|w| (w[0].scheduled_ns, w[0].peer) <= (w[1].scheduled_ns, w[1].peer))
	);
	configuration.interval_ns = 1;
	configuration.horizon_ns = 1;
	let simultaneous = schedule(&configuration, Workload::Small).unwrap();
	assert_eq!(simultaneous.len(), 5);
	assert!(simultaneous.iter().all(|j| j.scheduled_ns == 0));
}

#[test]
fn byte_and_operation_limits_are_exact_and_checked_before_large_allocations() {
	let mut configuration = config();
	configuration.max_operations = 7;
	configuration.max_plaintext_bytes = 7 * 512;
	assert_eq!(
		schedule(&configuration, Workload::Burst { messages: 7 })
			.unwrap()
			.len(),
		7
	);
	configuration.max_plaintext_bytes -= 1;
	assert!(
		schedule(&configuration, Workload::Burst { messages: 7 })
			.unwrap_err()
			.contains("byte limit")
	);
	configuration.max_plaintext_bytes = u64::MAX;
	assert!(
		schedule(&configuration, Workload::Burst { messages: 8 })
			.unwrap_err()
			.contains("operation limit")
	);
	configuration.horizon_ns = u64::MAX;
	configuration.interval_ns = 1;
	assert!(
		schedule(&configuration, Workload::Small)
			.unwrap_err()
			.contains("operation limit")
	);
	configuration.peers = usize::MAX;
	assert!(
		schedule(&configuration, Workload::Small)
			.unwrap_err()
			.contains("peer count")
	);
}

#[test]
fn invalid_configuration_and_peer_queries_fail_explicitly() {
	let mut configuration = config();
	configuration.peers = 0;
	assert!(schedule(&configuration, Workload::Small).is_err());
	configuration = config();
	configuration.interval_ns = 0;
	assert!(schedule(&configuration, Workload::Burst { messages: 7 }).is_err());
	for workload in [
		Workload::Mixed { large_every: 0 },
		Workload::Burst { messages: 0 },
		Workload::Heterogeneous {
			periods_ns: vec![],
			large_every: 1,
		},
		Workload::Heterogeneous {
			periods_ns: vec![1, 0],
			large_every: 1,
		},
	] {
		assert!(schedule(&config(), workload).is_err());
	}
	assert!(peer_period_phase(&config(), &Workload::Small, 3).is_err());
	configuration = config();
	configuration.peers = 1;
	let sparse = Workload::Heterogeneous {
		periods_ns: vec![1000, 100, 10, 5],
		large_every: 16,
	};
	assert_eq!(peer_period_phase(&configuration, &sparse, 0), Ok((1000, 0)));
	assert_eq!(schedule(&configuration, sparse).unwrap().len(), 1);
}

fn sample_job(at: u64) -> Scheduled {
	Scheduled {
		id: 0,
		peer: 0,
		peer_sequence: 0,
		scheduled_ns: at,
		payload: PayloadClass::Small,
		flow: Flow::Send,
		plaintext_bytes: 4,
	}
}

fn from_points(points: [u64; 7]) -> (Scheduled, CompletedTiming) {
	(
		sample_job(points[0]),
		CompletedTiming {
			enqueue_attempt_ns: points[1],
			enqueued_ns: points[2],
			owner_start_ns: points[3],
			native_start_ns: points[4],
			native_end_ns: points[5],
			completed_ns: points[6],
		},
	)
}

#[test]
fn delayed_feeder_and_backpressure_remain_in_response_latency() {
	let (job, timing) = from_points([10, 110, 210, 310, 410, 411, 412]);
	let result = timings(&job, &timing, 400).unwrap();
	assert_eq!(result.scheduler_lag_ns, 100);
	assert_eq!(result.enqueue_backpressure_ns, 100);
	assert_eq!(result.queue_wait_ns, 100);
	assert_eq!(result.owner_wait_ns, 100);
	assert_eq!(result.service_ns, 1);
	assert_eq!(result.completion_overhead_ns, 1);
	assert_eq!(result.response_ns, 402);
	assert_eq!(result.deadline_lag_ns, 2);
	assert!(!result.deadline_met);
	assert!(timings(&job, &timing, 402).unwrap().deadline_met);
}

#[test]
fn each_inverted_stage_is_rejected_and_equal_boundaries_are_valid() {
	for index in 0..6 {
		let mut points = [0, 10, 20, 30, 40, 50, 60];
		points.swap(index, index + 1);
		let (job, timing) = from_points(points);
		assert!(timings(&job, &timing, 100).is_err(), "stage {index}");
	}
	let (job, timing) = from_points([u64::MAX; 7]);
	let result = timings(&job, &timing, 0).unwrap();
	assert_eq!(result.response_ns, 0);
	assert!(result.deadline_met);
	let (job, timing) = from_points([
		u64::MAX - 6,
		u64::MAX - 5,
		u64::MAX - 4,
		u64::MAX - 3,
		u64::MAX - 2,
		u64::MAX - 1,
		u64::MAX,
	]);
	assert_eq!(timings(&job, &timing, 5).unwrap().deadline_lag_ns, 1);
}

fn property_config() -> ProptestConfig {
	ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok()
			.and_then(|v| v.parse().ok())
			.unwrap_or(64),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/proptest-regressions/concurrency_schedule.txt"
		)))),
		..ProptestConfig::default()
	}
}

proptest! {
	#![proptest_config(property_config())]
	#[test]
	fn generated_periodic_arrivals_have_no_loss_duplication_or_completion_dependency(peers in 1usize..9, period in 1u64..21, horizon in 1u64..101, cadence in 1usize..9) {
		let mut configuration = config();
		configuration.peers = peers;
		configuration.interval_ns = period;
		configuration.horizon_ns = horizon;
		let jobs = schedule(&configuration, Workload::Mixed { large_every: cadence }).unwrap();
		let mut expected = Vec::new();
		for at in 0..horizon {
			for peer in 0..peers {
				let phase = peer as u64 * period / peers as u64;
				if at >= phase && (at - phase).is_multiple_of(period) {
					expected.push((at, peer, ((at - phase) / period) as usize));
				}
			}
		}
		prop_assert_eq!(jobs.iter().map(|j| (j.scheduled_ns,j.peer,j.peer_sequence)).collect::<Vec<_>>(), expected);
		for (id, job) in jobs.iter().enumerate() { prop_assert_eq!(job.id,id); }
		let exact_bytes: u64 = jobs.iter().map(|j| j.plaintext_bytes as u64).sum();
		configuration.max_plaintext_bytes = exact_bytes;
		prop_assert_eq!(schedule(&configuration, Workload::Mixed { large_every: cadence }).unwrap(), jobs);
		configuration.max_plaintext_bytes -= 1;
		let rejected = schedule(&configuration, Workload::Mixed { large_every: cadence });
		prop_assert!(rejected.is_err());
	}

	#[test]
	fn generated_stage_delays_conserve_end_to_end_latency(at in 0u64..1_000_000, delays in prop::array::uniform6(0u64..1_000_000), budget in 0u64..6_000_000) {
		let mut points = [at; 7];
		for (index, delay) in delays.iter().enumerate() { points[index+1] = points[index] + delay; }
		let (job, timing) = from_points(points);
		let metrics = timings(&job,&timing,budget).unwrap();
		let expected: u64 = delays.iter().sum();
		prop_assert_eq!([metrics.scheduler_lag_ns,metrics.enqueue_backpressure_ns,metrics.queue_wait_ns,metrics.owner_wait_ns,metrics.service_ns,metrics.completion_overhead_ns],delays);
		prop_assert_eq!(metrics.response_ns, expected);
		prop_assert_eq!(metrics.deadline_met,expected<=budget);
		prop_assert_eq!(metrics.deadline_lag_ns,expected.saturating_sub(budget));
	}
}
