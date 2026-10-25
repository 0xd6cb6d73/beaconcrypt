// SPDX-License-Identifier: 0BSD

use super::*;
use std::sync::Barrier;

fn job(id: usize, peer: usize, bytes: usize) -> Scheduled {
	Scheduled {
		id,
		peer,
		peer_sequence: id,
		scheduled_ns: 0,
		payload: PayloadClass::Small,
		flow: Flow::Send,
		plaintext_bytes: bytes,
	}
}

#[test]
fn byte_limit_blocks_admission_until_the_old_job_leaves() {
	for (slots, byte_limit, first_bytes, second_bytes) in
		[(2, 4, 3, 3), (2, usize::MAX, usize::MAX, 1), (1, 100, 1, 1)]
	{
		assert_blocked_admission(slots, byte_limit, first_bytes, second_bytes);
	}
}

fn assert_blocked_admission(
	slots: usize,
	byte_limit: usize,
	first_bytes: usize,
	second_bytes: usize,
) {
	let queue = Arc::new(Queue::new(slots, byte_limit, 1));
	let cancelled = Arc::new(AtomicBool::new(false));
	let epoch = Instant::now();
	let deadline = epoch + Duration::from_secs(10);
	queue
		.push(&job(0, 0, first_bytes), epoch, deadline, &cancelled)
		.unwrap();
	let worker_queue = Arc::clone(&queue);
	let worker_cancelled = Arc::clone(&cancelled);
	let (attempt_tx, attempt_rx) = mpsc::channel();
	let (admitted_tx, admitted_rx) = mpsc::channel();
	let producer = thread::spawn(move || {
		let _finished = ProducerFinished(Arc::clone(&worker_queue));
		attempt_tx.send(()).unwrap();
		worker_queue
			.push(&job(1, 0, second_bytes), epoch, deadline, &worker_cancelled)
			.unwrap();
		admitted_tx.send(()).unwrap();
	});
	attempt_rx.recv_timeout(Duration::from_secs(5)).unwrap();
	assert_eq!(
		admitted_rx.recv_timeout(Duration::from_millis(100)),
		Err(mpsc::RecvTimeoutError::Timeout)
	);
	let before_pop = nanos(epoch.elapsed());
	assert_eq!(queue.pop().unwrap().id, 0);
	admitted_rx.recv_timeout(Duration::from_secs(5)).unwrap();
	producer.join().unwrap();
	let admitted = queue.pop().unwrap();
	assert_eq!(admitted.id, 1);
	assert!(admitted.enqueued_ns >= before_pop);
	assert!(queue.pop().is_none());
	let report = queue.report();
	assert_eq!(report["high_water_jobs"], 1);
	assert_eq!(report["high_water_bytes"], first_bytes.max(second_bytes));
}

#[test]
fn concurrent_feeders_preserve_every_id_and_each_peer_fifo() {
	let lanes = 4;
	let per_lane = 64;
	let queue = Arc::new(Queue::new(3, 11, lanes));
	let cancelled = Arc::new(AtomicBool::new(false));
	let epoch = Instant::now();
	let deadline = epoch + Duration::from_secs(10);
	let mut producers = Vec::new();
	for lane in 0..lanes {
		let queue = Arc::clone(&queue);
		let cancelled = Arc::clone(&cancelled);
		producers.push(thread::spawn(move || {
			let _finished = ProducerFinished(Arc::clone(&queue));
			for sequence in 0..per_lane {
				let id = sequence * lanes + lane;
				queue
					.push(&job(id, lane, 1 + id % 7), epoch, deadline, &cancelled)
					.unwrap();
			}
		}));
	}
	let mut received = Vec::new();
	while let Some(job) = queue.pop() {
		received.push(job.id);
	}
	for producer in producers {
		producer.join().unwrap();
	}
	for lane in 0..lanes {
		assert_eq!(
			received
				.iter()
				.copied()
				.filter(|id| id % lanes == lane)
				.collect::<Vec<_>>(),
			(0..per_lane)
				.map(|sequence| sequence * lanes + lane)
				.collect::<Vec<_>>()
		);
	}
	received.sort_unstable();
	assert_eq!(received, (0..lanes * per_lane).collect::<Vec<_>>());
	let report = queue.report();
	assert!(report["high_water_jobs"].as_u64().unwrap() <= 3);
	assert!(report["high_water_bytes"].as_u64().unwrap() <= 11);
}

#[test]
fn cancelled_feeder_finishes_without_losing_already_admitted_work() {
	let queue = Arc::new(Queue::new(1, 4, 1));
	let cancelled = Arc::new(AtomicBool::new(false));
	let epoch = Instant::now();
	let deadline = epoch + Duration::from_secs(10);
	queue
		.push(&job(0, 0, 4), epoch, deadline, &cancelled)
		.unwrap();
	cancelled.store(true, Ordering::Release);
	let result = queue.push(&job(1, 0, 4), epoch, deadline, &cancelled);
	assert!(result.is_err());
	queue.producer_finished();
	assert_eq!(queue.pop().unwrap().id, 0);
	assert!(queue.pop().is_none());
}

#[test]
fn drain_deadline_rejects_admission_even_when_queue_has_space() {
	let queue = Queue::new(1, 4, 1);
	let cancelled = AtomicBool::new(false);
	let epoch = Instant::now();
	assert!(queue.push(&job(0, 0, 4), epoch, epoch, &cancelled).is_err());
	assert!(cancelled.load(Ordering::Acquire));
	queue.producer_finished();
	assert!(queue.pop().is_none());
}

#[test]
fn split_preserves_exact_aggregate_limits() {
	for lanes in 1..32 {
		for total in lanes..100 {
			let parts: Vec<_> = (0..lanes).map(|lane| split(total, lanes, lane)).collect();
			assert_eq!(parts.iter().sum::<usize>(), total);
			assert!(parts.iter().all(|part| *part > 0));
			assert!(parts.iter().max().unwrap() - parts.iter().min().unwrap() <= 1);
		}
	}
}

#[test]
fn overlap_uses_half_open_intervals_and_does_not_sum_wall_time_twice() {
	let result = overlap(vec![(0, 10), (10, 20), (5, 15), (7, 7)]);
	assert_eq!(result["peak"], 2);
	assert_eq!(result["any_active_ns"], 20);
	assert_eq!(result["multiple_active_ns"], 10);
	assert_eq!(result["sum_active_ns"], 30);
	assert_eq!(overlap(Vec::new())["peak"], 0);
}

#[test]
fn independent_database_call_intervals_can_overlap_with_barrier_control() {
	let ready = Arc::new(Barrier::new(3));
	let entered = Arc::new(Barrier::new(3));
	let epoch = Instant::now();
	let mut threads = Vec::new();
	for _ in 0..2 {
		let ready = Arc::clone(&ready);
		let entered = Arc::clone(&entered);
		threads.push(thread::spawn(move || {
			let counts = Counters::default();
			counts.enable_trace(epoch, 1);
			ready.wait();
			let call = counts.call("controlled_test_call");
			entered.wait();
			drop(call);
			counts.take_trace()
		}));
	}
	ready.wait();
	entered.wait();
	let spans: Vec<_> = threads
		.into_iter()
		.flat_map(|thread| thread.join().unwrap())
		.collect();
	let result = overlap(
		spans
			.iter()
			.map(|span| (span.start_ns, span.end_ns))
			.collect(),
	);
	assert_eq!(result["peak"], 2);
	assert!(result["multiple_active_ns"].as_u64().unwrap() > 0);
}

fn bounded_failure_check(operation: impl FnOnce() + Send + 'static) {
	let (sender, receiver) = mpsc::channel();
	let check = thread::spawn(move || {
		let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(operation));
		let _ = sender.send(result.is_ok());
	});
	assert_eq!(
		receiver.recv_timeout(Duration::from_secs(5)),
		Ok(true),
		"failure must release all callbacks rather than hang"
	);
	check.join().unwrap();
}

#[test]
fn preparation_panic_closes_readiness_and_releases_waiting_workers() {
	bounded_failure_check(|| {
		let gate = Arc::new(StartGate::default());
		let cancelled = Arc::new(AtomicBool::new(false));
		let (ready_tx, ready_rx) = mpsc::channel::<std::result::Result<(), String>>();
		let (done_tx, done_rx) = mpsc::channel();
		let live_gate = Arc::clone(&gate);
		let live_cancelled = Arc::clone(&cancelled);
		let live_ready = ready_tx.clone();
		let live_done = done_tx.clone();
		let live = thread::spawn(move || {
			let _done = WorkerFinished {
				sender: Some(live_done),
				cancelled: live_cancelled,
			};
			live_ready.send(Ok(())).unwrap();
			drop(live_ready);
			assert!(live_gate.wait().is_err());
		});
		let failed = thread::spawn(move || {
			let _done = WorkerFinished {
				sender: Some(done_tx),
				cancelled,
			};
			let _ready = ready_tx;
			panic!("injected preparation panic");
		});
		assert_eq!(ready_rx.recv(), Ok(Ok(())));
		assert!(ready_rx.recv().is_err());
		gate.release(Err("preparation failed".into()));
		assert!(failed.join().is_err());
		live.join().unwrap();
		assert!(done_rx.recv().unwrap());
		assert!(done_rx.recv().unwrap());
	});
}

#[test]
fn worker_panic_cancels_a_blocked_feeder_and_releases_verification_waiters() {
	bounded_failure_check(|| {
		let queue = Arc::new(Queue::new(1, 4, 1));
		let cancelled = Arc::new(AtomicBool::new(false));
		let epoch = Instant::now();
		let deadline = epoch + Duration::from_secs(30);
		queue
			.push(&job(0, 0, 4), epoch, deadline, &cancelled)
			.unwrap();
		let producer_queue = Arc::clone(&queue);
		let producer_cancelled = Arc::clone(&cancelled);
		let producer = thread::spawn(move || {
			let _done = ProducerFinished(Arc::clone(&producer_queue));
			let _unwind = CancelOnUnwind(Arc::clone(&producer_cancelled));
			assert!(
				producer_queue
					.push(&job(1, 0, 4), epoch, deadline, &producer_cancelled)
					.is_err()
			);
		});
		let (done_tx, done_rx) = mpsc::channel();
		let verification = Arc::new(StartGate::default());
		let live_done = done_tx.clone();
		let live_cancelled = Arc::clone(&cancelled);
		let live_gate = Arc::clone(&verification);
		let live = thread::spawn(move || {
			let mut done = WorkerFinished {
				sender: Some(live_done),
				cancelled: live_cancelled,
			};
			done.arrive();
			assert!(live_gate.wait().is_err());
		});
		let failed = thread::spawn(move || {
			let _done = WorkerFinished {
				sender: Some(done_tx),
				cancelled,
			};
			panic!("injected worker panic outside native call");
		});
		producer.join().unwrap();
		let outcomes = [done_rx.recv().unwrap(), done_rx.recv().unwrap()];
		assert!(outcomes.contains(&true));
		verification.release(Err("worker failed".into()));
		assert!(failed.join().is_err());
		live.join().unwrap();
		assert_eq!(queue.pop().unwrap().id, 0);
		assert!(queue.pop().is_none());
	});
}

#[test]
fn producer_panic_closes_its_queue_and_signals_cancellation() {
	bounded_failure_check(|| {
		let queue = Arc::new(Queue::new(1, 4, 1));
		let cancelled = Arc::new(AtomicBool::new(false));
		let producer_queue = Arc::clone(&queue);
		let producer_cancelled = Arc::clone(&cancelled);
		let producer = thread::spawn(move || {
			let _done = ProducerFinished(producer_queue);
			let _unwind = CancelOnUnwind(producer_cancelled);
			panic!("injected producer panic");
		});
		assert!(queue.pop().is_none());
		assert!(producer.join().is_err());
		assert!(cancelled.load(Ordering::Acquire));
	});
}

#[test]
fn oversized_declared_capacity_reserves_only_the_finite_offered_work() {
	let queue = Queue::new(usize::MAX, 8, 1);
	queue.reserve(2);
	assert!(queue.state.lock().unwrap().jobs.capacity() >= 2);
	assert!(queue.state.lock().unwrap().jobs.capacity() < 16);
	let now = Instant::now();
	let cancelled = AtomicBool::new(false);
	assert!(
		queue
			.push(&job(0, 0, 9), now, now + Duration::from_secs(1), &cancelled)
			.is_err()
	);
	queue.producer_finished();
	assert!(queue.pop().is_none());
}

fn runtime_smoke(backend: &str) {
	for (population, active) in [(4, 4), (5, 3)] {
		runtime_smoke_population(backend, population, active);
	}
}

fn runtime_smoke_population(backend: &str, population: usize, active: usize) {
	let directory = tempfile::tempdir().unwrap();
	let config = super::super::Config {
		backend: backend.into(),
		active_peers: Some(active),
		warmup_messages: 0,
		small_bytes: 32,
		large_bytes: 128,
		burst_chunk_bytes: 256,
		large_every: 1,
		burst_chunks: vec![8],
		..Default::default()
	};
	let concurrent = Config {
		workers: 2,
		period_ms: vec![1],
		arrival_ms: 2,
		queue_capacity: 2,
		queue_bytes: 512,
		deadline_ms: 1000,
		drain_ms: 10_000,
		max_offered: 64,
		max_precomputed_bytes: 1024 * 1024,
	};
	let plans = cases(&config, &concurrent, active).unwrap();
	let payloads = Arc::new(Payloads {
		small: payload(32, 1),
		large: payload(128, 2),
		chunk: payload(256, 3),
	});
	for arm in [Arm::Snapshot, Arm::Row, Arm::Cached] {
		let mut fixture = ConcurrentFixture::new(
			arm,
			directory.path().join(format!("{}.sqlite", arm.label())),
			population,
			&config,
		)
		.unwrap();
		for name in ["small_period_1ms", "mixed_period_1ms", "burst_8"] {
			let plan = plans.iter().find(|plan| plan.name == name).unwrap();
			let result = measure(
				&mut fixture,
				plan,
				&config,
				&concurrent,
				Arc::clone(&payloads),
				1,
				arm.index(),
			)
			.unwrap();
			assert_eq!(result["status"], "complete");
			assert_eq!(result["outputs_verified"], true);
			assert_eq!(result["drain_expired"], false);
			let expected_messages = if name == "burst_8" { 8 } else { active * 2 };
			assert_eq!(result["offered"], expected_messages);
			assert_eq!(result["messages"], expected_messages);
			assert_eq!(result["peers"], population);
			assert_eq!(result["active_peers"], active);
			assert_eq!(result["touched_peers"], active);
			assert_eq!(
				fixture
					.peers
					.iter()
					.map(|peer| peer.index)
					.collect::<Vec<_>>(),
				(0..population).collect::<Vec<_>>()
			);
			assert_eq!(result["failures"], json!([]));
			assert_eq!(result["logical_feeder_lanes"], 2);
			let owners = if matches!(arm, Arm::Snapshot) { 1 } else { 2 };
			assert_eq!(result["owner_workers"], owners);
			let observations = result["observations"].as_array().unwrap();
			assert_eq!(
				observations
					.iter()
					.map(|entry| entry["id"].as_u64().unwrap())
					.collect::<Vec<_>>(),
				(0..expected_messages as u64).collect::<Vec<_>>()
			);
			for worker in result["workers"].as_array().unwrap() {
				let worker_id = worker["worker"].as_u64().unwrap();
				let expected_peers: Vec<_> = if matches!(arm, Arm::Snapshot) {
					(0..active).collect()
				} else {
					(worker_id as usize..active).step_by(2).collect()
				};
				assert_eq!(worker["peers"], json!(expected_peers));
				let completed = observations
					.iter()
					.filter(|entry| entry["worker"].as_u64() == Some(worker_id))
					.count() as u64;
				let factor = if matches!(arm, Arm::Row) { 2 } else { 1 };
				assert_eq!(
					worker["db_spans"].as_array().unwrap().len() as u64,
					completed * factor
				);
				assert_eq!(
					worker["database"]["network_exchanges"],
					if backend == "postgres" {
						completed * factor
					} else {
						0
					}
				);
				if matches!(arm, Arm::Cached) {
					assert_eq!(worker["cached_peers"], expected_peers.len());
					assert_eq!(worker["database"]["loads"], 0);
					assert_eq!(worker["database"]["expects"], completed);
				}
			}
			for queue in result["queues"].as_array().unwrap() {
				assert!(
					queue["high_water_jobs"].as_u64().unwrap()
						<= queue["capacity"].as_u64().unwrap()
				);
				assert!(
					queue["high_water_bytes"].as_u64().unwrap()
						<= queue["byte_capacity"].as_u64().unwrap()
				);
			}
			assert!(result["overlap"]["native"]["peak"].as_u64().unwrap() <= owners);
		}
	}
}

#[test]
fn sqlite_measure_runtime_checks_all_arms_and_queued_duplex_outputs() {
	runtime_smoke("sqlite");
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn postgres_measure_runtime_checks_all_arms_and_queued_duplex_outputs() {
	runtime_smoke("postgres");
}

#[test]
fn case_plan_rejects_invalid_resources_before_database_construction() {
	let config = super::super::Config::default();
	let base = Config::default();
	assert!(cases(&config, &base, 0).is_err());
	for change in [
		(|c: &mut Config| c.workers = 0) as fn(&mut Config),
		|c| c.queue_capacity = 0,
		|c| c.queue_bytes = 0,
		|c| c.period_ms.clear(),
		|c| c.period_ms.push(0),
		|c| c.arrival_ms = 0,
		|c| c.deadline_ms = 0,
		|c| c.drain_ms = 0,
		|c| c.max_offered = 0,
		|c| c.max_precomputed_bytes = 0,
		|c| c.arrival_ms = u64::MAX,
		|c| c.deadline_ms = u64::MAX,
		|c| c.drain_ms = u64::MAX,
		|c| c.arrival_ms = u64::MAX / 1_000_000,
		|c| c.queue_capacity = 7,
		|c| c.queue_bytes = 8 * 512_000 - 1,
		|c| c.max_offered = 12_799,
	] {
		let mut invalid = base.clone();
		change(&mut invalid);
		assert!(cases(&config, &invalid, 32).is_err());
	}
	let exact_queue = Config {
		queue_capacity: 8,
		queue_bytes: 8 * 512_000,
		..base
	};
	assert!(cases(&config, &exact_queue, 32).is_ok());
}

#[test]
fn case_plan_accounts_for_every_default_arrival_and_retained_byte_budget() {
	let config = super::super::Config::default();
	for (active, expected_operations) in [(1, 2080), (32, 45_680)] {
		let plans = cases(&config, &Config::default(), active).unwrap();
		assert_eq!(plans.len(), 13);
		assert_eq!(
			plans.iter().map(|p| p.schedule.len()).sum::<usize>(),
			expected_operations
		);
		for count in [64, 256, 512] {
			let name = format!("burst_{count}");
			let burst = plans.iter().find(|p| p.name == name).unwrap();
			assert_eq!(burst.schedule.len(), count);
			assert_eq!(burst.horizon_ns, 0);
			assert!(
				burst
					.schedule
					.iter()
					.all(|job| job.scheduled_ns == 0 && job.plaintext_bytes == 512_000)
			);
		}
		let regular = plans.iter().find(|p| p.name == "regular_large").unwrap();
		assert_eq!(regular.schedule.len(), active * 2);
		assert!(
			regular
				.schedule
				.iter()
				.all(|job| job.plaintext_bytes == 65_536)
		);
	}
	// Two retained frame/output allowances plus 1 KiB metadata for each of 512 chunks.
	let mut bounded = Config {
		max_precomputed_bytes: 524_812_288,
		..Config::default()
	};
	assert!(cases(&config, &bounded, 32).is_ok());
	bounded.max_precomputed_bytes -= 1;
	assert!(cases(&config, &bounded, 32).is_err());
	let last_ms = u64::MAX / 1_000_000;
	assert_eq!(ns(last_ms).unwrap(), last_ms * 1_000_000);
	assert!(ns(last_ms + 1).is_err());
}

#[test]
fn invalid_positive_parameters_report_the_preflight_error_before_dependent_limits() {
	let config = super::super::Config::default();
	for change in [
		(|c: &mut Config| c.queue_capacity = 0) as fn(&mut Config),
		|c| c.queue_bytes = 0,
		|c| c.arrival_ms = 0,
		|c| c.period_ms.clear(),
		|c| c.period_ms.push(0),
	] {
		let mut invalid = Config::default();
		change(&mut invalid);
		let error = cases(&config, &invalid, 32)
			.err()
			.expect("invalid input accepted");
		assert!(
			error
				.to_string()
				.starts_with("concurrent worker, queue, arrival, deadline and period"),
			"invalid positive parameter produced a downstream error instead of its preflight diagnostic: {error}"
		);
	}
}

#[test]
fn queue_reserves_the_finite_backlog_before_admission_without_growing_during_it() {
	for (capacity, offered) in [(7, 3), (3, 7), (1, 1), (4, 0)] {
		let queue = Queue::new(capacity, 64, 1);
		queue.reserve(offered);
		let admitted = capacity.min(offered);
		let allocated = queue.state.lock().unwrap().jobs.capacity();
		assert!(allocated >= admitted);
		let epoch = Instant::now();
		let cancelled = AtomicBool::new(false);
		for id in 0..admitted {
			queue
				.push(
					&job(id, 0, 1),
					epoch,
					epoch + Duration::from_secs(5),
					&cancelled,
				)
				.unwrap();
			assert_eq!(queue.state.lock().unwrap().jobs.capacity(), allocated);
		}
		queue.producer_finished();
		for id in 0..admitted {
			assert_eq!(queue.pop().unwrap().id, id);
		}
		assert!(queue.pop().is_none());
	}
}

#[test]
fn queue_close_liveness_guard_drains_fifo_and_waits_for_the_last_producer() {
	bounded_failure_check(|| {
		for producers in [1, 2, 3] {
			let queue = Arc::new(Queue::new(2, 4, producers));
			let producer_guards: Vec<_> = (0..producers)
				.map(|_| ProducerFinished(Arc::clone(&queue)))
				.collect();
			let epoch = Instant::now();
			let cancelled = AtomicBool::new(false);
			for id in 0..2 {
				queue
					.push(
						&job(id, 0, 1),
						epoch,
						epoch + Duration::from_secs(5),
						&cancelled,
					)
					.unwrap();
			}
			drop(producer_guards);
			for id in 0..2 {
				assert_eq!(queue.pop().unwrap().id, id);
				assert_eq!(queue.state.lock().unwrap().bytes, 1 - id);
			}
			assert!(queue.pop().is_none());
			assert!(queue.pop().is_none());
		}

		let queue = Arc::new(Queue::new(1, 4, 2));
		queue.producer_finished();
		let (started_tx, started_rx) = mpsc::channel();
		let (output_tx, output_rx) = mpsc::channel();
		let consumer_queue = Arc::clone(&queue);
		let consumer = thread::spawn(move || {
			started_tx.send(()).unwrap();
			output_tx
				.send(consumer_queue.pop().map(|entry| entry.id))
				.unwrap();
		});
		started_rx.recv_timeout(Duration::from_secs(1)).unwrap();
		assert_eq!(
			output_rx.recv_timeout(Duration::from_millis(100)),
			Err(mpsc::RecvTimeoutError::Timeout)
		);
		let epoch = Instant::now();
		queue
			.push(
				&job(7, 0, 1),
				epoch,
				epoch + Duration::from_secs(1),
				&AtomicBool::new(false),
			)
			.unwrap();
		assert_eq!(output_rx.recv_timeout(Duration::from_secs(1)), Ok(Some(7)));
		consumer.join().unwrap();
		queue.producer_finished();
		assert!(queue.pop().is_none());
	});
}

#[test]
fn payload_classes_preserve_declared_bytes_and_lengths() {
	let payloads = Payloads {
		small: vec![3, 1, 4],
		large: vec![9, 2, 6, 5, 3, 5, 8],
		chunk: vec![0xa5; 19],
	};
	assert_eq!(bytes(&payloads, PayloadClass::Small), &[3, 1, 4]);
	assert_eq!(
		bytes(&payloads, PayloadClass::Large),
		&[9, 2, 6, 5, 3, 5, 8]
	);
	assert_eq!(bytes(&payloads, PayloadClass::Burst), &[0xa5; 19]);
}

#[test]
fn native_commit_panic_is_reported_and_remaining_callbacks_are_cancelled() {
	bounded_failure_check(|| {
		let directory = tempfile::tempdir().unwrap();
		let path = directory.path().join("panic.sqlite");
		let config = super::super::Config::default();
		let fixture = ConcurrentFixture::new(Arm::Snapshot, path.clone(), 1, &config).unwrap();
		let jobs = Arc::new(vec![job(0, 0, 3), job(1, 0, 3)]);
		let queue = Arc::new(Queue::new(2, 6, 1));
		let gate = Arc::new(StartGate::default());
		let verification = Arc::new(StartGate::default());
		let cancelled = Arc::new(AtomicBool::new(false));
		let (ready_tx, ready_rx) = mpsc::channel();
		let (finished_tx, finished_rx) = mpsc::channel();
		let worker = Worker {
			index: 0,
			arm: Arm::Snapshot,
			location: WorkerLocation::copy(&fixture.location),
			lineage: fixture.lineage,
			peers: fixture.peers,
			jobs: Arc::clone(&jobs),
			payloads: Arc::new(Payloads {
				small: vec![2, 3, 5],
				large: vec![],
				chunk: vec![],
			}),
			queue: Arc::clone(&queue),
			gate: Arc::clone(&gate),
			finished: finished_tx,
			verification: Arc::clone(&verification),
			cancelled: Arc::clone(&cancelled),
			deadline_budget_ns: 1_000_000_000,
			finish_budget_ns: 5_000_000_000,
			logical_lanes: 1,
		};
		let thread = thread::spawn(move || worker.run(ready_tx));
		assert_eq!(ready_rx.recv_timeout(Duration::from_secs(3)), Ok(Ok(())));
		let connection = rusqlite::Connection::open(&path).unwrap();
		let saved: (Vec<u8>, Vec<u8>, Vec<u8>) = connection
			.query_row("SELECT generation,digest,value FROM snapshot", [], |row| {
				Ok((row.get(0)?, row.get(1)?, row.get(2)?))
			})
			.unwrap();
		// Corrupt only the owned fixture after successful preparation. The real store's
		// fixed-width lineage decode now panics inside the measured native operation.
		connection
			.execute("UPDATE snapshot SET lineage=x'00'", [])
			.unwrap();
		let epoch = Instant::now();
		for job in jobs.iter() {
			queue
				.push(job, epoch, epoch + Duration::from_secs(3), &cancelled)
				.unwrap();
		}
		queue.producer_finished();
		gate.release(Ok(epoch));
		assert_eq!(finished_rx.recv_timeout(Duration::from_secs(3)), Ok(false));
		verification.release(Ok(epoch));
		let result = thread.join().unwrap().unwrap();
		assert!(cancelled.load(Ordering::Acquire));
		assert!(result.observations.is_empty());
		assert_eq!(result.wire_bytes, 0);
		assert_eq!(result.failures.len(), 2);
		assert_eq!(result.failures[0]["id"], 0);
		assert_eq!(result.failures[0]["outcome"], "failed");
		assert_eq!(result.failures[0]["error"], "native operation panicked");
		assert_eq!(result.failures[0]["conflicts"], 0);
		assert_eq!(result.failures[0]["retries"], 0);
		assert_eq!(result.failures[1]["id"], 1);
		assert_eq!(result.failures[1]["outcome"], "cancelled");
		let after: (Vec<u8>, Vec<u8>, Vec<u8>) = connection
			.query_row("SELECT generation,digest,value FROM snapshot", [], |row| {
				Ok((row.get(0)?, row.get(1)?, row.get(2)?))
			})
			.unwrap();
		assert_eq!(
			saved, after,
			"a panicked callback must not persist a candidate"
		);
	});
}
