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
	let queue = Arc::new(Queue::new(2, 4, 1));
	let cancelled = Arc::new(AtomicBool::new(false));
	let epoch = Instant::now();
	let deadline = epoch + Duration::from_secs(10);
	queue
		.push(&job(0, 0, 3), epoch, deadline, &cancelled)
		.unwrap();
	let worker_queue = Arc::clone(&queue);
	let worker_cancelled = Arc::clone(&cancelled);
	let producer = thread::spawn(move || {
		let _finished = ProducerFinished(Arc::clone(&worker_queue));
		worker_queue
			.push(&job(1, 0, 3), epoch, deadline, &worker_cancelled)
			.unwrap();
	});
	let before_pop = nanos(epoch.elapsed());
	assert_eq!(queue.pop().unwrap().id, 0);
	producer.join().unwrap();
	let admitted = queue.pop().unwrap();
	assert_eq!(admitted.id, 1);
	assert!(admitted.enqueued_ns >= before_pop);
	assert!(queue.pop().is_none());
	let report = queue.report();
	assert_eq!(report["high_water_jobs"], 1);
	assert_eq!(report["high_water_bytes"], 3);
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
	let directory = tempfile::tempdir().unwrap();
	let config = super::super::Config {
		backend: backend.into(),
		active_peers: Some(4),
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
	let plans = cases(&config, &concurrent, 4).unwrap();
	let payloads = Arc::new(Payloads {
		small: payload(32, 1),
		large: payload(128, 2),
		chunk: payload(256, 3),
	});
	for arm in [Arm::Snapshot, Arm::Row, Arm::Cached] {
		let mut fixture = ConcurrentFixture::new(
			arm,
			directory.path().join(format!("{}.sqlite", arm.label())),
			4,
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
			assert_eq!(result["offered"], 8);
			assert_eq!(result["messages"], 8);
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
				(0..8).collect::<Vec<_>>()
			);
			for worker in result["workers"].as_array().unwrap() {
				let worker_id = worker["worker"].as_u64().unwrap();
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
					assert_eq!(worker["cached_peers"], 2);
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
