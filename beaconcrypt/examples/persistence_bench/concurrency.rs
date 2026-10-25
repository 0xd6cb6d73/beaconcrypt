// SPDX-License-Identifier: 0BSD

//! Offered-load experiment. All arrivals remain in the denominator when producers are blocked.

#[cfg(test)]
#[path = "concurrency_runtime_tests.rs"]
mod tests;

use std::{
	collections::VecDeque,
	fs::OpenOptions,
	path::PathBuf,
	rc::Rc,
	sync::{
		Arc, Condvar, Mutex,
		atomic::{AtomicBool, Ordering},
		mpsc,
	},
	thread,
	time::{Duration, Instant},
};

use beaconcrypt::{Beacon, RowError, SnapshotLineage};
use serde::Serialize;
use serde_json::{Value, json};

use super::concurrency_schedule::{
	CompletedTiming, Flow, PayloadClass, ScheduleConfig, Scheduled, Workload, peer_period_phase,
	schedule, timings,
};
use super::{
	Arm, Backend, Fixture, Location, Options, Payloads, Result, SERVER_ID, command,
	database::Counters, environment, nanos, payload, write_report,
};

#[derive(Clone, Serialize)]
pub struct Config {
	pub workers: usize,
	pub period_ms: Vec<usize>,
	pub arrival_ms: u64,
	pub queue_capacity: usize,
	pub queue_bytes: usize,
	pub deadline_ms: u64,
	pub drain_ms: u64,
	pub max_offered: usize,
	pub max_precomputed_bytes: u64,
}

impl Default for Config {
	fn default() -> Self {
		Self {
			workers: 8,
			period_ms: vec![1000, 100, 10, 5],
			arrival_ms: 2000,
			queue_capacity: 256,
			queue_bytes: 16 * 1024 * 1024,
			deadline_ms: 1000,
			drain_ms: 600_000,
			max_offered: 20_000,
			max_precomputed_bytes: 512 * 1024 * 1024,
		}
	}
}

fn ns(ms: u64) -> Result<u64> {
	ms.checked_mul(1_000_000)
		.ok_or_else(|| "millisecond duration overflows nanoseconds".into())
}

struct Case {
	name: String,
	schedule: Arc<Vec<Scheduled>>,
	peer_schedule: Value,
	horizon_ns: u64,
}

fn cases(config: &super::Config, concurrent: &Config, active: usize) -> Result<Vec<Case>> {
	if concurrent.workers == 0
		|| concurrent.queue_capacity == 0
		|| concurrent.queue_bytes == 0
		|| concurrent.period_ms.is_empty()
		|| concurrent.period_ms.contains(&0)
		|| concurrent.arrival_ms == 0
		|| concurrent.deadline_ms == 0
		|| concurrent.drain_ms == 0
	{
		return Err(
			"concurrent worker, queue, arrival, deadline and period values must be positive".into(),
		);
	}
	let workers = concurrent.workers.min(active);
	if concurrent.queue_capacity < workers
		|| concurrent.queue_bytes / workers
			< config
				.burst_chunk_bytes
				.max(config.large_bytes)
				.max(config.small_bytes)
	{
		return Err(
			"each row lane needs at least one job slot and room for the largest payload".into(),
		);
	}
	let periods: Vec<u64> = concurrent
		.period_ms
		.iter()
		.map(|&ms| ns(ms as u64))
		.collect::<Result<_>>()?;
	let mut definitions = Vec::new();
	for (&ms, &period) in concurrent.period_ms.iter().zip(&periods) {
		definitions.push((format!("small_period_{ms}ms"), period, Workload::Small));
		definitions.push((
			format!("mixed_period_{ms}ms"),
			period,
			Workload::Mixed {
				large_every: config.large_every,
			},
		));
	}
	definitions.push(("regular_large".into(), 1_000_000_000, Workload::Large));
	definitions.push((
		"heterogeneous_mixed".into(),
		periods[0],
		Workload::Heterogeneous {
			periods_ns: periods,
			large_every: config.large_every,
		},
	));
	for &messages in &config.burst_chunks {
		definitions.push((format!("burst_{messages}"), 1, Workload::Burst { messages }));
	}
	definitions.into_iter().map(|(name, interval_ns, workload)| {
		let settings = ScheduleConfig { peers: active, interval_ns, horizon_ns: ns(concurrent.arrival_ms)?,
			small_bytes: config.small_bytes, large_bytes: config.large_bytes, burst_bytes: config.burst_chunk_bytes,
			max_operations: concurrent.max_offered, max_plaintext_bytes: concurrent.max_precomputed_bytes };
		let jobs = schedule(&settings, workload.clone())?;
		// Receive ciphertext, output plaintext/ciphertext, and metadata are retained for checking.
		// Bound their conservative estimate separately from the bounded callback queues.
		let retained = jobs.iter().try_fold(0_u64, |total, job| {
			total.checked_add((job.plaintext_bytes as u64).checked_mul(2)?.checked_add(1024)?)
		}).ok_or("precomputed fixture size overflow")?;
		if retained > concurrent.max_precomputed_bytes {
			return Err(format!("{name} requires an estimated {retained} retained bytes, above --max-precomputed-bytes").into());
		}
		let peer_schedule: Vec<_> = (0..active).map(|peer| {
			peer_period_phase(&settings, &workload, peer).map(|(period_ns, phase_ns)| json!({"peer":peer,"period_ns":period_ns,"phase_ns":phase_ns,"lane":peer%workers}))
		}).collect::<std::result::Result<_,_>>()?;
		let horizon_ns = if matches!(workload, Workload::Burst {..}) { 0 } else { settings.horizon_ns };
		Ok(Case { name, schedule: Arc::new(jobs), peer_schedule: json!(peer_schedule), horizon_ns })
	}).collect()
}

struct Peer {
	index: usize,
	beacon: Beacon,
	kid: u64,
	send_sequence: u64,
	receive_sequence: u64,
}

enum WorkerLocation {
	Sqlite(PathBuf),
	Postgres(Box<super::postgres::PgFixture>),
}
impl WorkerLocation {
	fn copy(location: &Location) -> Self {
		match location {
			Location::Sqlite(path) => Self::Sqlite(path.clone()),
			Location::Postgres(fixture) => Self::Postgres(Box::new(fixture.worker_copy())),
		}
	}
	fn local(self) -> Location {
		match self {
			Self::Sqlite(path) => Location::Sqlite(path),
			Self::Postgres(fixture) => Location::Postgres(Rc::new(*fixture)),
		}
	}
}

struct ConcurrentFixture {
	arm: Arm,
	location: Location,
	lineage: SnapshotLineage,
	peers: Vec<Peer>,
}
impl ConcurrentFixture {
	fn new(arm: Arm, path: PathBuf, peers: usize, config: &super::Config) -> Result<Self> {
		let fixture = Fixture::new(arm, path, peers, config)?;
		let Fixture {
			server,
			location,
			lineage,
			beacons,
			kids,
			send_sequences,
			receive_sequences,
			..
		} = fixture;
		drop(server);
		let peers = beacons
			.into_iter()
			.zip(kids)
			.zip(send_sequences)
			.zip(receive_sequences)
			.enumerate()
			.map(
				|(index, (((beacon, kid), send_sequence), receive_sequence))| Peer {
					index,
					beacon,
					kid,
					send_sequence,
					receive_sequence,
				},
			)
			.collect();
		Ok(Self {
			arm,
			location,
			lineage,
			peers,
		})
	}
}

struct Queued {
	id: usize,
	attempt_ns: u64,
	enqueued_ns: u64,
	bytes: usize,
}
struct QueueState {
	jobs: VecDeque<Queued>,
	bytes: usize,
	producers: usize,
	high_jobs: usize,
	high_bytes: usize,
}
struct Queue {
	state: Mutex<QueueState>,
	changed: Condvar,
	capacity: usize,
	byte_capacity: usize,
}
impl Queue {
	fn new(capacity: usize, byte_capacity: usize, producers: usize) -> Self {
		Self {
			state: Mutex::new(QueueState {
				jobs: VecDeque::new(),
				bytes: 0,
				producers,
				high_jobs: 0,
				high_bytes: 0,
			}),
			changed: Condvar::new(),
			capacity,
			byte_capacity,
		}
	}
	fn reserve(&self, offered: usize) {
		self.state
			.lock()
			.unwrap()
			.jobs
			.reserve_exact(self.capacity.min(offered));
	}
	fn push(
		&self,
		job: &Scheduled,
		epoch: Instant,
		deadline: Instant,
		cancelled: &AtomicBool,
	) -> std::result::Result<(), String> {
		if job.plaintext_bytes > self.byte_capacity {
			return Err("callback exceeds queue byte capacity".into());
		}
		let attempt_ns = nanos(epoch.elapsed());
		let mut state = self.state.lock().unwrap();
		loop {
			if cancelled.load(Ordering::Acquire) {
				return Err("another callback failed or drain deadline expired".into());
			}
			let now = Instant::now();
			if now >= deadline {
				cancelled.store(true, Ordering::Release);
				self.changed.notify_all();
				return Err("drain deadline expired before admission".into());
			}
			if state.jobs.len() < self.capacity
				&& job.plaintext_bytes <= self.byte_capacity.saturating_sub(state.bytes)
			{
				break;
			}
			(state, _) = self
				.changed
				.wait_timeout(state, (deadline - now).min(Duration::from_millis(50)))
				.unwrap();
		}
		let enqueued_ns = nanos(epoch.elapsed());
		state.bytes += job.plaintext_bytes;
		state.jobs.push_back(Queued {
			id: job.id,
			attempt_ns,
			enqueued_ns,
			bytes: job.plaintext_bytes,
		});
		state.high_jobs = state.high_jobs.max(state.jobs.len());
		state.high_bytes = state.high_bytes.max(state.bytes);
		self.changed.notify_all();
		Ok(())
	}
	fn pop(&self) -> Option<Queued> {
		let mut state = self.state.lock().unwrap();
		loop {
			if let Some(job) = state.jobs.pop_front() {
				state.bytes -= job.bytes;
				self.changed.notify_all();
				return Some(job);
			}
			if state.producers == 0 {
				return None;
			}
			state = self.changed.wait(state).unwrap();
		}
	}
	fn producer_finished(&self) {
		let mut state = self.state.lock().unwrap();
		state.producers -= 1;
		self.changed.notify_all();
	}
	fn report(&self) -> Value {
		let state = self.state.lock().unwrap();
		json!({"capacity":self.capacity,"byte_capacity":self.byte_capacity,"high_water_jobs":state.high_jobs,"high_water_bytes":state.high_bytes})
	}
}

struct ProducerFinished(Arc<Queue>);
impl Drop for ProducerFinished {
	fn drop(&mut self) {
		self.0.producer_finished();
	}
}

/// Every worker reports leaving the measured phase, including unwinding before normal arrival.
/// This avoids an uncancellable barrier stranding surviving workers after a panic.
struct WorkerFinished {
	sender: Option<mpsc::Sender<bool>>,
	cancelled: Arc<AtomicBool>,
}
impl WorkerFinished {
	fn arrive(&mut self) {
		if let Some(sender) = self.sender.take() {
			let _ = sender.send(false);
		}
	}
}
impl Drop for WorkerFinished {
	fn drop(&mut self) {
		if let Some(sender) = self.sender.take() {
			self.cancelled.store(true, Ordering::Release);
			let _ = sender.send(true);
		}
	}
}

struct CancelOnUnwind(Arc<AtomicBool>);
impl Drop for CancelOnUnwind {
	fn drop(&mut self) {
		if thread::panicking() {
			self.0.store(true, Ordering::Release);
		}
	}
}

#[derive(Default)]
struct StartGate {
	value: Mutex<Option<std::result::Result<Instant, String>>>,
	changed: Condvar,
}
impl StartGate {
	fn wait(&self) -> std::result::Result<Instant, String> {
		let mut value = self.value.lock().unwrap();
		while value.is_none() {
			value = self.changed.wait(value).unwrap();
		}
		value.as_ref().unwrap().clone()
	}
	fn release(&self, value: std::result::Result<Instant, String>) {
		*self.value.lock().unwrap() = Some(value);
		self.changed.notify_all();
	}
}

fn bytes(payloads: &Payloads, kind: PayloadClass) -> &[u8] {
	match kind {
		PayloadClass::Small => &payloads.small,
		PayloadClass::Large => &payloads.large,
		PayloadClass::Burst => &payloads.chunk,
	}
}

struct Prepared {
	frame: Option<Vec<u8>>,
	sequence: u64,
	kid: u64,
	local_peer: usize,
}

struct WorkerResult {
	peers: Vec<Peer>,
	report: Value,
	observations: Vec<Value>,
	failures: Vec<Value>,
	wire_bytes: u64,
}

struct Worker {
	index: usize,
	arm: Arm,
	location: WorkerLocation,
	lineage: SnapshotLineage,
	peers: Vec<Peer>,
	jobs: Arc<Vec<Scheduled>>,
	payloads: Arc<Payloads>,
	queue: Arc<Queue>,
	gate: Arc<StartGate>,
	finished: mpsc::Sender<bool>,
	verification: Arc<StartGate>,
	cancelled: Arc<AtomicBool>,
	deadline_budget_ns: u64,
	finish_budget_ns: u64,
	logical_lanes: usize,
}

impl Worker {
	fn run(
		mut self,
		ready: mpsc::Sender<std::result::Result<(), String>>,
	) -> std::result::Result<WorkerResult, String> {
		let mut finished = WorkerFinished {
			sender: Some(self.finished.clone()),
			cancelled: Arc::clone(&self.cancelled),
		};
		let counts = Rc::new(Counters::default());
		let location = self.location.local();
		let prepared = (|| -> Result<_> {
			let (mut server, open_ns) = Backend::open(
				self.arm,
				&location,
				Rc::clone(&counts),
				self.lineage,
				self.peers.len(),
			)?;
			let cold = counts.take();
			// Each owner warms only the peers it owns, outside all arrival/service timing.
			for peer in &mut self.peers {
				let sent = server.encrypt(b"concurrent warmup", peer.kid)?;
				let received = peer
					.beacon
					.decrypt_message(&sent.ciphertext)
					.ok_or("warmup send rejected")?;
				if received.plaintext != b"concurrent warmup" {
					return Err("warmup send mismatch".into());
				}
				peer.send_sequence += 1;
				let sent = peer
					.beacon
					.encrypt_message(b"concurrent warmup")
					.ok_or("warmup client rejected")?;
				if server.decrypt(&sent.ciphertext)?.plaintext != b"concurrent warmup" {
					return Err("warmup receive mismatch".into());
				}
				peer.receive_sequence += 1;
			}
			let warm = counts.take();
			let mut inputs: Vec<Option<Prepared>> = (0..self.jobs.len()).map(|_| None).collect();
			for (local_peer, peer) in self.peers.iter_mut().enumerate() {
				for job in self.jobs.iter().filter(|job| job.peer == peer.index) {
					let (frame, sequence) = match job.flow {
						Flow::Send => {
							peer.send_sequence += 1;
							(None, peer.send_sequence)
						}
						Flow::Receive => {
							let output = peer
								.beacon
								.encrypt_message(bytes(&self.payloads, job.payload))
								.ok_or("receive pre-generation failed")?;
							peer.receive_sequence += 1;
							(Some(output.ciphertext), peer.receive_sequence)
						}
					};
					inputs[job.id] = Some(Prepared {
						frame,
						sequence,
						kid: peer.kid,
						local_peer,
					});
				}
			}
			Ok((server, open_ns, cold, warm, inputs))
		})();
		let (mut server, open_ns, cold, warm, inputs) = match prepared {
			Ok(value) => {
				let _ = ready.send(Ok(()));
				value
			}
			Err(error) => {
				let error = error.to_string();
				let _ = ready.send(Err(error.clone()));
				return Err(error);
			}
		};
		drop(ready);
		let epoch = self.gate.wait()?;
		let count = inputs.iter().filter(|input| input.is_some()).count();
		let mut observations = Vec::with_capacity(count);
		let mut failures = Vec::new();
		let mut outputs = Vec::with_capacity(count);
		counts.enable_trace(epoch, count * 2);
		let mut wire_bytes = 0_u64;
		while let Some(queued) = self.queue.pop() {
			let job = &self.jobs[queued.id];
			let owner_start_ns = nanos(epoch.elapsed());
			if owner_start_ns >= self.finish_budget_ns {
				self.cancelled.store(true, Ordering::Release);
			}
			if self.cancelled.load(Ordering::Acquire) {
				failures.push(json!({"id":job.id,"peer":job.peer,"lane":job.peer%self.logical_lanes,"worker":self.index,"outcome":"cancelled","error":"run failed or drain deadline expired"}));
				continue;
			}
			let input = inputs[job.id].as_ref().expect("stable peer owner");
			let native_start_ns = nanos(epoch.elapsed());
			let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> Result<_> {
				match job.flow {
					Flow::Send => {
						let output =
							server.encrypt(bytes(&self.payloads, job.payload), input.kid)?;
						Ok((output.ciphertext, output.key_id, output.seq))
					}
					Flow::Receive => {
						let output = server.decrypt(input.frame.as_ref().unwrap())?;
						Ok((output.plaintext, output.key_id, output.seq))
					}
				}
			}));
			let native_end_ns = nanos(epoch.elapsed());
			let output = match result {
				Ok(Ok(output)) => output,
				other => {
					let (error, conflicts) = match other {
						Ok(Err(error)) => (
							error.to_string(),
							usize::from(matches!(
								error.downcast_ref::<RowError>(),
								Some(RowError::Conflict)
							)),
						),
						Err(_) => ("native operation panicked".into(), 0),
						_ => unreachable!(),
					};
					self.cancelled.store(true, Ordering::Release);
					failures.push(json!({"id":job.id,"peer":job.peer,"lane":job.peer%self.logical_lanes,"worker":self.index,"outcome":"failed","error":error,"conflicts":conflicts,"retries":0}));
					continue;
				}
			};
			wire_bytes += match job.flow {
				Flow::Send => output.0.len(),
				Flow::Receive => input.frame.as_ref().unwrap().len(),
			} as u64;
			outputs.push((job.id, output));
			let completed_ns = nanos(epoch.elapsed());
			let timing = CompletedTiming {
				enqueue_attempt_ns: queued.attempt_ns,
				enqueued_ns: queued.enqueued_ns,
				owner_start_ns,
				native_start_ns,
				native_end_ns,
				completed_ns,
			};
			// Materialize JSON only after every worker leaves the measured phase.
			observations.push((job.id, timing));
		}
		let database = counts.take();
		let spans = counts.take_trace();
		finished.arrive();
		self.verification.wait()?;
		// This barrier prevents client verification on a fast lane from contaminating another lane.
		let mut checked = Vec::with_capacity(observations.len());
		for ((id, timing), (output_id, (output, kid, seq))) in observations.into_iter().zip(outputs)
		{
			if id != output_id {
				return Err("output observation identity mismatch".into());
			}
			let job = &self.jobs[id];
			let input = inputs[id].as_ref().unwrap();
			if kid != input.kid || seq != input.sequence {
				return Err("peer/sequence verification failed".into());
			}
			let plaintext = match job.flow {
				Flow::Send => {
					let decoded = self.peers[input.local_peer]
						.beacon
						.decrypt_message(&output)
						.ok_or("client output authentication failed")?;
					if decoded.key_id != SERVER_ID || decoded.seq != seq {
						return Err("client output metadata mismatch".into());
					}
					decoded.plaintext
				}
				Flow::Receive => output,
			};
			if plaintext != bytes(&self.payloads, job.payload) {
				return Err("plaintext verification failed".into());
			}
			let metrics = timings(job, &timing, self.deadline_budget_ns)?;
			checked.push(json!({"id":id,"peer":job.peer,"lane":job.peer%self.logical_lanes,"worker":self.index,"timing":timing,"metrics":metrics,"outcome":"completed","conflicts":0,"retries":0,"attempts":1}));
		}
		let report = json!({"worker":self.index,"peers":self.peers.iter().map(|p|p.index).collect::<Vec<_>>(),"warm_database_open_ns":open_ns,
			"cold_open_database":cold,"warm_database":warm,"database":database,"db_spans":spans,
			"cached_peers":server.cached_peers(),"cache_capacity":server.cached_peers().map(|_|self.peers.len())});
		Ok(WorkerResult {
			peers: self.peers,
			report,
			observations: checked,
			failures,
			wire_bytes,
		})
	}
}

fn split(total: usize, lanes: usize, lane: usize) -> usize {
	total / lanes + usize::from(lane < total % lanes)
}

fn overlap(mut intervals: Vec<(u64, u64)>) -> Value {
	let mut edges = Vec::with_capacity(intervals.len() * 2);
	for (start, end) in intervals.drain(..) {
		if end > start {
			edges.push((start, 1_i64));
			edges.push((end, -1));
		}
	}
	// End before start at an equal timestamp: half-open intervals never invent overlap.
	edges.sort_unstable();
	let mut active = 0_i64;
	let mut peak = 0_i64;
	let mut previous = 0;
	let mut any = 0_u64;
	let mut concurrent = 0_u64;
	let mut weighted = 0_u64;
	for (time, delta) in edges {
		let dt = time - previous;
		if active > 0 {
			any += dt;
			weighted += dt * active as u64;
		}
		if active > 1 {
			concurrent += dt;
		}
		active += delta;
		peak = peak.max(active);
		previous = time;
	}
	json!({"peak":peak,"any_active_ns":any,"multiple_active_ns":concurrent,"sum_active_ns":weighted})
}

fn measure(
	fixture: &mut ConcurrentFixture,
	case: &Case,
	config: &super::Config,
	concurrent: &Config,
	payloads: Arc<Payloads>,
	trial: usize,
	pair_order: usize,
) -> Result<Value> {
	let active = config.active_peers.unwrap().min(fixture.peers.len());
	let lanes = concurrent.workers.min(active);
	let owners = if matches!(fixture.arm, Arm::Snapshot) {
		1
	} else {
		lanes
	};
	let queues: Vec<_> = (0..owners)
		.map(|owner| {
			Arc::new(Queue::new(
				split(concurrent.queue_capacity, owners, owner),
				split(concurrent.queue_bytes, owners, owner),
				if owners == 1 { lanes } else { 1 },
			))
		})
		.collect();
	for (owner, queue) in queues.iter().enumerate() {
		let offered = case
			.schedule
			.iter()
			.filter(|job| owners == 1 || job.peer % lanes == owner)
			.count();
		queue.reserve(offered);
	}
	let gate = Arc::new(StartGate::default());
	let (finished_tx, finished_rx) = mpsc::channel();
	let verification = Arc::new(StartGate::default());
	let cancelled = Arc::new(AtomicBool::new(false));
	let (ready_tx, ready_rx) = mpsc::channel();
	let mut partitions: Vec<Vec<Peer>> = (0..owners).map(|_| Vec::new()).collect();
	let mut inactive = Vec::new();
	for peer in fixture.peers.drain(..) {
		if peer.index < active {
			let owner = if owners == 1 { 0 } else { peer.index % lanes };
			partitions[owner].push(peer);
		} else {
			inactive.push(peer);
		}
	}
	let finish_budget_ns = case
		.horizon_ns
		.checked_add(ns(concurrent.drain_ms)?)
		.ok_or("drain deadline overflow")?;
	let mut workers = Vec::new();
	for (index, peers) in partitions.into_iter().enumerate() {
		let worker = Worker {
			index,
			arm: fixture.arm,
			location: WorkerLocation::copy(&fixture.location),
			lineage: fixture.lineage,
			peers,
			jobs: Arc::clone(&case.schedule),
			payloads: Arc::clone(&payloads),
			queue: Arc::clone(&queues[index]),
			gate: Arc::clone(&gate),
			finished: finished_tx.clone(),
			verification: Arc::clone(&verification),
			cancelled: Arc::clone(&cancelled),
			deadline_budget_ns: ns(concurrent.deadline_ms)?,
			finish_budget_ns,
			logical_lanes: lanes,
		};
		let ready = ready_tx.clone();
		workers.push(thread::spawn(move || worker.run(ready)));
	}
	drop(ready_tx);
	drop(finished_tx);
	let mut preparation_error = None;
	for _ in 0..owners {
		match ready_rx.recv() {
			Ok(Ok(())) => {}
			Ok(Err(error)) => {
				preparation_error = Some(error);
				break;
			}
			Err(error) => {
				preparation_error = Some(error.to_string());
				break;
			}
		}
	}
	if preparation_error.is_none()
		&& let Err(error) = fixture.location.checkpoint()
	{
		preparation_error = Some(error.to_string());
	}
	let footprint_before = if preparation_error.is_none() {
		match fixture.location.footprint(fixture.arm) {
			Ok(value) => value,
			Err(error) => {
				preparation_error = Some(error.to_string());
				Value::Null
			}
		}
	} else {
		Value::Null
	};
	if let Some(error) = preparation_error {
		gate.release(Err(error.clone()));
		for worker in workers {
			let _ = worker.join();
		}
		return Err(error.into());
	}
	let mut producers = Vec::new();
	for lane in 0..lanes {
		let jobs = Arc::clone(&case.schedule);
		let queue = Arc::clone(&queues[if owners == 1 { 0 } else { lane }]);
		let gate = Arc::clone(&gate);
		let cancelled = Arc::clone(&cancelled);
		producers.push(thread::spawn(move || {
			let _finished = ProducerFinished(Arc::clone(&queue));
			let _unwind = CancelOnUnwind(Arc::clone(&cancelled));
			let epoch = gate
				.wait()
				.expect("preparation finished before producer launch");
			let deadline = epoch + Duration::from_nanos(finish_budget_ns);
			let mut failures = Vec::new();
			for job in jobs.iter().filter(|job| job.peer % lanes == lane) {
				let scheduled = epoch + Duration::from_nanos(job.scheduled_ns);
				while Instant::now() < scheduled && !cancelled.load(Ordering::Acquire) {
					thread::sleep(
						scheduled
							.saturating_duration_since(Instant::now())
							.min(Duration::from_millis(50)),
					);
				}
				if let Err(error) = queue.push(job, epoch, deadline, &cancelled) {
					failures.push(
						json!({"id":job.id,"peer":job.peer,"lane":lane,"outcome":"not_admitted","error":error}),
					);
				}
			}
			failures
		}));
	}
	let epoch = Instant::now() + Duration::from_millis(50);
	gate.release(Ok(epoch));
	let mut failures = Vec::new();
	let mut thread_error = None;
	for producer in producers {
		match producer.join() {
			Ok(records) => failures.extend(records),
			Err(_) => {
				cancelled.store(true, Ordering::Release);
				thread_error = Some("producer thread panicked".to_owned());
			}
		}
	}
	for _ in 0..owners {
		match finished_rx.recv() {
			Ok(false) => {}
			Ok(true) | Err(_) => {
				thread_error = Some("worker aborted before verification".to_owned());
			}
		}
	}
	verification.release(match &thread_error {
		Some(error) => Err(error.clone()),
		None => Ok(epoch),
	});
	let mut observations = Vec::new();
	let mut worker_reports = Vec::new();
	let mut wire_bytes = 0_u64;
	for worker in workers {
		match worker.join() {
			Ok(Ok(result)) => {
				inactive.extend(result.peers);
				observations.extend(result.observations);
				failures.extend(result.failures);
				wire_bytes += result.wire_bytes;
				worker_reports.push(result.report);
			}
			Ok(Err(error)) => thread_error = Some(error),
			Err(_) => thread_error = Some("worker thread panicked".to_owned()),
		}
	}
	if let Some(error) = thread_error {
		return Err(error.into());
	}
	inactive.sort_by_key(|peer| peer.index);
	fixture.peers = inactive;
	observations.sort_by_key(|entry| entry["id"].as_u64());
	failures.sort_by_key(|entry| entry["id"].as_u64());
	let batch_ns = observations
		.iter()
		.filter_map(|entry| entry["timing"]["completed_ns"].as_u64())
		.max()
		.unwrap_or(0);
	let mut owner_intervals = Vec::new();
	let mut native_intervals = Vec::new();
	for entry in &observations {
		let t = &entry["timing"];
		owner_intervals.push((
			t["owner_start_ns"].as_u64().unwrap(),
			t["completed_ns"].as_u64().unwrap(),
		));
		native_intervals.push((
			t["native_start_ns"].as_u64().unwrap(),
			t["native_end_ns"].as_u64().unwrap(),
		));
	}
	let db_intervals = worker_reports
		.iter()
		.flat_map(|worker| worker["db_spans"].as_array().unwrap())
		.map(|span| {
			(
				span["start_ns"].as_u64().unwrap(),
				span["end_ns"].as_u64().unwrap(),
			)
		})
		.collect();
	let plaintext_bytes: u64 = case
		.schedule
		.iter()
		.map(|job| job.plaintext_bytes as u64)
		.sum();
	let lane_load:Vec<_>=(0..lanes).map(|lane|json!({"lane":lane,"offered":case.schedule.iter().filter(|job|job.peer%lanes==lane).count(),"plaintext_bytes":case.schedule.iter().filter(|job|job.peer%lanes==lane).map(|job|job.plaintext_bytes as u64).sum::<u64>()})).collect();
	let outputs_verified = failures.is_empty() && observations.len() == case.schedule.len();
	let drain_expired = batch_ns > finish_budget_ns;
	let complete = outputs_verified && !drain_expired;
	Ok(
		json!({"arm":fixture.arm.label(),"trial":trial,"pair_order":pair_order,"peers":fixture.peers.len(),"active_peers":active,
		"touched_peers":case.schedule.iter().map(|job|job.peer).collect::<std::collections::BTreeSet<_>>().len(),"scenario":case.name,"direction":"duplex",
		"offered":case.schedule.len(),"messages":observations.len(),"plaintext_bytes":plaintext_bytes,"wire_bytes":wire_bytes,
		"planned_horizon_ns":case.horizon_ns,"deadline_budget_ns":ns(concurrent.deadline_ms)?,"drain_budget_ns":ns(concurrent.drain_ms)?,
		"peer_schedule":case.peer_schedule,"lane_load":lane_load,"scheduled":*case.schedule,"observations":observations,"failures":failures,
		"workers":worker_reports,"queues":queues.iter().map(|queue|queue.report()).collect::<Vec<_>>(),"logical_feeder_lanes":lanes,"owner_workers":owners,
		"server_batch_ns":batch_ns,"operations_per_second":if batch_ns>0 {observations.len() as f64/(batch_ns as f64/1e9)}else{0.0},
		"plaintext_mib_per_second":if batch_ns>0 {plaintext_bytes as f64/1048576.0/(batch_ns as f64/1e9)}else{0.0},
		"overlap":{"owner":overlap(owner_intervals),"native":overlap(native_intervals),"database_client_call":overlap(db_intervals)},
		"footprint_before":footprint_before,"footprint_after":fixture.location.footprint(fixture.arm)?,"outputs_verified":outputs_verified,"drain_expired":drain_expired,"status":if complete{"complete"}else{"failed"}}),
	)
}

pub fn run(options: Options) -> Result<()> {
	let source_environment = environment();
	let mut config = options.config;
	config.active_peers = Some(config.active_peers.unwrap_or(32));
	// Validate all schedules and memory/queue bounds before creating any database fixture.
	let plans = config
		.peer_counts
		.iter()
		.map(|&peers| {
			cases(
				&config,
				&options.concurrency,
				config.active_peers.unwrap().min(peers),
			)
		})
		.collect::<Result<Vec<_>>>()?;
	let mut output = OpenOptions::new()
		.create_new(true)
		.write(true)
		.open(&options.output)?;
	let parent = options
		.database_directory
		.unwrap_or(std::env::current_dir()?);
	let directory = tempfile::Builder::new()
		.prefix("beaconcrypt-concurrent-bench-")
		.tempdir_in(parent)?;
	let filesystem_type = command(
		"stat",
		&["-f", "-c", "%T", &directory.path().to_string_lossy()],
	);
	if config.backend == "sqlite" && matches!(filesystem_type.as_deref(), Some("tmpfs" | "ramfs")) {
		return Err("use persistent storage for database fixtures".into());
	}
	let payloads = Arc::new(Payloads {
		small: payload(config.small_bytes, 1),
		large: payload(config.large_bytes, 2),
		chunk: payload(config.burst_chunk_bytes, 3),
	});
	let mut report = json!({"schema_version":3,"arms":["snapshot","row","cached_row"],"backend":config.backend,"status":"running",
		"component":"native durable persistence with concurrent offered-load callbacks","config":config,"concurrency":options.concurrency,"environment":source_environment,
		"fixture_workspace":directory.path(),"filesystem_type":filesystem_type,"fixtures":[],"results":[],
		"scope":"Snapshot: one resident owner and connection. Row/cached: stable per-peer owner lanes with independent connections to one authoritative database. No provider transport or application receipt journal.",
		"timing":"Immutable absolute arrivals include upstream backlog, bounded-queue waiting and native service. All offered work drains; deadline misses do not cancel it. Unexpected errors or drain cap make the report failed. Pre-generation, warmup and client verification are outside timing.",
		"queue_policy":"Same logical feeder lanes and aggregate queued-job/queued-plaintext-byte limits. Snapshot shares its queue; rows partition capacity by lane. Blocked feeders retain all original planned arrival times. In-service work is additional to waiting queue capacity.",
		"overlap_definition":"Owner and native API spans include database calls. Database client-call spans include lock/network/commit waiting, not database server CPU execution. Distinct worker intervals establish overlapping requests, not necessarily overlapping physical writes.",
		"byte_metrics":"Logical values, plaintext and query exchanges are not physical disk/network I/O. Precomputed requests/results are retained for verification and are harness memory.",
		"retries":"No automatic retries. Unexpected conflicts/storage errors fail the case and cancel remaining work explicitly."});
	write_report(&mut output, &report)?;
	let outcome = (|| -> Result<()> {
		for (peer_index, (&peers, cases)) in config.peer_counts.iter().zip(&plans).enumerate() {
			for trial in 1..=config.trials {
				let mut fixtures = Vec::new();
				let mut arms = [Arm::Snapshot, Arm::Row, Arm::Cached];
				arms.rotate_left((trial - 1 + peer_index) % 3);
				for arm in arms {
					let fixture = ConcurrentFixture::new(
						arm,
						directory
							.path()
							.join(format!("{}-{peers}-{trial}.sqlite", arm.label())),
						peers,
						&config,
					)?;
					report["fixtures"].as_array_mut().unwrap().push(json!({"arm":arm.label(),"trial":trial,"peers":peers,"lineage":fixture.lineage.as_bytes(),"database_settings":fixture.location.settings()}));
					fixtures.push(fixture);
				}
				fixtures.sort_by_key(|fixture| fixture.arm.index());
				for (case_index, case) in cases.iter().enumerate() {
					let first = (trial - 1 + peer_index + case_index) % 3;
					for order in 0..3 {
						let index = (first + order) % 3;
						let result = measure(
							&mut fixtures[index],
							case,
							&config,
							&options.concurrency,
							Arc::clone(&payloads),
							trial,
							order,
						)?;
						let failed = result["status"] != "complete";
						report["results"].as_array_mut().unwrap().push(result);
						if failed {
							return Err(
								"concurrent case failed; inspect explicit failure records".into()
							);
						}
					}
					println!(
						"trial={trial} peers={peers} concurrent={} offered_per_arm={}",
						case.name,
						case.schedule.len()
					);
				}
				write_report(&mut output, &report)?;
			}
		}
		Ok(())
	})();
	report["status"] = json!(if outcome.is_ok() {
		"complete"
	} else {
		"failed"
	});
	if let Err(error) = &outcome {
		report["error"] = json!(error.to_string());
	}
	write_report(&mut output, &report)?;
	outcome
}
