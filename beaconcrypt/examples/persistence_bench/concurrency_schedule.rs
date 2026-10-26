// SPDX-License-Identifier: 0BSD

//! Fixed offered arrivals and complete callback accounting, independent of wall clocks or storage.

use serde::Serialize;

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum PayloadClass {
	Small,
	Large,
	Burst,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Flow {
	Send,
	Receive,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct Scheduled {
	pub id: usize,
	pub peer: usize,
	pub peer_sequence: usize,
	pub scheduled_ns: u64,
	pub payload: PayloadClass,
	pub flow: Flow,
	pub plaintext_bytes: usize,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Workload {
	Small,
	Large,
	Mixed {
		large_every: usize,
	},
	Heterogeneous {
		periods_ns: Vec<u64>,
		large_every: usize,
	},
	Burst {
		messages: usize,
	},
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ScheduleConfig {
	pub peers: usize,
	pub interval_ns: u64,
	pub horizon_ns: u64,
	pub small_bytes: usize,
	pub large_bytes: usize,
	pub burst_bytes: usize,
	pub max_operations: usize,
	pub max_plaintext_bytes: u64,
}

fn validate(config: &ScheduleConfig, workload: &Workload) -> Result<(), String> {
	if config.peers == 0
		|| config.interval_ns == 0
		|| config.horizon_ns == 0
		|| config.small_bytes == 0
		|| config.large_bytes == 0
		|| config.burst_bytes == 0
		|| config.max_operations == 0
		|| config.max_plaintext_bytes == 0
	{
		return Err("schedule parameters and limits must be positive".into());
	}
	if config.peers > config.max_operations {
		return Err("active peer count exceeds the bounded operation budget".into());
	}
	match workload {
		Workload::Mixed { large_every: 0 } | Workload::Heterogeneous { large_every: 0, .. } => {
			return Err("large_every must be positive".into());
		}
		Workload::Heterogeneous { periods_ns, .. }
			if periods_ns.is_empty() || periods_ns.contains(&0) =>
		{
			return Err("heterogeneous periods must be nonempty and positive".into());
		}
		Workload::Burst { messages: 0 } => {
			return Err("burst must contain at least one message".into());
		}
		_ => {}
	}
	Ok(())
}

fn period_phase(config: &ScheduleConfig, workload: &Workload, peer: usize) -> (u64, u64) {
	match workload {
		Workload::Burst { .. } => (0, 0),
		Workload::Heterogeneous { periods_ns, .. } => {
			// Contiguous cohorts avoid aliasing period=peer%4 with worker=peer%8.
			// With 32 peers and four cohorts, each eight-peer block contains every lane.
			let peers = config.peers as u128;
			let count = periods_ns.len() as u128;
			let cohort = peer as u128 * count / peers;
			let first = (cohort * peers).div_ceil(count);
			let end = ((cohort + 1) * peers).div_ceil(count);
			let period = periods_ns[cohort as usize];
			let phase = (peer as u128 - first) * u128::from(period) / (end - first);
			(period, phase as u64)
		}
		_ => {
			let phase = peer as u128 * u128::from(config.interval_ns) / config.peers as u128;
			(config.interval_ns, phase as u64)
		}
	}
}

/// Record each peer's exact cadence. Bursts have zero arrival offset and no periodic cadence.
pub fn peer_period_phase(
	config: &ScheduleConfig,
	workload: &Workload,
	peer: usize,
) -> Result<(u64, u64), String> {
	validate(config, workload)?;
	if peer >= config.peers {
		return Err("schedule peer is out of range".into());
	}
	Ok(period_phase(config, workload, peer))
}

fn payload(config: &ScheduleConfig, workload: &Workload, sequence: usize) -> (PayloadClass, usize) {
	match workload {
		Workload::Burst { .. } => (PayloadClass::Burst, config.burst_bytes),
		Workload::Large => (PayloadClass::Large, config.large_bytes),
		Workload::Mixed { large_every } | Workload::Heterogeneous { large_every, .. }
			if (sequence / 2 + 1).is_multiple_of(*large_every) =>
		{
			// Classify duplex pairs so alternating flows both receive the large workload.
			(PayloadClass::Large, config.large_bytes)
		}
		_ => (PayloadClass::Small, config.small_bytes),
	}
}

fn offered_count(horizon: u64, period: u64, phase: u64) -> u128 {
	if phase >= horizon {
		0
	} else {
		u128::from((horizon - 1 - phase) / period) + 1
	}
}

fn plaintext_count(config: &ScheduleConfig, workload: &Workload, count: u128) -> u128 {
	match workload {
		Workload::Burst { .. } => count * config.burst_bytes as u128,
		Workload::Mixed { large_every } | Workload::Heterogeneous { large_every, .. } => {
			let cadence = *large_every as u128;
			let pairs = count / 2;
			let large = (pairs / cadence) * 2
				+ u128::from(count % 2 == 1 && (pairs + 1).is_multiple_of(cadence));
			large * config.large_bytes as u128 + (count - large) * config.small_bytes as u128
		}
		Workload::Small => count * config.small_bytes as u128,
		Workload::Large => count * config.large_bytes as u128,
	}
}

/// Construct a finite, immutable offered workload before any fixture or frame allocation.
/// The byte cap covers plaintext only; callers additionally bound ciphertext/output allocations.
pub fn schedule(config: &ScheduleConfig, workload: Workload) -> Result<Vec<Scheduled>, String> {
	validate(config, &workload)?;
	let mut operations = 0u128;
	let mut bytes = 0u128;
	let mut account = |count: u128| -> Result<(), String> {
		operations = operations
			.checked_add(count)
			.ok_or("offered count overflow")?;
		bytes = bytes
			.checked_add(plaintext_count(config, &workload, count))
			.ok_or("offered plaintext count overflow")?;
		if operations > config.max_operations as u128 {
			return Err("offered operation limit exceeded before allocation".into());
		}
		if bytes > u128::from(config.max_plaintext_bytes) {
			return Err("offered plaintext byte limit exceeded before allocation".into());
		}
		Ok(())
	};
	match workload {
		Workload::Burst { messages } => account(messages as u128)?,
		_ => {
			for peer in 0..config.peers {
				let (period, phase) = period_phase(config, &workload, peer);
				account(offered_count(config.horizon_ns, period, phase))?;
			}
		}
	}
	let count = usize::try_from(operations).map_err(|_| "offered count does not fit usize")?;
	let mut jobs = Vec::new();
	jobs.try_reserve_exact(count)
		.map_err(|_| "cannot reserve bounded schedule")?;
	let mut push = |peer: usize, peer_sequence: usize, scheduled_ns: u64| {
		let (class, plaintext_bytes) = payload(config, &workload, peer_sequence);
		jobs.push(Scheduled {
			id: 0,
			peer,
			peer_sequence,
			scheduled_ns,
			payload: class,
			flow: if peer_sequence.is_multiple_of(2) {
				Flow::Send
			} else {
				Flow::Receive
			},
			plaintext_bytes,
		});
	};
	match workload {
		Workload::Burst { messages } => {
			for index in 0..messages {
				push(index % config.peers, index / config.peers, 0);
			}
		}
		_ => {
			for peer in 0..config.peers {
				let (period, phase) = period_phase(config, &workload, peer);
				let count = offered_count(config.horizon_ns, period, phase);
				for sequence in 0..count {
					let at = u128::from(phase) + sequence * u128::from(period);
					push(peer, sequence as usize, at as u64);
				}
			}
			jobs.sort_unstable_by_key(|job| (job.scheduled_ns, job.peer, job.peer_sequence));
		}
	}
	for (id, job) in jobs.iter_mut().enumerate() {
		job.id = id;
	}
	Ok(jobs)
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
pub struct CompletedTiming {
	pub enqueue_attempt_ns: u64,
	pub enqueued_ns: u64,
	pub owner_start_ns: u64,
	pub native_start_ns: u64,
	pub native_end_ns: u64,
	pub completed_ns: u64,
}

#[derive(Clone, Copy, Debug, Serialize, PartialEq, Eq)]
pub struct TimingMetrics {
	pub scheduler_lag_ns: u64,
	pub enqueue_backpressure_ns: u64,
	pub queue_wait_ns: u64,
	pub owner_wait_ns: u64,
	pub service_ns: u64,
	pub completion_overhead_ns: u64,
	pub response_ns: u64,
	pub deadline_lag_ns: u64,
	pub deadline_met: bool,
}

/// Deadlines classify the completed callback; they never cancel or retry a native transition.
pub fn timings(
	job: &Scheduled,
	value: &CompletedTiming,
	deadline_budget_ns: u64,
) -> Result<TimingMetrics, String> {
	let points = [
		job.scheduled_ns,
		value.enqueue_attempt_ns,
		value.enqueued_ns,
		value.owner_start_ns,
		value.native_start_ns,
		value.native_end_ns,
		value.completed_ns,
	];
	if points.windows(2).any(|pair| pair[0] > pair[1]) {
		return Err("callback timestamps must retain planned arrival and stage order".into());
	}
	let response_ns = value.completed_ns - job.scheduled_ns;
	Ok(TimingMetrics {
		scheduler_lag_ns: value.enqueue_attempt_ns - job.scheduled_ns,
		enqueue_backpressure_ns: value.enqueued_ns - value.enqueue_attempt_ns,
		queue_wait_ns: value.owner_start_ns - value.enqueued_ns,
		owner_wait_ns: value.native_start_ns - value.owner_start_ns,
		service_ns: value.native_end_ns - value.native_start_ns,
		completion_overhead_ns: value.completed_ns - value.native_end_ns,
		response_ns,
		deadline_lag_ns: response_ns.saturating_sub(deadline_budget_ns),
		deadline_met: response_ns <= deadline_budget_ns,
	})
}

#[cfg(test)]
#[path = "concurrency_schedule_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "concurrency_duplex_tests.rs"]
mod duplex_tests;
