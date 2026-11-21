// SPDX-License-Identifier: 0BSD

//! Small, independently testable contracts for benchmark routing and timing.

use std::time::{Duration, Instant};

pub(super) fn metadata_matches(actual: (u64, u64), expected: (u64, u64)) -> bool {
	actual == expected
}

/// Callers provide at least one owner. Inactive peers have no owner in this workload.
pub(super) fn owner_for_peer(peer: usize, active: usize, owners: usize) -> Option<usize> {
	if peer >= active {
		None
	} else {
		Some(peer % owners)
	}
}

pub(super) fn owned_job_count(
	peers: impl IntoIterator<Item = usize>,
	active: usize,
	owners: usize,
	owner: usize,
) -> usize {
	peers
		.into_iter()
		.filter(|&peer| owner_for_peer(peer, active, owners) == Some(owner))
		.count()
}

pub(super) fn measurement_epoch(now: Instant) -> Instant {
	now + Duration::from_millis(50)
}

/// A bounded sleep preserves opportunities to observe cancellation between sleeps.
pub(super) fn pacing_delay(now: Instant, scheduled: Instant) -> Option<Duration> {
	if now >= scheduled {
		None
	} else {
		Some(scheduled.duration_since(now).min(Duration::from_millis(50)))
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Completion {
	pub outputs_verified: bool,
	pub drain_expired: bool,
	pub complete: bool,
}

impl Completion {
	/// A late committed result remains verified, but cannot make an over-budget report complete.
	pub(super) fn new(
		offered: usize,
		completed: usize,
		failures: usize,
		batch_ns: u64,
		finish_budget_ns: u64,
	) -> Self {
		let outputs_verified = completed == offered && failures == 0;
		let drain_expired = batch_ns > finish_budget_ns;
		Self {
			outputs_verified,
			drain_expired,
			complete: outputs_verified && !drain_expired,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn metadata_rejects_each_corrupted_field_and_a_wrong_protocol_role() {
		let expected_peer_output = (41, 7);
		assert!(metadata_matches((41, 7), expected_peer_output));
		for corrupted in [(42, 7), (41, 8), (42, 8), (19, 7), (7, 41)] {
			assert!(!metadata_matches(corrupted, expected_peer_output));
		}
		let expected_server_output = (19, 7);
		assert!(metadata_matches((19, 7), expected_server_output));
		assert!(!metadata_matches((41, 7), expected_server_output));
		assert!(metadata_matches((u64::MAX, u64::MAX), (u64::MAX, u64::MAX)));
		assert!(!metadata_matches(
			(u64::MAX - 1, u64::MAX),
			(u64::MAX, u64::MAX)
		));
		assert!(!metadata_matches(
			(u64::MAX, u64::MAX - 1),
			(u64::MAX, u64::MAX)
		));
		assert!(!metadata_matches((0, 7), expected_peer_output));
		assert!(!metadata_matches((41, 0), expected_peer_output));
	}

	#[test]
	fn owner_assignment_handles_uneven_populations_and_inactive_peers() {
		let expected = [
			Some(0),
			Some(1),
			Some(2),
			Some(0),
			Some(1),
			Some(2),
			Some(0),
			None,
			None,
		];
		for (peer, expected_owner) in expected.into_iter().enumerate() {
			assert_eq!(owner_for_peer(peer, 7, 3), expected_owner);
		}
		for peer in 0..7 {
			assert_eq!(
				owner_for_peer(peer, 7, 1),
				Some(0),
				"snapshot has one owner"
			);
		}
		assert_eq!(owner_for_peer(7, 7, 1), None);
		assert_eq!(owner_for_peer(0, 0, 1), None);
		assert_eq!(owner_for_peer(usize::MAX, 7, 3), None);
		assert_eq!(owner_for_peer(0, 3, 8), Some(0));
		assert_eq!(owner_for_peer(1, 3, 8), Some(1));
		assert_eq!(owner_for_peer(2, 3, 8), Some(2));
		assert_eq!(owner_for_peer(3, 3, 8), None);
	}

	#[test]
	fn owned_job_counts_follow_explicit_peer_occurrences_and_exclude_inactive_ids() {
		let peers = [0, 2, 4, 6, 1, 1, 5, 5, 5, 9, 10, usize::MAX];
		assert_eq!(owned_job_count(peers, 7, 3, 0), 2);
		assert_eq!(owned_job_count(peers, 7, 3, 1), 3);
		assert_eq!(owned_job_count(peers, 7, 3, 2), 4);
		assert_eq!(owned_job_count(peers, 7, 3, 3), 0);
		assert_eq!(owned_job_count(peers, 7, 1, 0), 9);
		assert_eq!(owned_job_count(peers, 0, 3, 0), 0);
		assert_eq!(owned_job_count([], 7, 3, 0), 0);
	}

	#[test]
	fn measurement_epoch_has_an_exact_future_lead_without_reading_the_clock_again() {
		let origin = Instant::now();
		for offset in [
			Duration::ZERO,
			Duration::from_nanos(1),
			Duration::from_secs(2),
		] {
			let supplied_now = origin + offset;
			let epoch = measurement_epoch(supplied_now);
			assert!(epoch > supplied_now);
			assert_eq!(
				epoch.duration_since(supplied_now),
				Duration::from_millis(50)
			);
		}
	}

	#[test]
	fn pacing_respects_due_arrivals_and_the_sleep_cap_boundary() {
		let now = Instant::now();
		for (remaining_ns, expected_ns) in [
			(1, 1),
			(1_000_000, 1_000_000),
			(49_999_999, 49_999_999),
			(50_000_000, 50_000_000),
			(50_000_001, 50_000_000),
			(250_000_000, 50_000_000),
		] {
			assert_eq!(
				pacing_delay(now, now + Duration::from_nanos(remaining_ns)),
				Some(Duration::from_nanos(expected_ns))
			);
		}
		assert_eq!(pacing_delay(now, now), None);
		assert_eq!(pacing_delay(now + Duration::from_nanos(1), now), None);
		assert_eq!(pacing_delay(now + Duration::from_secs(2), now), None);
	}

	#[test]
	fn completion_requires_every_offered_callback_and_preserves_late_commit_information() {
		let on_time = Completion {
			outputs_verified: true,
			drain_expired: false,
			complete: true,
		};
		assert_eq!(Completion::new(2, 2, 0, 9, 10), on_time);
		assert_eq!(Completion::new(2, 2, 0, 10, 10), on_time);
		assert_eq!(
			Completion::new(2, 2, 0, 11, 10),
			Completion {
				outputs_verified: true,
				drain_expired: true,
				complete: false
			}
		);
		for (completed, failures) in [(0, 0), (1, 0), (3, 0), (2, 1), (1, 1), (2, 2)] {
			assert_eq!(
				Completion::new(2, completed, failures, 9, 10),
				Completion {
					outputs_verified: false,
					drain_expired: false,
					complete: false
				}
			);
			assert_eq!(
				Completion::new(2, completed, failures, 11, 10),
				Completion {
					outputs_verified: false,
					drain_expired: true,
					complete: false
				}
			);
		}
		// This helper preserves count/deadline policy; nonempty schedules are checked upstream.
		assert_eq!(Completion::new(0, 0, 0, 0, 0), on_time);
		assert_eq!(
			Completion::new(usize::MAX, usize::MAX, 0, u64::MAX, u64::MAX),
			on_time
		);
		assert_eq!(
			Completion::new(2, 2, 0, u64::MAX, u64::MAX - 1),
			Completion {
				outputs_verified: true,
				drain_expired: true,
				complete: false
			}
		);
	}
}
