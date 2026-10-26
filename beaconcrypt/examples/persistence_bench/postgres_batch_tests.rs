// SPDX-License-Identifier: 0BSD

use std::collections::{BTreeMap, VecDeque};

use proptest::{prelude::*, test_runner::FileFailurePersistence};

use super::*;

const TIMEOUT: Duration = Duration::from_secs(5);

fn config() -> BatchConfig {
	BatchConfig {
		max_delay: Duration::ZERO,
		..BatchConfig::default()
	}
}

fn change(read: u8, expected: Option<u8>, write: u8, value: u8) -> ChangeSet {
	ChangeSet::new(RowChanges {
		reads: BTreeMap::from([(vec![read], expected.map(|value| vec![value]))]),
		writes: BTreeMap::from([(vec![write], vec![value])]),
	})
}

#[test]
fn zeroize_clears_read_and_write_secrets_while_preserving_absent_expectations() {
	let mut changes = ChangeSet::new(RowChanges {
		reads: BTreeMap::from([
			(vec![0], Some(vec![1, 2, 3])),
			(vec![1], None),
			(vec![2], Some(Vec::new())),
		]),
		writes: BTreeMap::from([(vec![3], vec![4, 5, 6]), (vec![4], vec![7])]),
	});
	changes.zeroize();
	assert_eq!(
		changes.reads,
		BTreeMap::from([
			(vec![0], Some(Vec::new())),
			(vec![1], None),
			(vec![2], Some(Vec::new())),
		])
	);
	assert_eq!(
		changes.writes,
		BTreeMap::from([(vec![3], Vec::new()), (vec![4], Vec::new())])
	);
}

fn dispatch(
	config: BatchConfig,
	changes: Vec<ChangeSet>,
	commit: impl FnMut(&[ChangeSet]) -> Result<Vec<bool>, RowError>,
) -> Vec<BatchReceipt> {
	config.validate().unwrap();
	let (sender, receiver) = mpsc::sync_channel(changes.len().max(1));
	let mut outputs = Vec::new();
	for changes in changes {
		let bytes = changes.bytes().unwrap();
		assert!(bytes <= config.max_bytes);
		let (reply, output) = mpsc::channel();
		sender
			.send(Request {
				changes,
				bytes,
				reply,
			})
			.unwrap();
		outputs.push(output);
	}
	drop(sender);
	run(
		config,
		Inbox {
			receiver,
			counts: Arc::default(),
		},
		commit,
	);
	outputs
		.into_iter()
		.map(|output| output.recv_timeout(TIMEOUT).unwrap())
		.collect()
}

#[test]
fn zero_delay_groups_independent_writes_and_shared_reads_with_one_leader() {
	let receipts = dispatch(
		config(),
		vec![change(9, None, 1, 1), change(9, Some(2), 2, 2)],
		|batch| {
			assert_eq!(batch.len(), 2);
			// Differing expectations for a shared read are validated separately by the SQL callback.
			Ok(vec![true, false])
		},
	);
	assert_eq!(receipts[0].status, Ok(()));
	assert_eq!(receipts[1].status, Err(RowError::Conflict));
	assert!(receipts[0].leader);
	assert!(!receipts[1].leader);
	assert!(receipts.iter().all(|receipt| receipt.batch_len == 2));
}

#[test]
fn read_write_and_write_write_dependencies_flush_without_reordering_or_retry() {
	let mut batches = Vec::new();
	let receipts = dispatch(
		config(),
		vec![
			change(9, None, 1, 1),
			change(1, Some(1), 2, 2),
			change(8, None, 2, 3),
			change(7, None, 8, 4),
		],
		|batch| {
			batches.push(
				batch
					.iter()
					.map(|change| change.writes.values().next().unwrap()[0])
					.collect::<Vec<_>>(),
			);
			Ok(vec![true; batch.len()])
		},
	);
	assert_eq!(batches, vec![vec![1], vec![2], vec![3], vec![4]]);
	assert!(
		receipts
			.iter()
			.all(|receipt| receipt.status.is_ok() && receipt.leader)
	);
}

#[test]
fn request_and_byte_limits_split_batches_and_allow_exact_fit() {
	for (max_requests, max_bytes) in [(2, 100), (8, 10)] {
		let mut batches = Vec::new();
		let receipts = dispatch(
			BatchConfig {
				max_requests,
				max_bytes,
				..config()
			},
			(0..5).map(|key| change(9, None, key, key)).collect(),
			|batch| {
				batches.push(batch.len());
				Ok(vec![true; batch.len()])
			},
		);
		assert_eq!(batches, vec![2, 2, 1]);
		assert_eq!(receipts.iter().filter(|receipt| receipt.leader).count(), 3);
	}
}

#[test]
fn whole_batch_errors_and_malformed_status_vectors_fail_every_request() {
	for result in [
		Err(storage("lost acknowledgement")),
		Err(RowError::Conflict),
		Ok(vec![true]),
	] {
		let receipts = dispatch(
			config(),
			vec![change(9, None, 1, 1), change(9, None, 2, 2)],
			|_| result.clone(),
		);
		assert!(
			receipts
				.iter()
				.all(|receipt| matches!(receipt.status, Err(RowError::Storage(_))))
		);
		assert_eq!(receipts[0].status, receipts[1].status);
		assert!(receipts[0].leader);
		assert!(!receipts[1].leader);
		assert_eq!(receipts[0].batch_len, 2);
		if let Err(error @ RowError::Storage(_)) = result {
			assert_eq!(receipts[0].status, Err(error));
		}
	}
}

#[test]
fn admission_rejects_oversized_changes_before_running_sql() {
	let batcher = Batcher::start(
		BatchConfig {
			max_bytes: 5,
			..config()
		},
		|batch| {
			assert_eq!(batch.len(), 1);
			Ok(vec![true])
		},
	)
	.unwrap();
	assert!(matches!(
		batcher.commit(change(0, Some(0), 1, 1)),
		Err(RowError::Storage(_))
	));
	assert_eq!(
		batcher.commit(change(0, None, 1, 1)).unwrap().status,
		Ok(())
	);
	batcher.shutdown().unwrap();
}

#[test]
fn invalid_bounds_are_rejected_and_zero_delay_is_valid() {
	config().validate().unwrap();
	BatchConfig {
		max_requests: 1024,
		queue_capacity: 1024,
		max_bytes: 1,
		max_delay: Duration::from_secs(1),
	}
	.validate()
	.unwrap();
	BatchConfig {
		queue_capacity: 2,
		max_bytes: 256 * 1024 * 1024,
		..config()
	}
	.validate()
	.unwrap();
	for invalid in [
		BatchConfig {
			max_requests: 0,
			..config()
		},
		BatchConfig {
			max_requests: 1025,
			..config()
		},
		BatchConfig {
			queue_capacity: 0,
			..config()
		},
		BatchConfig {
			queue_capacity: 1025,
			..config()
		},
		BatchConfig {
			queue_capacity: usize::MAX,
			..config()
		},
		BatchConfig {
			max_bytes: 0,
			..config()
		},
		BatchConfig {
			max_bytes: usize::MAX,
			..config()
		},
		BatchConfig {
			max_bytes: 1024 * 1024 * 1024,
			..config()
		},
		BatchConfig {
			max_delay: Duration::from_secs(2),
			..config()
		},
	] {
		assert!(matches!(invalid.validate(), Err(RowError::Storage(_))));
	}
}

#[test]
fn a_failed_commit_does_not_retry_or_prevent_following_requests() {
	let mut calls = 0;
	let batcher = Batcher::start(
		BatchConfig {
			max_delay: Duration::from_millis(1),
			..config()
		},
		move |batch| {
			calls += 1;
			assert_eq!(batch.len(), 1);
			assert_eq!(batch[0].writes.values().next().unwrap()[0], calls);
			if calls == 1 {
				Err(storage("first commit failed"))
			} else {
				Ok(vec![true])
			}
		},
	)
	.unwrap();
	assert_eq!(
		batcher.commit(change(9, None, 1, 1)).unwrap().status,
		Err(storage("first commit failed"))
	);
	assert_eq!(
		batcher.commit(change(9, None, 2, 2)).unwrap().status,
		Ok(())
	);
	batcher.shutdown().unwrap();
}

#[test]
fn an_idle_singleton_keeps_the_positive_coalescing_window_open() {
	let delay = Duration::from_millis(20);
	let batcher = Batcher::start(
		BatchConfig {
			max_requests: 2,
			max_delay: delay,
			..config()
		},
		|batch| Ok(vec![true; batch.len()]),
	)
	.unwrap();
	let before_submission = Instant::now();
	let receipt = batcher.commit(change(9, None, 1, 1)).unwrap();
	assert_eq!(receipt.status, Ok(()));
	// No other sender or shutdown can end this window early. Scheduling noise can only
	// lengthen the observed interval, so the test does not impose a wall-clock upper bound.
	assert!(before_submission.elapsed() >= delay);
	batcher.shutdown().unwrap();
}

#[test]
fn no_receipt_precedes_commit_acknowledgement_and_shutdown_drains_accepted_requests() {
	let (entered, waiting) = mpsc::channel();
	let (release, gate) = mpsc::channel();
	let mut first = true;
	let batcher = Batcher::start(
		BatchConfig {
			max_requests: 2,
			..config()
		},
		move |batch| {
			if first {
				first = false;
				entered.send(()).unwrap();
				gate.recv_timeout(TIMEOUT).unwrap();
			} else {
				assert_eq!(batch.len(), 2);
			}
			Ok(vec![true; batch.len()])
		},
	)
	.unwrap();
	let sentinel = batcher.submit(change(9, None, 0, 0)).unwrap();
	waiting.recv_timeout(TIMEOUT).unwrap();
	let second = batcher.submit(change(9, None, 1, 1)).unwrap();
	let third = batcher.submit(change(9, None, 2, 2)).unwrap();
	assert_eq!(batcher.pending_for_test(), 2);
	for result in [&sentinel, &second, &third] {
		assert!(matches!(result.try_recv(), Err(mpsc::TryRecvError::Empty)));
	}
	let closing = batcher.clone();
	let shutdown = thread::spawn(move || closing.shutdown());
	release.send(()).unwrap();
	shutdown.join().unwrap().unwrap();
	assert_eq!(sentinel.recv_timeout(TIMEOUT).unwrap().status, Ok(()));
	let second = second.recv_timeout(TIMEOUT).unwrap();
	let third = third.recv_timeout(TIMEOUT).unwrap();
	assert_eq!((second.status, third.status), (Ok(()), Ok(())));
	assert_eq!((second.batch_len, third.batch_len), (2, 2));
	assert!(second.leader && !third.leader);
	assert_eq!(batcher.pending_for_test(), 0);
	assert!(matches!(
		batcher.commit(change(9, None, 3, 3)),
		Err(RowError::Storage(_))
	));
	batcher.shutdown().unwrap();
}

#[test]
fn coordinator_panic_disconnects_active_and_queued_requests_and_shutdown_reports_it() {
	let (entered, waiting) = mpsc::channel();
	let (release, gate) = mpsc::channel();
	let batcher = Batcher::start(config(), move |_| {
		entered.send(()).unwrap();
		gate.recv_timeout(TIMEOUT).unwrap();
		panic!("simulated commit worker panic")
	})
	.unwrap();
	let first = batcher.submit(change(9, None, 0, 0)).unwrap();
	waiting.recv_timeout(TIMEOUT).unwrap();
	let second = batcher.submit(change(9, None, 1, 1)).unwrap();
	release.send(()).unwrap();
	for result in [first, second] {
		assert!(matches!(
			result.recv_timeout(TIMEOUT),
			Err(mpsc::RecvTimeoutError::Disconnected)
		));
	}
	assert!(matches!(
		batcher.commit(change(9, None, 2, 2)),
		Err(RowError::Storage(_))
	));
	assert!(matches!(batcher.shutdown(), Err(RowError::Storage(_))));
	assert!(matches!(batcher.shutdown(), Err(RowError::Storage(_))));
}

#[test]
fn abandoning_a_reply_does_not_stop_following_commits_or_last_handle_cleanup() {
	struct Exited(mpsc::Sender<()>);
	impl Drop for Exited {
		fn drop(&mut self) {
			let _ = self.0.send(());
		}
	}
	let (exit, exited) = mpsc::channel();
	let signal = Exited(exit);
	let batcher = Batcher::start(config(), move |batch| {
		let _ = &signal;
		Ok(vec![true; batch.len()])
	})
	.unwrap();
	drop(batcher.submit(change(9, None, 1, 1)).unwrap());
	assert_eq!(
		batcher.commit(change(9, None, 2, 2)).unwrap().status,
		Ok(())
	);
	drop(batcher);
	exited.recv_timeout(TIMEOUT).unwrap();
}

#[test]
fn dropping_the_last_handle_waits_for_the_active_commit_and_drains_the_queue() {
	let (entered, waiting) = mpsc::channel();
	let (release, gate) = mpsc::channel();
	let mut first = true;
	let batcher = Batcher::start(config(), move |batch| {
		if first {
			first = false;
			entered.send(()).unwrap();
			gate.recv_timeout(TIMEOUT).unwrap();
		}
		Ok(vec![true; batch.len()])
	})
	.unwrap();
	let active = batcher.submit(change(9, None, 0, 0)).unwrap();
	waiting.recv_timeout(TIMEOUT).unwrap();
	let queued = batcher.submit(change(9, None, 1, 1)).unwrap();
	assert_eq!(batcher.pending_for_test(), 1);
	let (started, dropping) = mpsc::channel();
	let (finished, dropped) = mpsc::channel();
	let dropper = thread::spawn(move || {
		started.send(()).unwrap();
		drop(batcher);
		finished.send(()).unwrap();
	});
	dropping.recv_timeout(TIMEOUT).unwrap();
	assert!(matches!(
		dropped.recv_timeout(Duration::from_millis(100)),
		Err(mpsc::RecvTimeoutError::Timeout)
	));
	release.send(()).unwrap();
	dropped.recv_timeout(TIMEOUT).unwrap();
	// Both receipts must already exist when Drop returns, including the queued request.
	assert_eq!(active.try_recv().unwrap().status, Ok(()));
	assert_eq!(queued.try_recv().unwrap().status, Ok(()));
	dropper.join().unwrap();
}

fn property_config() -> ProptestConfig {
	ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok()
			.and_then(|value| value.parse().ok())
			.unwrap_or(64),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/proptest-regressions/postgres_batch.txt"
		)))),
		..ProptestConfig::default()
	}
}

proptest! {
	#![proptest_config(property_config())]
	#[test]
	fn grouped_optimistic_commits_match_serial_validation_without_retry(
		operations in prop::collection::vec((0u8..6, prop::option::of(0u8..4), 0u8..6, 0u8..4), 0..24),
		max_requests in 1usize..9,
		max_bytes in 6usize..40,
	) {
		let config = BatchConfig { max_requests, max_bytes, ..config() };
		let changes: Vec<_> = operations.iter().map(|&(read, expected, write, value)| change(read, expected, write, value)).collect();
		let mut ordered: VecDeque<_> = changes.iter().map(|change| (change.reads.clone(), change.writes.clone())).collect();
		let mut expected_state = WriteSet::new();
		let expected_status: Vec<_> = changes.iter().map(|change| {
			let valid = change.reads.iter().all(|(key, expected)| expected_state.get(key) == expected.as_ref());
			if valid { expected_state.extend(change.writes.clone()); }
			valid
		}).collect();
		let mut actual_state = WriteSet::new();
		let receipts = dispatch(config, changes, |batch| {
			assert!(!batch.is_empty() && batch.len() <= max_requests);
			assert!(batch.iter().map(|change| change.bytes().unwrap()).sum::<usize>() <= max_bytes);
			for (index, change) in batch.iter().enumerate() {
				let expected = ordered.pop_front().unwrap();
				assert_eq!((&change.reads, &change.writes), (&expected.0, &expected.1));
				for other in &batch[..index] {
					// Independent model: no write key may appear in the other operation at all.
					assert!(change.writes.keys().all(|key| !other.reads.contains_key(key) && !other.writes.contains_key(key)));
					assert!(other.writes.keys().all(|key| !change.reads.contains_key(key)));
				}
			}
			Ok(batch.iter().map(|change| {
				let valid = change.reads.iter().all(|(key, expected)| actual_state.get(key) == expected.as_ref());
				if valid { actual_state.extend(change.writes.clone()); }
				valid
			}).collect())
		});
		prop_assert!(ordered.is_empty());
		prop_assert_eq!(actual_state, expected_state);
		let actual_status: Vec<_> = receipts.iter().map(|receipt| receipt.status.is_ok()).collect();
		prop_assert_eq!(actual_status, expected_status);
		let mut offset = 0;
		while offset < receipts.len() {
			let length = receipts[offset].batch_len;
			prop_assert!(length > 0 && length <= max_requests && offset + length <= receipts.len());
			for index in 0..length {
				prop_assert_eq!(receipts[offset + index].batch_len, length);
				prop_assert_eq!(receipts[offset + index].leader, index == 0);
			}
			offset += length;
		}
	}
}
