// SPDX-License-Identifier: 0BSD

#![cfg(all(
	feature = "std",
	feature = "beacon",
	feature = "server",
	feature = "pqxdh"
))]

use std::{
	alloc::{GlobalAlloc, Layout, System},
	cell::Cell,
	ptr,
	sync::{Arc, Mutex},
};

use beaconcrypt::{
	Beacon, CachedRowServer, PersistenceError, PersistentServer, ProviderBeacon, ProviderServer,
	RowServer, SendOutcome, Server, ServerSnapshot, SnapshotHead, SnapshotLineage, SnapshotStore,
};

#[path = "../examples/sqlite/store.rs"]
mod sqlite;

thread_local! {
	static FAIL_BYTES: Cell<usize> = const { Cell::new(0) };
	static FAILED: Cell<bool> = const { Cell::new(false) };
}

struct FaultAllocator;

fn reject(size: usize) -> bool {
	FAIL_BYTES
		.try_with(|target| {
			if target.get() != 0 && target.get() == size {
				target.set(0);
				FAILED.with(|failed| failed.set(true));
				true
			} else {
				false
			}
		})
		.unwrap_or(false)
}

// Each fault is thread-local and affects one fallible reservation; all other allocations use the system allocator.
unsafe impl GlobalAlloc for FaultAllocator {
	unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
		if reject(layout.size()) {
			ptr::null_mut()
		} else {
			unsafe { System.alloc(layout) }
		}
	}

	unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
		unsafe { System.dealloc(pointer, layout) };
	}

	unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
		if reject(size) {
			ptr::null_mut()
		} else {
			unsafe { System.realloc(pointer, layout, size) }
		}
	}
}

#[global_allocator]
static ALLOCATOR: FaultAllocator = FaultAllocator;

fn fail_frame_write<T>(sequence: u64, sender: u64, operation: impl FnOnce() -> T) -> T {
	let bytes = beaconcrypt_core::transport::protected_frame_len(7, sequence, sender).unwrap();
	struct Reset;
	impl Drop for Reset {
		fn drop(&mut self) {
			FAIL_BYTES.with(|target| target.set(0));
		}
	}
	FAILED.with(|failed| failed.set(false));
	FAIL_BYTES.with(|target| target.set(bytes));
	let guard = Reset;
	let output = operation();
	drop(guard);
	assert!(
		FAILED.with(Cell::get),
		"the final frame reservation must fail"
	);
	output
}

fn pair() -> (Server, Beacon, u64) {
	let mut server = Server::new(19, Some(&[7; 32]), Some(&[8; 32]));
	let mut beacon = Beacon::new(
		19,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	assert!(matches!(
		beacon.encrypt_message_outcome(b"fresh"),
		SendOutcome::Rejected
	));
	let request = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&request).unwrap();
	let response = server.build_registration_response(pending, None).unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	(server, beacon, response.kid)
}

#[test]
fn raw_outcomes_distinguish_rejection_and_actual_frame_writer_failure() {
	let (mut server, mut beacon, kid) = pair();
	let before = server.ratchet_status(kid).unwrap().send_sequence();
	assert!(matches!(
		server.encrypt_message_outcome(b"", kid),
		SendOutcome::Rejected
	));
	assert!(matches!(
		server.encrypt_message_outcome(b"unknown", kid + 1),
		SendOutcome::Rejected
	));
	assert_eq!(server.ratchet_status(kid).unwrap().send_sequence(), before);

	for flavor in 0..3 {
		let before = server.ratchet_status(kid).unwrap().send_sequence();
		let output = fail_frame_write(before + 1, 19, || match flavor {
			0 => server.encrypt_message_outcome(b"payload", kid).map(|_| ()),
			1 => server
				.encrypt_and_update_outcome(b"payload", kid)
				.map(|_| ()),
			_ => server
				.encrypt_and_update_json_outcome(b"payload", kid)
				.map(|_| ()),
		});
		assert!(matches!(output, SendOutcome::ConsumedWithoutOutput));
		assert!(output.changed());
		assert_eq!(
			server.ratchet_status(kid).unwrap().send_sequence(),
			before + 1
		);
		let sent = server
			.encrypt_message_outcome(b"next", kid)
			.into_option()
			.unwrap();
		assert_eq!(sent.seq, before + 2);
		assert_eq!(beacon.decrypt_message(&sent).unwrap().plaintext, b"next");
	}

	let before = beacon.ratchet_status().unwrap().send_sequence();
	let sender = beacon.identity_key_kid();
	let output = fail_frame_write(before + 1, sender, || {
		beacon.encrypt_message_outcome(b"payload")
	});
	assert!(matches!(output, SendOutcome::ConsumedWithoutOutput));
	assert_eq!(beacon.ratchet_status().unwrap().send_sequence(), before + 1);
	let sent = beacon
		.encrypt_message_outcome(b"reply")
		.into_option()
		.unwrap();
	assert_eq!(server.decrypt_message(&sent).unwrap().plaintext, b"reply");
}

#[derive(Default)]
struct State {
	bytes: Option<Vec<u8>>,
	head: Option<SnapshotHead>,
	writes: usize,
	fail: Option<(PersistenceError, bool)>,
}

#[derive(Clone, Default)]
struct Store(Arc<Mutex<State>>);

impl SnapshotStore for Store {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		Ok(self
			.0
			.lock()
			.unwrap()
			.bytes
			.clone()
			.map(ServerSnapshot::from_bytes))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		let mut state = self.0.lock().unwrap();
		state.writes += 1;
		if state.head.as_ref() != expected {
			return Ok(false);
		}
		let head = replacement.validate_successor(expected)?;
		let failure = state.fail.take();
		if failure.is_none_or(|(_, published)| published) {
			state.bytes = Some(replacement.as_bytes().to_vec());
			state.head = Some(head);
		}
		match failure {
			Some((error, _)) => Err(error),
			None => Ok(true),
		}
	}
}

fn persistent_pair() -> (PersistentServer<Store>, Beacon, u64, Store) {
	let store = Store::default();
	let mut server =
		PersistentServer::create(19, Some(&[7; 32]), Some(&[8; 32]), store.clone()).unwrap();
	let mut beacon = Beacon::new(
		19,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let request = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&request).unwrap().unwrap();
	let response = server
		.build_registration_response(pending, None)
		.unwrap()
		.unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	(server, beacon, response.kid, store)
}

#[test]
fn persistent_consumed_outcome_is_durable_and_unchanged_rejection_skips_cas() {
	let (mut server, mut beacon, kid, store) = persistent_pair();
	let head = server.head();
	let writes = store.0.lock().unwrap().writes;
	assert!(matches!(
		server.encrypt_message_outcome(b"", kid).unwrap(),
		SendOutcome::Rejected
	));
	assert_eq!(server.head(), head);
	assert_eq!(store.0.lock().unwrap().writes, writes);
	let before = server.ratchet_status(kid).unwrap().send_sequence();
	let outcome = fail_frame_write(before + 1, 19, || {
		server.encrypt_message_outcome(b"payload", kid)
	})
	.unwrap();
	assert!(matches!(outcome, SendOutcome::ConsumedWithoutOutput));
	assert_eq!(server.head().generation(), head.generation() + 1);
	assert_eq!(store.0.lock().unwrap().writes, writes + 1);
	drop(server);
	let mut restored = PersistentServer::restore(store).unwrap();
	let sent = restored
		.encrypt_message_outcome(b"next", kid)
		.unwrap()
		.into_option()
		.unwrap();
	assert_eq!(sent.seq, before + 2);
	assert_eq!(beacon.decrypt_message(&sent).unwrap().plaintext, b"next");
}

#[test]
fn persistence_errors_never_release_an_explicit_outcome() {
	for flavor in 0..3 {
		for published in [false, true] {
			let (mut server, _beacon, kid, store) = persistent_pair();
			let head = server.head();
			let sequence = server.ratchet_status(kid).unwrap().send_sequence();
			store.0.lock().unwrap().fail = Some((PersistenceError::CommitUnknown, published));
			let result = match flavor {
				0 => server
					.encrypt_message_outcome(b"message", kid)
					.map(|o| o.map(|_| ())),
				1 => server
					.encrypt_and_update_outcome(b"message", kid)
					.map(|o| o.map(|_| ())),
				_ => server
					.encrypt_and_update_json_outcome(b"message", kid)
					.map(|o| o.map(|_| ())),
			};
			assert_eq!(result.err(), Some(PersistenceError::CommitUnknown));
			assert!(server.is_poisoned());
			assert_eq!(server.head(), head);
			assert_eq!(
				server.encrypt_message_outcome(b"blocked", kid).err(),
				Some(PersistenceError::Poisoned)
			);
			drop(server);
			let restored = PersistentServer::restore(store).unwrap();
			assert_eq!(
				restored.ratchet_status(kid).unwrap().send_sequence(),
				sequence + u64::from(published)
			);
		}
	}
}

#[test]
fn row_and_cached_conveniences_release_typed_committed_results() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("rows.sqlite");
	let lineage = SnapshotLineage::from_bytes([0x51; 32]);
	let mut rows = RowServer::create(
		19,
		Some(&[7; 32]),
		Some(&[8; 32]),
		sqlite::SqliteRowStore::open(&path).unwrap(),
		lineage,
	)
	.unwrap();
	let mut beacon = Beacon::new(19, rows.identity_pk().as_bytes(), &rows.mldsa_public_key());
	let request = beacon.get_registration_bundle().unwrap();
	let response = rows.register_beacon(&request, None).unwrap().unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	let kid = response.kid;
	assert!(matches!(
		rows.encrypt_message_outcome(b"", kid).unwrap(),
		SendOutcome::Rejected
	));
	let outcome =
		fail_frame_write(2, 19, || rows.encrypt_message_outcome(b"payload", kid)).unwrap();
	assert!(matches!(outcome, SendOutcome::ConsumedWithoutOutput));
	let sent = rows
		.encrypt_message_outcome(b"first", kid)
		.unwrap()
		.into_option()
		.unwrap();
	assert_eq!(sent.sequence(), 3);
	assert_eq!(
		beacon.decrypt_message(sent.data()).unwrap().plaintext,
		b"first"
	);
	let mut cached = CachedRowServer::from_server(rows, 1);
	assert!(matches!(
		cached.encrypt_message_outcome(b"", kid).unwrap(),
		SendOutcome::Rejected
	));
	let outcome =
		fail_frame_write(4, 19, || cached.encrypt_message_outcome(b"payload", kid)).unwrap();
	assert!(matches!(outcome, SendOutcome::ConsumedWithoutOutput));
	drop(cached);
	let mut restored =
		RowServer::open(sqlite::SqliteRowStore::open(&path).unwrap(), lineage).unwrap();
	let sent = restored
		.encrypt_message_outcome(b"second", kid)
		.unwrap()
		.into_option()
		.unwrap();
	assert_eq!(sent.sequence(), 5);
	assert_eq!(
		beacon.decrypt_message(sent.data()).unwrap().plaintext,
		b"second"
	);
}
