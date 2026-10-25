use std::{
	collections::BTreeMap,
	path::Path,
	sync::{
		Arc, Barrier, Mutex,
		atomic::{AtomicBool, Ordering},
	},
	thread,
};

use beaconcrypt::{
	Beacon, ProviderBeacon, RowError, RowServer, RowStore, RowTransaction, SnapshotLineage,
};
use rusqlite::Connection;

#[path = "../examples/sqlite/store.rs"]
mod store;
use store::SqliteRowStore;

const LINEAGE: SnapshotLineage = SnapshotLineage::from_bytes([0x31; 32]);
const SERVER_ID: u64 = 17;

fn create(path: &Path) -> RowServer<SqliteRowStore> {
	RowServer::create(
		SERVER_ID,
		Some(&[0x32; 32]),
		Some(&[0x33; 32]),
		SqliteRowStore::open(path).unwrap(),
		LINEAGE,
	)
	.unwrap()
}

fn open(path: &Path) -> RowServer<SqliteRowStore> {
	RowServer::open(SqliteRowStore::open(path).unwrap(), LINEAGE).unwrap()
}

fn beacon<S: RowStore>(server: &RowServer<S>) -> Beacon {
	Beacon::try_new(
		server.identity_key_kid(),
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
	.unwrap()
}

fn register<S: RowStore>(server: &mut RowServer<S>) -> (Beacon, u64) {
	let mut beacon = beacon(server);
	let registration = beacon.get_registration_bundle().unwrap();
	let response = server
		.register_beacon(&registration, Some(b"registered"))
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		b"registered"
	);
	(beacon, response.kid)
}

fn rows(path: &Path) -> BTreeMap<Vec<u8>, Vec<u8>> {
	let connection = Connection::open(path).unwrap();
	let mut statement = connection
		.prepare("SELECT key, value FROM beaconcrypt_rows ORDER BY key")
		.unwrap();
	statement
		.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
		.unwrap()
		.collect::<rusqlite::Result<_>>()
		.unwrap()
}

fn changed_rows(before: &BTreeMap<Vec<u8>, Vec<u8>>, after: &BTreeMap<Vec<u8>, Vec<u8>>) -> usize {
	assert_eq!(before.len(), after.len());
	before
		.iter()
		.filter(|(key, value)| after.get(*key) != Some(*value))
		.count()
}

#[derive(Default)]
struct Accesses {
	reads: Vec<Vec<u8>>,
	writes: Vec<Vec<u8>>,
}

struct TracedStore {
	inner: SqliteRowStore,
	accesses: Arc<Mutex<Accesses>>,
}

struct TracedTransaction<'a> {
	inner: &'a mut dyn RowTransaction,
	accesses: &'a Mutex<Accesses>,
}

impl RowTransaction for TracedTransaction<'_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.accesses.lock().unwrap().reads.push(key.to_vec());
		self.inner.load(key)
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.accesses.lock().unwrap().writes.push(key.to_vec());
		self.inner.store(key, value)
	}
}

impl RowStore for TracedStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		self.inner.transaction(&mut |transaction| {
			operation(&mut TracedTransaction {
				inner: transaction,
				accesses: &self.accesses,
			})
		})
	}
}

fn take_peer_access(accesses: &Mutex<Accesses>, expect_write: bool) -> Vec<u8> {
	let accesses = std::mem::take(&mut *accesses.lock().unwrap());
	assert_eq!(accesses.reads.len(), 1, "only one peer row may be loaded");
	if expect_write {
		assert_eq!(accesses.writes, accesses.reads);
	} else {
		assert!(accesses.writes.is_empty());
	}
	accesses.reads.into_iter().next().unwrap()
}

#[test]
fn traffic_loads_only_its_peer_and_cached_receives_advance_the_row_revision() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("accesses.sqlite");
	let mut initial = create(&path);
	let (mut beacon, kid) = register(&mut initial);
	register(&mut initial);
	let accesses = Arc::new(Mutex::new(Accesses::default()));
	let mut server = RowServer::open(
		TracedStore {
			inner: SqliteRowStore::open(&path).unwrap(),
			accesses: Arc::clone(&accesses),
		},
		LINEAGE,
	)
	.unwrap();
	assert_eq!(
		accesses.lock().unwrap().reads.len(),
		1,
		"open loads only identity"
	);
	assert!(accesses.lock().unwrap().writes.is_empty());
	*accesses.lock().unwrap() = Accesses::default();

	let response = server.encrypt_message(b"one peer", kid).unwrap().unwrap();
	beacon.decrypt_message(&response.ciphertext).unwrap();
	let peer_key = take_peer_access(&accesses, true);
	let first = beacon.encrypt_message(b"one").unwrap();
	let second = beacon.encrypt_message(b"two").unwrap();
	server.decrypt_message(&second.ciphertext).unwrap().unwrap();
	assert_eq!(take_peer_access(&accesses, true), peer_key);
	let before = rows(&path)[&peer_key].clone();
	assert_eq!(
		server
			.decrypt_message(&first.ciphertext)
			.unwrap()
			.unwrap()
			.seq,
		1
	);
	assert_eq!(take_peer_access(&accesses, true), peer_key);
	let after = rows(&path)[&peer_key].clone();
	// Inspect the documented v1 row framing: cached-key consumption changes the independent row
	// revision even though the peer's receive frontier remains two.
	let generation = |bytes: &[u8]| u64::from_le_bytes(bytes[17..25].try_into().unwrap());
	let payload = |bytes: &[u8]| {
		let key_len = u16::from_le_bytes(bytes[57..59].try_into().unwrap()) as usize;
		serde_json::from_slice::<serde_json::Value>(&bytes[59 + key_len..]).unwrap()
	};
	assert_eq!(generation(&after), generation(&before) + 1);
	let before = payload(&before);
	let after = payload(&after);
	assert_eq!(before["ratchet"]["recv_ctr"], 2);
	assert_eq!(after["ratchet"]["recv_ctr"], 2);
	assert_eq!(before["ratchet"]["recv_past"].as_object().unwrap().len(), 1);
	assert!(
		after["ratchet"]["recv_past"]
			.as_object()
			.unwrap()
			.is_empty()
	);
	assert!(server.decrypt_message(&first.ciphertext).unwrap().is_none());
	assert_eq!(take_peer_access(&accesses, false), peer_key);
}

#[test]
fn sqlite_restart_loads_identity_and_only_replaces_the_selected_peer() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("server.sqlite");
	let mut server = create(&path);
	let (mut first, first_kid) = register(&mut server);
	let (mut second, second_kid) = register(&mut server);
	assert_eq!(first_kid, SERVER_ID + 1);
	assert_eq!(second_kid, SERVER_ID + 2);
	let before = rows(&path);
	drop(server);
	let mut server = open(&path);
	assert_eq!(rows(&path), before, "opening must not activate every peer");

	let encrypted = server
		.encrypt_message(b"first", first_kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		first
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.plaintext,
		b"first"
	);
	assert_eq!(changed_rows(&before, &rows(&path)), 1);
	let before = rows(&path);
	let encrypted = second.encrypt_message(b"second").unwrap();
	let received = server
		.decrypt_message(&encrypted.ciphertext)
		.unwrap()
		.unwrap();
	assert_eq!(received.plaintext, b"second");
	assert_eq!(received.key_id, second_kid);
	assert_eq!(changed_rows(&before, &rows(&path)), 1);

	drop(server);
	let mut reopened = open(&path);
	assert!(
		reopened
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.is_none()
	);
	let response = reopened
		.encrypt_message(b"after restart", second_kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		second
			.decrypt_message(&response.ciphertext)
			.unwrap()
			.plaintext,
		b"after restart"
	);
}

#[test]
fn rejected_and_cached_receives_have_the_same_durable_effect_as_the_protocol() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("receive.sqlite");
	let mut server = create(&path);
	let (mut beacon, _) = register(&mut server);
	let first = beacon.encrypt_message(b"one").unwrap();
	let second = beacon.encrypt_message(b"two").unwrap();
	let third = beacon.encrypt_message(b"three").unwrap();
	assert_eq!(
		server
			.decrypt_message(&third.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"three"
	);
	let before = rows(&path);
	for input in [
		&[][..],
		b"malformed".as_slice(),
		third.ciphertext.as_slice(),
	] {
		assert!(server.decrypt_message(input).unwrap().is_none());
		assert_eq!(rows(&path), before);
	}
	let mut corrupted = first.ciphertext.clone();
	*corrupted.last_mut().unwrap() ^= 1;
	assert!(server.decrypt_message(&corrupted).unwrap().is_none());
	assert_eq!(rows(&path), before);
	assert_eq!(
		server
			.decrypt_message(&first.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"one"
	);
	assert_eq!(changed_rows(&before, &rows(&path)), 1);
	drop(server);
	let mut server = open(&path);
	assert!(server.decrypt_message(&first.ciphertext).unwrap().is_none());
	assert_eq!(
		server
			.decrypt_message(&second.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"two"
	);
}

#[test]
fn failed_registration_response_retains_replay_marker_after_restart() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("registration.sqlite");
	let mut server = create(&path);
	let mut beacon = beacon(&server);
	let request = beacon.get_registration_bundle().unwrap();
	let before = rows(&path);
	assert!(
		server
			.register_beacon(&request, Some(b""))
			.unwrap()
			.is_none()
	);
	let after = rows(&path);
	assert_eq!(after.len(), before.len() + 1);
	for (key, value) in before {
		assert_eq!(
			after.get(&key),
			Some(&value),
			"allocator and identity remain unchanged"
		);
	}
	drop(server);
	let mut server = open(&path);
	assert!(
		server
			.register_beacon(&request, Some(b"retry"))
			.unwrap()
			.is_none()
	);
	assert_eq!(rows(&path), after);
	let (_, kid) = register(&mut server);
	assert_eq!(kid, SERVER_ID + 1);
}

#[test]
fn independent_connections_can_mutate_different_peers_without_global_fencing() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("workers.sqlite");
	let mut server = create(&path);
	let (mut first, first_kid) = register(&mut server);
	let (mut second, second_kid) = register(&mut server);
	let mut worker_one = open(&path);
	let mut worker_two = open(&path);
	let barrier = Arc::new(Barrier::new(2));
	let worker_barrier = Arc::clone(&barrier);
	let one = thread::spawn(move || {
		worker_barrier.wait();
		worker_one
			.encrypt_message(b"worker one", first_kid)
			.unwrap()
			.unwrap()
	});
	let two = thread::spawn(move || {
		barrier.wait();
		worker_two
			.encrypt_message(b"worker two", second_kid)
			.unwrap()
			.unwrap()
	});
	assert_eq!(
		first
			.decrypt_message(&one.join().unwrap().ciphertext)
			.unwrap()
			.plaintext,
		b"worker one"
	);
	assert_eq!(
		second
			.decrypt_message(&two.join().unwrap().ciphertext)
			.unwrap()
			.plaintext,
		b"worker two"
	);
	// The original server handle also remains usable after both independent commits.
	assert!(
		server
			.encrypt_message(b"original owner", first_kid)
			.unwrap()
			.is_some()
	);
}

#[test]
fn competing_receives_publish_plaintext_once() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("race.sqlite");
	let mut server = create(&path);
	let (mut beacon, _) = register(&mut server);
	let encrypted = beacon.encrypt_message(b"only once").unwrap();
	let mut one = open(&path);
	let mut two = open(&path);
	let barrier = Arc::new(Barrier::new(2));
	let first_barrier = Arc::clone(&barrier);
	let first_input = encrypted.ciphertext.clone();
	let first = thread::spawn(move || {
		first_barrier.wait();
		one.decrypt_message(&first_input).unwrap()
	});
	let second = thread::spawn(move || {
		barrier.wait();
		two.decrypt_message(&encrypted.ciphertext).unwrap()
	});
	let outputs = [first.join().unwrap(), second.join().unwrap()];
	assert_eq!(outputs.iter().filter(|output| output.is_some()).count(), 1);
	assert_eq!(
		outputs.into_iter().flatten().next().unwrap().plaintext,
		b"only once"
	);
}

#[test]
fn concurrent_replays_establish_only_one_peer_and_consume_one_id() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("registration-replay-race.sqlite");
	let server = create(&path);
	let mut beacon = beacon(&server);
	let request = beacon.get_registration_bundle().unwrap();
	let first_request = request.clone();
	let before = rows(&path);
	let mut one = open(&path);
	let mut two = open(&path);
	let barrier = Arc::new(Barrier::new(2));
	let first_barrier = Arc::clone(&barrier);
	let first = thread::spawn(move || {
		first_barrier.wait();
		one.register_beacon(&first_request, Some(b"accepted once"))
			.unwrap()
	});
	let replay = request.clone();
	let second = thread::spawn(move || {
		barrier.wait();
		two.register_beacon(&replay, Some(b"accepted once"))
			.unwrap()
	});
	let outputs = [first.join().unwrap(), second.join().unwrap()];
	assert_eq!(outputs.iter().filter(|output| output.is_some()).count(), 1);
	let response = outputs.into_iter().flatten().next().unwrap();
	assert_eq!(response.kid, SERVER_ID + 1);
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		b"accepted once"
	);
	let after = rows(&path);
	assert_eq!(after.len(), before.len() + 2, "one marker and one peer");
	assert_eq!(
		before
			.iter()
			.filter(|(key, value)| after.get(*key) != Some(*value))
			.count(),
		1,
		"only the allocator changes among existing rows"
	);
	let mut reopened = open(&path);
	assert!(
		reopened
			.register_beacon(&request, Some(b"replay after restart"))
			.unwrap()
			.is_none()
	);
	assert_eq!(rows(&path), after);
	let frame = beacon.encrypt_message(b"the sole peer works").unwrap();
	assert_eq!(
		reopened
			.decrypt_message(&frame.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"the sole peer works"
	);
	assert_eq!(register(&mut reopened).1, SERVER_ID + 2);
}

#[test]
fn concurrent_registrations_allocate_distinct_ids_and_persist_both_peers() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("registration-race.sqlite");
	let server = create(&path);
	let mut first_beacon = beacon(&server);
	let mut second_beacon = beacon(&server);
	let first_request = first_beacon.get_registration_bundle().unwrap();
	let second_request = second_beacon.get_registration_bundle().unwrap();
	let mut one = open(&path);
	let mut two = open(&path);
	let barrier = Arc::new(Barrier::new(2));
	let first_barrier = Arc::clone(&barrier);
	let first = thread::spawn(move || {
		first_barrier.wait();
		one.register_beacon(&first_request, Some(b"first"))
			.unwrap()
			.unwrap()
	});
	let second = thread::spawn(move || {
		barrier.wait();
		two.register_beacon(&second_request, Some(b"second"))
			.unwrap()
			.unwrap()
	});
	let first = first.join().unwrap();
	let second = second.join().unwrap();
	assert_ne!(first.kid, second.kid);
	let mut assigned = [first.kid, second.kid];
	assigned.sort_unstable();
	assert_eq!(assigned, [SERVER_ID + 1, SERVER_ID + 2]);
	assert_eq!(
		first_beacon.finish_registration(&first.serialized).unwrap(),
		b"first"
	);
	assert_eq!(
		second_beacon
			.finish_registration(&second.serialized)
			.unwrap(),
		b"second"
	);
	let mut server = open(&path);
	for (mut beacon, expected) in [(first_beacon, b"one"), (second_beacon, b"two")] {
		let frame = beacon.encrypt_message(expected).unwrap();
		assert_eq!(
			server
				.decrypt_message(&frame.ciphertext)
				.unwrap()
				.unwrap()
				.plaintext,
			expected
		);
	}
}

#[test]
fn a_full_receive_cache_survives_database_reopen() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("full-cache.sqlite");
	let mut server = create(&path);
	let (mut beacon, _) = register(&mut server);
	let frames = (1..=51u8)
		.map(|value| beacon.encrypt_message(&[value]).unwrap())
		.collect::<Vec<_>>();
	assert_eq!(
		server
			.decrypt_message(&frames[50].ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		[51]
	);
	drop(server);
	let mut server = open(&path);
	// The next contiguous target requires no extra cache entry even with all 50 slots occupied.
	let next = beacon.encrypt_message(b"next").unwrap();
	assert_eq!(
		server
			.decrypt_message(&next.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"next"
	);
	for (index, frame) in frames[..50].iter().enumerate() {
		let plaintext = server
			.decrypt_message(&frame.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext;
		assert_eq!(plaintext, [index as u8 + 1]);
		assert!(server.decrypt_message(&frame.ciphertext).unwrap().is_none());
	}
}

#[test]
fn corrupt_peer_row_is_rejected_without_loading_unrelated_peers() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("corrupt.sqlite");
	let mut server = create(&path);
	let (mut first, first_kid) = register(&mut server);
	let (mut second, second_kid) = register(&mut server);
	let before = rows(&path);
	server
		.encrypt_message(b"identify changed row", first_kid)
		.unwrap()
		.unwrap();
	let after = rows(&path);
	let key = before
		.iter()
		.find(|(key, value)| after.get(*key) != Some(*value))
		.unwrap()
		.0;
	Connection::open(&path)
		.unwrap()
		.execute(
			"UPDATE beaconcrypt_rows SET value = ?1 WHERE key = ?2",
			rusqlite::params![b"invalid row".as_slice(), key],
		)
		.unwrap();
	let damaged = rows(&path);
	let frame = first.encrypt_message(b"must reject").unwrap();
	assert!(matches!(
		server.decrypt_message(&frame.ciphertext),
		Err(RowError::InvalidRow)
	));
	assert_eq!(rows(&path), damaged);
	drop(server);
	let mut server = open(&path);
	let response = server
		.encrypt_message(b"unaffected", second_kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		second
			.decrypt_message(&response.ciphertext)
			.unwrap()
			.plaintext,
		b"unaffected"
	);
	let frame = second.encrypt_message(b"still works").unwrap();
	assert_eq!(
		server
			.decrypt_message(&frame.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"still works"
	);
}

struct FailingStore {
	inner: SqliteRowStore,
	fail: Arc<AtomicBool>,
	after_commit: bool,
}

struct FailingSecondWriteStore {
	inner: SqliteRowStore,
	armed: bool,
}

struct FailingSecondWriteTransaction<'a> {
	inner: &'a mut dyn RowTransaction,
	armed: &'a mut bool,
	writes: usize,
}

impl RowTransaction for FailingSecondWriteTransaction<'_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.inner.load(key)
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.writes += 1;
		if self.writes == 2 && *self.armed {
			*self.armed = false;
			return Err(RowError::Storage("injected peer write failure".into()));
		}
		self.inner.store(key, value)
	}
}

impl RowStore for FailingSecondWriteStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		self.inner.transaction(&mut |transaction| {
			operation(&mut FailingSecondWriteTransaction {
				inner: transaction,
				armed: &mut self.armed,
				writes: 0,
			})
		})
	}
}

#[test]
fn failed_peer_insert_rolls_back_allocator_but_retains_registration_marker() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("registration-peer-write.sqlite");
	let mut initial = create(&path);
	let (_, first_kid) = register(&mut initial);
	let mut beacon = beacon(&initial);
	let request = beacon.get_registration_bundle().unwrap();
	let before = rows(&path);
	let mut server = RowServer::open(
		FailingSecondWriteStore {
			inner: SqliteRowStore::open(&path).unwrap(),
			armed: true,
		},
		LINEAGE,
	)
	.unwrap();
	// The marker transaction has one write. The response transaction writes the allocator first,
	// then fails at the peer insertion, so its earlier allocator write must be rolled back.
	assert_eq!(
		server
			.register_beacon(&request, Some(b"withheld response"))
			.err(),
		Some(RowError::Storage("injected peer write failure".into()))
	);
	let after = rows(&path);
	assert_eq!(after.len(), before.len() + 1, "only the marker survives");
	for (key, value) in before {
		assert_eq!(after.get(&key), Some(&value));
	}
	drop(server);
	let mut reopened = open(&path);
	assert!(
		reopened
			.register_beacon(&request, Some(b"replay after failure"))
			.unwrap()
			.is_none()
	);
	assert_eq!(rows(&path), after);
	assert_eq!(register(&mut reopened).1, first_kid + 1);
}

impl RowStore for FailingStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		let fail = self.fail.swap(false, Ordering::SeqCst);
		self.inner.transaction(&mut |transaction| {
			operation(transaction)?;
			if fail && !self.after_commit {
				return Err(RowError::Storage("injected rollback".into()));
			}
			Ok(())
		})?;
		if fail && self.after_commit {
			return Err(RowError::Storage("commit acknowledgement lost".into()));
		}
		Ok(())
	}
}

#[test]
fn failed_transaction_withholds_plaintext_and_rolls_back_the_row() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("rollback.sqlite");
	let mut server = create(&path);
	let (mut beacon, _) = register(&mut server);
	let encrypted = beacon.encrypt_message(b"withheld").unwrap();
	let fail = Arc::new(AtomicBool::new(false));
	let mut server = RowServer::open(
		FailingStore {
			inner: SqliteRowStore::open(&path).unwrap(),
			fail: Arc::clone(&fail),
			after_commit: false,
		},
		LINEAGE,
	)
	.unwrap();
	let before = rows(&path);
	fail.store(true, Ordering::SeqCst);
	assert!(matches!(
		server.decrypt_message(&encrypted.ciphertext),
		Err(RowError::Storage(_))
	));
	assert_eq!(rows(&path), before);
	assert_eq!(
		server
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"withheld"
	);
}

#[test]
fn unknown_commit_outcome_never_reuses_the_local_predecessor() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("unknown.sqlite");
	let mut server = create(&path);
	let (mut beacon, kid) = register(&mut server);
	let encrypted = beacon
		.encrypt_message(b"committed but not returned")
		.unwrap();
	let fail = Arc::new(AtomicBool::new(false));
	let mut server = RowServer::open(
		FailingStore {
			inner: SqliteRowStore::open(&path).unwrap(),
			fail: Arc::clone(&fail),
			after_commit: true,
		},
		LINEAGE,
	)
	.unwrap();
	let before = rows(&path);
	fail.store(true, Ordering::SeqCst);
	assert!(matches!(
		server.decrypt_message(&encrypted.ciphertext),
		Err(RowError::Storage(_))
	));
	assert_eq!(changed_rows(&before, &rows(&path)), 1);
	assert!(
		server
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.is_none()
	);
	let send_before = rows(&path);
	fail.store(true, Ordering::SeqCst);
	assert!(matches!(
		server.encrypt_message(b"withheld send", kid),
		Err(RowError::Storage(_))
	));
	assert_eq!(changed_rows(&send_before, &rows(&path)), 1);
	let next = server
		.encrypt_message(b"fresh sequence", kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		next.seq, 3,
		"registration and unknown send each consumed a key"
	);
	assert_eq!(
		beacon.decrypt_message(&next.ciphertext).unwrap().plaintext,
		b"fresh sequence"
	);
}

#[test]
fn sqlite_transactions_roll_back_all_rows_and_invoke_the_callback_once() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("atomic.sqlite");
	let mut store = SqliteRowStore::open(&path).unwrap();
	let mut calls = 0;
	let error = store.transaction(&mut |transaction| {
		calls += 1;
		assert!(transaction.load(b"one")?.is_none());
		transaction.store(b"one", b"secret")?;
		transaction.store(b"two", b"other secret")?;
		Err(RowError::Storage("rollback".into()))
	});
	assert!(matches!(error, Err(RowError::Storage(_))));
	assert_eq!(calls, 1);
	assert!(rows(&path).is_empty());
	store
		.transaction(&mut |transaction| {
			transaction.store(b"one", b"first")?;
			transaction.store(b"one", b"replacement")?;
			transaction.store(b"two", b"second")?;
			assert_eq!(
				transaction.load(b"one")?.as_deref(),
				Some(b"replacement".as_slice())
			);
			Ok(())
		})
		.unwrap();
	assert_eq!(
		rows(&path),
		BTreeMap::from([
			(b"one".to_vec(), b"replacement".to_vec()),
			(b"two".to_vec(), b"second".to_vec()),
		])
	);
}

#[test]
fn database_errors_and_duplicate_creation_do_not_replace_identity() {
	let directory = tempfile::tempdir().unwrap();
	assert!(matches!(
		SqliteRowStore::open(directory.path()),
		Err(RowError::Storage(_))
	));
	let path = directory.path().join("create.sqlite");
	assert!(matches!(
		RowServer::open(SqliteRowStore::open(&path).unwrap(), LINEAGE),
		Err(RowError::MissingIdentity)
	));
	let _server = create(&path);
	let before = rows(&path);
	assert!(matches!(
		RowServer::create(0, None, None, SqliteRowStore::open(&path).unwrap(), LINEAGE),
		Err(RowError::Conflict)
	));
	assert_eq!(rows(&path), before);
	let other_lineage = SnapshotLineage::from_bytes([0x41; 32]);
	let mut other = RowServer::create(
		0,
		None,
		None,
		SqliteRowStore::open(&path).unwrap(),
		other_lineage,
	)
	.unwrap();
	let (_, kid) = register(&mut other);
	assert_eq!(kid, 1);
	for (key, value) in before {
		assert_eq!(rows(&path).get(&key), Some(&value));
	}
}
