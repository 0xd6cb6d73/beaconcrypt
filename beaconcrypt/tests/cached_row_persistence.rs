// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use std::{
	collections::BTreeMap,
	path::{Path, PathBuf},
	sync::{
		Arc, Barrier,
		atomic::{AtomicBool, AtomicUsize, Ordering},
	},
	thread,
};

use beaconcrypt::{
	Beacon, CachedRowServer, Decrypted, ProviderBeacon, RowError, RowServer, RowStore,
	RowTransaction, SnapshotLineage,
};
use beaconcrypt_parse::{CryptoFrame, decode_frame};
use proptest::{prelude::*, test_runner::FileFailurePersistence};
use rusqlite::Connection;

mod common;
#[path = "../examples/sqlite/optimistic.rs"]
mod optimistic;
use optimistic::OptimisticSqliteRowStore;

const SERVER_ID: u64 = 39;

fn create(path: &Path) -> RowServer<OptimisticSqliteRowStore> {
	let mut lineage = [0; 32];
	libsodium_rs::random::fill_bytes(&mut lineage);
	RowServer::create(
		SERVER_ID,
		Some(&[41; 32]),
		Some(&[42; 32]),
		OptimisticSqliteRowStore::open(path).unwrap(),
		SnapshotLineage::from_bytes(lineage),
	)
	.unwrap()
}

fn register(server: &mut RowServer<OptimisticSqliteRowStore>) -> (Beacon, u64) {
	let mut beacon = Beacon::try_new(
		server.identity_key_kid(),
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
	.unwrap();
	let response = server
		.register_beacon(
			&beacon.get_registration_bundle().unwrap(),
			Some(b"registered"),
		)
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
		.prepare("SELECT key,value FROM beaconcrypt_rows ORDER BY key")
		.unwrap();
	statement
		.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
		.unwrap()
		.collect::<rusqlite::Result<_>>()
		.unwrap()
}

fn corrupt(frame: &[u8]) -> Vec<u8> {
	let original = decode_frame(frame).unwrap();
	let mut ciphertext = original.cipher_text.to_vec();
	ciphertext[0] ^= 1;
	common::encode_frame(CryptoFrame {
		cipher_text: &ciphertext,
		..original
	})
}

#[derive(Default)]
struct Trace {
	loads: AtomicUsize,
	expects: AtomicUsize,
	writes: AtomicUsize,
	fail_before: AtomicBool,
	lose_ack: AtomicBool,
}

impl Trace {
	fn take_counts(&self) -> (usize, usize, usize) {
		(
			self.loads.swap(0, Ordering::SeqCst),
			self.expects.swap(0, Ordering::SeqCst),
			self.writes.swap(0, Ordering::SeqCst),
		)
	}
}

struct TracedStore {
	inner: OptimisticSqliteRowStore,
	trace: Arc<Trace>,
}
struct TracedTransaction<'a> {
	inner: &'a mut dyn RowTransaction,
	trace: &'a Trace,
}

impl RowTransaction for TracedTransaction<'_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.trace.loads.fetch_add(1, Ordering::SeqCst);
		self.inner.load(key)
	}
	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.trace.writes.fetch_add(1, Ordering::SeqCst);
		self.inner.store(key, value)
	}
	fn expect(&mut self, key: &[u8], value: Option<&[u8]>) -> Result<(), RowError> {
		self.trace.expects.fetch_add(1, Ordering::SeqCst);
		self.inner.expect(key, value)
	}
}

impl RowStore for TracedStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		self.inner.transaction(&mut |inner| {
			operation(&mut TracedTransaction {
				inner,
				trace: &self.trace,
			})?;
			if self.trace.fail_before.swap(false, Ordering::SeqCst) {
				return Err(RowError::Storage("rollback before commit".into()));
			}
			Ok(())
		})?;
		if self.trace.lose_ack.swap(false, Ordering::SeqCst) {
			return Err(RowError::Storage("lost durable acknowledgement".into()));
		}
		Ok(())
	}
}

fn cached(
	path: &Path,
	lineage: SnapshotLineage,
	capacity: usize,
) -> (CachedRowServer<TracedStore>, Arc<Trace>) {
	let trace = Arc::new(Trace::default());
	let server = CachedRowServer::open(
		TracedStore {
			inner: OptimisticSqliteRowStore::open(path).unwrap(),
			trace: Arc::clone(&trace),
		},
		lineage,
		capacity,
	)
	.unwrap();
	assert_eq!(trace.take_counts(), (1, 0, 0));
	(server, trace)
}

#[test]
fn warm_peer_uses_expect_and_other_peer_writes_do_not_conflict() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut owner = create(&path);
	let (mut first, first_id) = register(&mut owner);
	let (mut second, second_id) = register(&mut owner);
	let (mut server, trace) = cached(&path, owner.lineage(), 2);
	first
		.decrypt_message(
			&server
				.encrypt_message(b"cold", first_id)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	assert_eq!(trace.take_counts(), (1, 0, 1));
	second
		.decrypt_message(
			&owner
				.encrypt_message(b"independent", second_id)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	let before = rows(&path);
	first
		.decrypt_message(
			&server
				.encrypt_message(b"warm", first_id)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	assert_eq!(trace.take_counts(), (0, 1, 1));
	let after = rows(&path);
	assert_eq!(before.len(), after.len());
	assert_eq!(
		before
			.iter()
			.filter(|(key, value)| after.get(*key) != Some(*value))
			.count(),
		1
	);
	assert_eq!(server.cached_peer_count(), 1);
}

#[test]
fn competing_writer_invalidates_candidate_then_reload_recovers() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut owner = create(&path);
	let (mut beacon, kid) = register(&mut owner);
	let (mut server, trace) = cached(&path, owner.lineage(), 2);
	beacon
		.decrypt_message(
			&server
				.encrypt_message(b"warm", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	trace.take_counts();
	beacon
		.decrypt_message(
			&owner
				.encrypt_message(b"other writer", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	let before = rows(&path);
	assert!(matches!(
		server.encrypt_message(b"loser", kid),
		Err(RowError::Conflict)
	));
	assert_eq!(trace.take_counts(), (0, 1, 1));
	assert_eq!(rows(&path), before);
	assert_eq!(server.cached_peer_count(), 0);
	let output = server.encrypt_message(b"reloaded", kid).unwrap().unwrap();
	assert_eq!(
		beacon
			.decrypt_message(&output.ciphertext)
			.unwrap()
			.plaintext,
		b"reloaded"
	);
	assert_eq!(trace.take_counts(), (1, 0, 1));
}

#[test]
fn rejected_receive_and_cached_key_consumption_validate_the_predecessor() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut owner = create(&path);
	let (mut beacon, _) = register(&mut owner);
	let (mut server, trace) = cached(&path, owner.lineage(), 1);
	let early = beacon.encrypt_message(b"early").unwrap();
	let later = beacon.encrypt_message(b"later").unwrap();
	assert_eq!(
		server
			.decrypt_message(&later.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"later"
	);
	let before = rows(&path);
	assert!(
		server
			.decrypt_message(&corrupt(&early.ciphertext))
			.unwrap()
			.is_none()
	);
	assert_eq!(rows(&path), before);
	assert_eq!(server.cached_peer_count(), 1);
	assert_eq!(
		owner
			.decrypt_message(&early.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"early"
	);
	trace.take_counts();
	let committed = rows(&path);
	// The old cached receive would reject this replay without writing. Its stale read still fails.
	assert!(matches!(
		server.decrypt_message(&later.ciphertext),
		Err(RowError::Conflict)
	));
	assert_eq!(trace.take_counts(), (0, 1, 0));
	assert_eq!(rows(&path), committed);
	assert_eq!(server.cached_peer_count(), 0);
	assert!(server.decrypt_message(&early.ciphertext).unwrap().is_none());
	assert_eq!(trace.take_counts(), (1, 0, 0));
}

#[test]
fn rollback_and_unknown_commit_never_retain_tentative_cache_or_lose_the_receipt() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut owner = create(&path);
	let (mut beacon, kid) = register(&mut owner);
	let (mut server, trace) = cached(&path, owner.lineage(), 2);
	beacon
		.decrypt_message(
			&server
				.encrypt_message(b"warm", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	let frame = beacon.encrypt_message(b"exact durable result").unwrap();
	let before = rows(&path);
	trace.fail_before.store(true, Ordering::SeqCst);
	assert!(server.decrypt_message(&frame.ciphertext).is_err());
	assert_eq!(rows(&path), before);
	assert_eq!(server.cached_peer_count(), 0);
	trace.lose_ack.store(true, Ordering::SeqCst);
	assert!(
		server
			.transaction(|session| {
				assert!(session.load_application(b"request").unwrap().is_none());
				let output = session.decrypt_message(&frame.ciphertext)?.message.unwrap();
				session.store_application(b"request", output.data())?;
				Ok(output.data().to_vec())
			})
			.is_err()
	);
	assert_eq!(server.cached_peer_count(), 0);
	assert_ne!(rows(&path), before);
	trace.take_counts();
	let recovered = server
		.transaction(|session| session.load_application(b"request"))
		.unwrap()
		.unwrap();
	assert_eq!(recovered.as_slice(), b"exact durable result");
	assert_eq!(trace.take_counts(), (1, 0, 0));
	assert_eq!(server.cached_peer_count(), 0);
	assert!(server.decrypt_message(&frame.ciphertext).unwrap().is_none());
	let next = beacon.encrypt_message(b"next").unwrap();
	assert_eq!(
		server
			.decrypt_message(&next.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"next"
	);
}

#[test]
fn concurrent_cached_workers_publish_one_successor() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut owner = create(&path);
	let (mut beacon, kid) = register(&mut owner);
	let frame = beacon.encrypt_message(b"prime receive").unwrap().ciphertext;
	owner.decrypt_message(&frame).unwrap().unwrap();
	let lineage = owner.lineage();
	let barrier = Arc::new(Barrier::new(2));
	let handles: Vec<_> = (0..2)
		.map(|_| {
			let path = path.clone();
			let barrier = Arc::clone(&barrier);
			let frame = frame.clone();
			thread::spawn(move || {
				let (mut server, _) = cached(&path, lineage, 1);
				assert!(server.decrypt_message(&frame).unwrap().is_none());
				assert_eq!(server.cached_peer_count(), 1);
				barrier.wait();
				server.encrypt_message(b"one winner", kid)
			})
		})
		.collect();
	let results: Vec<_> = handles
		.into_iter()
		.map(|handle| handle.join().unwrap())
		.collect();
	assert_eq!(
		results
			.iter()
			.filter(|result| matches!(result, Err(RowError::Conflict)))
			.count(),
		1
	);
	let winner = results.into_iter().find_map(Result::ok).unwrap().unwrap();
	assert_eq!(
		beacon
			.decrypt_message(&winner.ciphertext)
			.unwrap()
			.plaintext,
		b"one winner"
	);
}

#[test]
fn optimistic_adapter_validates_read_only_absence_empty_values_and_atomicity() {
	let directory = tempfile::tempdir().unwrap();
	let path = directory.path().join("state.sqlite");
	let mut reader = OptimisticSqliteRowStore::open(&path).unwrap();
	let mut writer = OptimisticSqliteRowStore::open(&path).unwrap();
	writer
		.transaction(&mut |tx| tx.store(b"authorization", b"allow"))
		.unwrap();
	assert_eq!(
		reader.transaction(&mut |tx| {
			tx.expect(b"authorization", Some(b"allow"))?;
			writer.transaction(&mut |tx| tx.store(b"authorization", b"revoked"))?;
			tx.store(b"output", b"must not commit")
		}),
		Err(RowError::Conflict)
	);
	assert!(!rows(&path).contains_key(b"output".as_slice()));
	assert_eq!(
		reader.transaction(&mut |tx| {
			assert!(tx.load(b"new request")?.is_none());
			writer.transaction(&mut |tx| tx.store(b"new request", b""))?;
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(
		reader.transaction(&mut |tx| tx.expect(b"new request", None)),
		Err(RowError::Conflict)
	);
	reader
		.transaction(&mut |tx| {
			tx.expect(b"new request", Some(b""))?;
			assert_eq!(tx.load(b"new request")?, Some(Vec::new()));
			tx.store(b"new request", b"updated")?;
			tx.expect(b"new request", Some(b"updated"))?;
			assert_eq!(tx.load(b"new request")?, Some(b"updated".to_vec()));
			Ok(())
		})
		.unwrap();
	let before = rows(&path);
	assert_eq!(
		reader.transaction(&mut |tx| {
			tx.expect(b"new request", Some(b"updated"))?;
			assert_eq!(tx.expect(b"new request", None), Err(RowError::Conflict));
			assert_eq!(
				tx.store(b"ignored error", b"must not commit"),
				Err(RowError::Conflict)
			);
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(rows(&path), before);
}

#[derive(Clone, Debug)]
enum Command {
	Queue(usize, Vec<u8>),
	Deliver(usize, usize, bool),
	Send(usize, Vec<u8>, bool),
	Clear,
	Reopen,
}

fn command() -> impl Strategy<Value = Command> {
	prop_oneof![
		4 => (0usize..3, proptest::collection::vec(any::<u8>(), 1..65)).prop_map(|(peer, bytes)| Command::Queue(peer, bytes)),
		6 => (0usize..3, any::<usize>(), any::<bool>()).prop_map(|(peer, index, damage)| Command::Deliver(peer, index, damage)),
		4 => (0usize..3, proptest::collection::vec(any::<u8>(), 1..65), any::<bool>()).prop_map(|(peer, bytes, external)| Command::Send(peer, bytes, external)),
		1 => Just(Command::Clear),
		1 => Just(Command::Reopen),
	]
}

struct History {
	path: PathBuf,
	server: CachedRowServer<OptimisticSqliteRowStore>,
	beacons: Vec<Beacon>,
	kids: Vec<u64>,
	frames: Vec<Vec<Vec<u8>>>,
}

impl History {
	fn new(path: PathBuf, capacity: usize) -> Self {
		let mut server = create(&path);
		let peers: Vec<_> = (0..3).map(|_| register(&mut server)).collect();
		let (beacons, kids) = peers.into_iter().unzip();
		Self {
			path,
			server: CachedRowServer::from_server(server, capacity),
			beacons,
			kids,
			frames: vec![Vec::new(); 3],
		}
	}

	fn run(&mut self, command: &Command) -> Option<(Vec<u8>, u64, u64)> {
		match command {
			Command::Queue(peer, bytes) => {
				self.frames[*peer].push(
					self.beacons[*peer]
						.encrypt_message(bytes)
						.unwrap()
						.ciphertext,
				);
				None
			}
			Command::Deliver(peer, index, damage) => {
				let frames = &self.frames[*peer];
				if frames.is_empty() {
					return None;
				}
				let bytes = &frames[index % frames.len()];
				let damaged;
				let bytes = if *damage {
					damaged = corrupt(bytes);
					&damaged
				} else {
					bytes
				};
				let result = self.server.decrypt_message(bytes);
				let result = if matches!(result, Err(RowError::Conflict)) {
					assert_eq!(self.server.cached_peer_count(), 0);
					self.server.decrypt_message(bytes)
				} else {
					result
				};
				result.unwrap().map(
					|Decrypted {
					     plaintext,
					     key_id,
					     seq,
					 }| (plaintext, key_id, seq),
				)
			}
			Command::Send(peer, bytes, external) => {
				let result = if *external {
					let mut other = RowServer::open(
						OptimisticSqliteRowStore::open(&self.path).unwrap(),
						self.server.lineage(),
					)
					.unwrap();
					other.encrypt_message(bytes, self.kids[*peer])
				} else {
					let result = self.server.encrypt_message(bytes, self.kids[*peer]);
					if matches!(result, Err(RowError::Conflict)) {
						assert_eq!(self.server.cached_peer_count(), 0);
						self.server.encrypt_message(bytes, self.kids[*peer])
					} else {
						result
					}
				};
				let output = result.unwrap().unwrap();
				let plaintext = self.beacons[*peer]
					.decrypt_message(&output.ciphertext)
					.unwrap();
				assert_eq!(plaintext.plaintext, *bytes);
				Some((plaintext.plaintext, output.key_id, output.seq))
			}
			Command::Clear => {
				self.server.clear_cache();
				None
			}
			Command::Reopen => {
				self.server = CachedRowServer::open(
					OptimisticSqliteRowStore::open(&self.path).unwrap(),
					self.server.lineage(),
					self.server.cache_capacity(),
				)
				.unwrap();
				assert_eq!(self.server.cached_peer_count(), 0);
				None
			}
		}
	}
}

fn config() -> ProptestConfig {
	ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok()
			.and_then(|value| value.parse().ok())
			.unwrap_or(24),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/proptest-regressions/cached_row_persistence.txt"
		)))),
		..ProptestConfig::default()
	}
}

proptest! {
	#![proptest_config(config())]
	#[test]
	fn generated_commit_failures_recover_exact_receipts_without_repeating_committed_crypto(
		capacity in 0usize..4,
		steps in proptest::collection::vec((0u8..3, any::<bool>(), proptest::collection::vec(any::<u8>(), 1..65)), 1..17),
	) {
		let directory = tempfile::tempdir().unwrap();
		let path = directory.path().join("faults.sqlite");
		let mut owner = create(&path);
		let (mut beacon, kid) = register(&mut owner);
		let (mut server, trace) = cached(&path, owner.lineage(), capacity);
		for (index, (fault, clear, plaintext)) in steps.iter().enumerate() {
			if *clear { server.clear_cache(); }
			let before = rows(&path);
			let request = (index as u64).to_le_bytes();
			let mut native_calls = 0;
			let mut operation = |session: &mut beaconcrypt::RowSession<'_>| {
				if let Some(receipt) = session.load_application(&request)? {
					return Ok(receipt.to_vec());
				}
				native_calls += 1;
				let pending = session.encrypt_message(plaintext, kid)?.message.unwrap();
				session.store_application(&request, pending.data())?;
				Ok(pending.data().to_vec())
			};
			trace.fail_before.store(*fault == 1, Ordering::SeqCst);
			trace.lose_ack.store(*fault == 2, Ordering::SeqCst);
			let first = server.transaction(&mut operation);
			let ciphertext = if *fault == 0 {
				first.unwrap()
			} else {
				prop_assert!(first.is_err());
				prop_assert_eq!(server.cached_peer_count(), 0);
				if *fault == 1 { prop_assert_eq!(rows(&path), before); }
				else { prop_assert_ne!(rows(&path), before); }
				server.transaction(&mut operation).unwrap()
			};
			prop_assert_eq!(native_calls, if *fault == 1 { 2 } else { 1 });
			let output = beacon.decrypt_message(&ciphertext).unwrap();
			prop_assert_eq!(output.plaintext.as_slice(), plaintext.as_slice());
			prop_assert_eq!(output.seq, index as u64 + 2);
			let receipt = server.transaction(|session| session.load_application(&request)).unwrap().unwrap();
			prop_assert_eq!(receipt.as_slice(), ciphertext.as_slice());
		}
	}

	#[test]
	fn cached_histories_match_uncached_under_reordering_eviction_and_competing_writers(
		capacity in 0usize..5,
		commands in proptest::collection::vec(command(), 1..33),
	) {
		let directory = tempfile::tempdir().unwrap();
		let mut reference = History::new(directory.path().join("reference.sqlite"), 0);
		let mut cached = History::new(directory.path().join("cached.sqlite"), capacity);
		// Make delivery and replay commands meaningful even after shrinking away all generated sends.
		for peer in 0..3 {
			for payload in [b"first".to_vec(), b"second".to_vec()] {
				let command = Command::Queue(peer, payload);
				reference.run(&command); cached.run(&command);
			}
		}
		for (step, command) in commands.iter().enumerate() {
			prop_assert_eq!(cached.run(command), reference.run(command), "step {}: {:?}", step, command);
			prop_assert!(cached.server.cached_peer_count() <= capacity);
		}
		// Drain in reverse order to exercise persisted skipped keys, then verify every replay rejects.
		for peer in 0..3 {
			for index in (0..reference.frames[peer].len()).rev() {
				let command = Command::Deliver(peer, index, false);
				prop_assert_eq!(cached.run(&command), reference.run(&command));
				prop_assert_eq!(cached.run(&command), None);
				prop_assert_eq!(reference.run(&command), None);
			}
		}
	}
}
