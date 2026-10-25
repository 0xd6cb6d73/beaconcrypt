// SPDX-License-Identifier: 0BSD

use std::{
	cell::{Cell, RefCell},
	path::PathBuf,
	rc::Rc,
	sync::{Arc, Barrier},
	time::Instant,
};

use beaconcrypt::{
	PersistentServer, RowError, RowStore, RowTransaction, ServerSnapshot, SnapshotHead,
	SnapshotLineage, SnapshotStore,
};

use super::{
	database::{Counters, SqlRowStore, SqlSnapshotStore},
	postgres::{PgFixture, PgRowStore, PgSnapshotStore},
};
use serde_json::{Value, json};

enum Factory {
	Sqlite(PathBuf),
	Postgres(PgFixture),
}
impl Clone for Factory {
	fn clone(&self) -> Self {
		match self {
			Self::Sqlite(p) => Self::Sqlite(p.clone()),
			Self::Postgres(p) => Self::Postgres(p.worker_copy()),
		}
	}
}
impl Factory {
	fn rows(&self) -> Box<dyn RowStore> {
		self.rows_with_counts().0
	}
	fn rows_with_counts(&self) -> (Box<dyn RowStore>, Rc<Counters>) {
		let counts = Rc::new(Counters::default());
		let store: Box<dyn RowStore> = match self {
			Self::Sqlite(p) => Box::new(SqlRowStore::open(p, Rc::clone(&counts)).unwrap()),
			Self::Postgres(p) => {
				Box::new(PgRowStore::open(Rc::new(p.worker_copy()), Rc::clone(&counts)).unwrap())
			}
		};
		(store, counts)
	}
	fn snapshot(&self) -> Box<dyn SnapshotStore> {
		self.snapshot_with_counts().0
	}
	fn snapshot_with_counts(&self) -> (Box<dyn SnapshotStore>, Rc<Counters>) {
		let counts = Rc::new(Counters::default());
		let store: Box<dyn SnapshotStore> = match self {
			Self::Sqlite(p) => Box::new(SqlSnapshotStore::open(p, Rc::clone(&counts)).unwrap()),
			Self::Postgres(p) => Box::new(
				PgSnapshotStore::open(Rc::new(p.worker_copy()), Rc::clone(&counts)).unwrap(),
			),
		};
		(store, counts)
	}
	fn reject_z(&self) {
		match self {Self::Sqlite(p)=>rusqlite::Connection::open(p).unwrap().execute_batch("CREATE TRIGGER reject_z BEFORE INSERT ON peer_rows WHEN NEW.key=x'7a' BEGIN SELECT RAISE(ABORT,'injected failure'); END;").unwrap(),Self::Postgres(p)=>p.reject_z()}
	}
}

fn fixture(pg: bool, operation: impl FnOnce(&Factory)) {
	let directory = tempfile::tempdir().unwrap();
	let owner = if pg {
		libsodium_rs::ensure_init().unwrap();
		let mut bytes = [0; 32];
		libsodium_rs::random::fill_bytes(&mut bytes);
		Some(
			PgFixture::create(
				&std::env::var("BEACONCRYPT_BENCH_POSTGRES").expect("set live PostgreSQL DSN"),
				SnapshotLineage::from_bytes(bytes),
			)
			.unwrap(),
		)
	} else {
		None
	};
	let factory = match &owner {
		Some(p) => Factory::Postgres(p.worker_copy()),
		None => Factory::Sqlite(directory.path().join("rows.sqlite")),
	};
	operation(&factory);
}

fn put(store: &mut dyn RowStore, key: &[u8], value: &[u8]) {
	store.transaction(&mut |tx| tx.store(key, value)).unwrap();
}
fn get(store: &mut dyn RowStore, key: &[u8]) -> Option<Vec<u8>> {
	let mut value = None;
	store
		.transaction(&mut |tx| {
			value = tx.load(key)?;
			Ok(())
		})
		.unwrap();
	value
}

fn empty_and_read_your_writes(f: &Factory) {
	let mut store = f.rows();
	store
		.transaction(&mut |tx| {
			assert_eq!(tx.load(b"empty")?, None);
			tx.store(b"empty", b"")?;
			assert_eq!(tx.load(b"empty")?, Some(vec![]));
			tx.expect(b"empty", Some(b""))?;
			Ok(())
		})
		.unwrap();
	assert_eq!(get(&mut *store, b"empty"), Some(vec![]));
	assert_eq!(
		store.transaction(&mut |tx| tx.expect(b"empty", None)),
		Err(RowError::Conflict)
	);
}

fn stale_multirow_is_atomic(f: &Factory) {
	let mut a = f.rows();
	let mut b = f.rows();
	put(&mut *a, b"a", b"old");
	put(&mut *a, b"b", b"old");
	assert_eq!(
		a.transaction(&mut |tx| {
			assert_eq!(tx.load(b"a")?, Some(b"old".to_vec()));
			tx.expect(b"b", Some(b"old"))?;
			tx.store(b"a", b"candidate")?;
			tx.store(b"c", b"candidate")?;
			put(&mut *b, b"b", b"winner");
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(get(&mut *a, b"a"), Some(b"old".to_vec()));
	assert_eq!(get(&mut *a, b"b"), Some(b"winner".to_vec()));
	assert_eq!(get(&mut *a, b"c"), None);
}

fn absent_and_read_only_conflicts(f: &Factory) {
	let mut a = f.rows();
	let mut b = f.rows();
	assert_eq!(
		a.transaction(&mut |tx| {
			assert_eq!(tx.load(b"missing")?, None);
			put(&mut *b, b"missing", b"");
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(
		a.transaction(&mut |tx| {
			tx.expect(b"missing", Some(b""))?;
			put(&mut *b, b"missing", b"new");
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(get(&mut *a, b"missing"), Some(b"new".to_vec()));
}

fn errors_are_sticky_and_rollback(f: &Factory) {
	let mut a = f.rows();
	assert_eq!(
		a.transaction(&mut |tx| {
			tx.store(b"discard", b"value")?;
			Err(RowError::OutputEncoding)
		}),
		Err(RowError::OutputEncoding)
	);
	assert_eq!(get(&mut *a, b"discard"), None);
	assert_eq!(
		a.transaction(&mut |tx| {
			tx.expect(b"key", None)?;
			assert_eq!(tx.expect(b"key", Some(b"value")), Err(RowError::Conflict));
			assert_eq!(tx.store(b"discard", b"value"), Err(RowError::Conflict));
			assert_eq!(tx.load(b"key"), Err(RowError::Conflict));
			assert_eq!(tx.load(b"other"), Err(RowError::Conflict));
			assert_eq!(tx.expect(b"other", None), Err(RowError::Conflict));
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(get(&mut *a, b"discard"), None);
}

#[test]
fn buffered_failure_stops_cached_reads_fetches_expectations_and_staged_writes() {
	for error in [
		RowError::Conflict,
		RowError::Storage("injected fetch failure".into()),
	] {
		let counts = Counters::default();
		let fetches = Cell::new(0);
		let mut tx = super::buffered::Buffered::new(
			|key: &[u8]| {
				fetches.set(fetches.get() + 1);
				if key == b"bad" {
					Err(error.clone())
				} else {
					Ok(Some(b"original".to_vec()))
				}
			},
			&counts,
		);
		assert_eq!(tx.load(b"read").unwrap(), Some(b"original".to_vec()));
		tx.store(b"staged", b"before").unwrap();
		if error == RowError::Conflict {
			assert_eq!(tx.expect(b"read", Some(b"different")), Err(error.clone()));
		} else {
			assert_eq!(tx.load(b"bad"), Err(error.clone()));
		}
		let prior_fetches = fetches.get();
		let prior_reads = tx.reads.clone();
		let prior_writes = tx.writes.clone();
		for key in [b"read".as_slice(), b"staged", b"uncached"] {
			assert_eq!(tx.load(key), Err(error.clone()));
			assert_eq!(tx.expect(key, None), Err(error.clone()));
			assert_eq!(tx.store(key, b"must not be staged"), Err(error.clone()));
		}
		assert_eq!(fetches.get(), prior_fetches);
		assert_eq!(tx.reads, prior_reads);
		assert_eq!(tx.writes, prior_writes);
		assert_eq!(tx.failure, Some(error));
	}
}

fn database_error_rolls_back_prior_write(f: &Factory) {
	let mut a = f.rows();
	f.reject_z();
	assert!(matches!(
		a.transaction(&mut |tx| {
			tx.store(b"a", b"first")?;
			tx.store(b"z", b"fail")
		}),
		Err(RowError::Storage(_))
	));
	assert_eq!(get(&mut *a, b"a"), None);
	assert_eq!(get(&mut *a, b"z"), None);
}

fn concurrent_conflict(f: &Factory) {
	let mut initial = f.rows();
	put(&mut *initial, b"present", b"initial");
	let barrier = Arc::new(Barrier::new(2));
	let workers = (0..2)
		.map(|i| {
			let factory = f.clone();
			let gate = Arc::clone(&barrier);
			std::thread::spawn(move || {
				let mut store = factory.rows();
				store.transaction(&mut |tx| {
					// Reverse callback order; commit locks must still be globally ordered.
					if i == 0 {
						assert_eq!(tx.load(b"absent")?, None);
						tx.expect(b"present", Some(b"initial"))?;
					} else {
						tx.expect(b"present", Some(b"initial"))?;
						assert_eq!(tx.load(b"absent")?, None);
					}
					tx.store(b"absent", &[i])?;
					tx.store(b"present", &[i])?;
					gate.wait();
					Ok(())
				})
			})
		})
		.collect::<Vec<_>>();
	let outcomes = workers
		.into_iter()
		.map(|worker| worker.join().unwrap())
		.collect::<Vec<_>>();
	assert_eq!(outcomes.iter().filter(|result| result.is_ok()).count(), 1);
	assert_eq!(
		outcomes
			.iter()
			.filter(|result| **result == Err(RowError::Conflict))
			.count(),
		1
	);
	assert_eq!(
		get(&mut *initial, b"absent"),
		get(&mut *initial, b"present")
	);
}

struct Capture(Rc<RefCell<Option<Vec<u8>>>>);
impl SnapshotStore for Capture {
	fn load(&self) -> Option<ServerSnapshot> {
		self.0.borrow().clone().map(ServerSnapshot::from_bytes)
	}
	fn compare_and_swap(&mut self, _: Option<&SnapshotHead>, replacement: &ServerSnapshot) -> bool {
		*self.0.borrow_mut() = Some(replacement.as_bytes().to_vec());
		true
	}
}
fn concurrent_snapshot_cas(f: &Factory) {
	let saved = Rc::new(RefCell::new(None));
	let mut server = PersistentServer::create(
		19,
		Some(&[82; 32]),
		Some(&[83; 32]),
		Capture(Rc::clone(&saved)),
	)
	.unwrap();
	let initial = ServerSnapshot::from_bytes(saved.borrow().clone().unwrap());
	let head = initial.head().unwrap();
	server.get_shared_secret(b"invalid registration").unwrap();
	let next = saved.borrow().clone().unwrap();
	assert!(f.snapshot().compare_and_swap(None, &initial));
	let barrier = Arc::new(Barrier::new(2));
	let workers = (0..2)
		.map(|_| {
			let factory = f.clone();
			let bytes = next.clone();
			let gate = Arc::clone(&barrier);
			std::thread::spawn(move || {
				let mut store = factory.snapshot();
				gate.wait();
				store.compare_and_swap(Some(&head), &ServerSnapshot::from_bytes(bytes))
			})
		})
		.collect::<Vec<_>>();
	assert_eq!(
		workers
			.into_iter()
			.map(|worker| worker.join().unwrap())
			.filter(|won| *won)
			.count(),
		1
	);
	assert_eq!(f.snapshot().load().unwrap().as_bytes(), next);
}

fn expected_counts(nonzero: &[(&str, u64)]) -> Value {
	let mut expected = json!({
		"network_exchanges":0,"sql_calls":0,"validation_bytes_sent":0,"validation_rows":0,
		"value_bytes_expected":0,"stores":0,"expects":0,"loads":0,"reads":0,"writes":0,
		"transactions":0,"value_bytes_read":0,"value_bytes_written":0,"head_bytes_read":0
	});
	for &(key, value) in nonzero {
		*expected.get_mut(key).expect("known counter name") = json!(value);
	}
	expected
}

fn assert_counts_and_reset(counts: &Counters, expected: Value) {
	assert_eq!(serde_json::to_value(counts.take()).unwrap(), expected);
	assert_eq!(
		serde_json::to_value(counts.take()).unwrap(),
		expected_counts(&[]),
		"taking counters must reset every field, including accumulated byte counts"
	);
}

fn assert_trace_and_disable(counts: &Counters, epoch: Instant, labels: &[&str]) {
	let spans = counts.take_trace();
	assert_eq!(
		spans.iter().map(|span| span.kind).collect::<Vec<_>>(),
		labels,
		"only actual client database calls produce spans; buffered callbacks do not"
	);
	let elapsed = super::nanos(epoch.elapsed());
	for span in &spans {
		assert!(span.start_ns < span.end_ns);
		assert!(span.end_ns <= elapsed);
	}
	for pair in spans.windows(2) {
		assert!(pair[0].end_ns <= pair[1].start_ns);
	}
	assert!(counts.take_trace().is_empty());
}

fn row_counters_distinguish_callbacks_fetches_validation_and_committed_values(f: &Factory) {
	let pg = matches!(f, Factory::Postgres(_));
	let (mut store, counts) = f.rows_with_counts();
	store
		.transaction(&mut |tx| {
			tx.store(b"alpha", b"one")?;
			tx.store(b"beta", b"bravo!")?;
			tx.store(b"empty", b"")
		})
		.unwrap();
	counts.take();
	let epoch = Instant::now();
	counts.enable_trace(epoch, 8);
	let callbacks = Cell::new(0);
	store
		.transaction(&mut |tx| {
			callbacks.set(callbacks.get() + 1);
			assert_eq!(tx.load(b"alpha")?, Some(b"one".to_vec()));
			assert_eq!(tx.load(b"alpha")?, Some(b"one".to_vec()));
			assert_eq!(tx.load(b"missing")?, None);
			assert_eq!(tx.load(b"missing")?, None);
			assert_eq!(tx.load(b"empty")?, Some(vec![]));
			tx.expect(b"alpha", Some(b"one"))?;
			tx.expect(b"beta", Some(b"bravo!"))?;
			tx.expect(b"absent", None)?;
			tx.expect(b"empty", Some(b""))?;
			assert_eq!(tx.load(b"beta")?, Some(b"bravo!".to_vec()));
			assert_eq!(tx.load(b"absent")?, None);
			tx.store(b"alpha", b"intermediate")?;
			tx.store(b"alpha", b"final")?;
			assert_eq!(tx.load(b"alpha")?, Some(b"final".to_vec()));
			tx.expect(b"alpha", Some(b"final"))?;
			tx.store(b"beta", b"BB")?;
			assert_eq!(tx.load(b"beta")?, Some(b"BB".to_vec()));
			tx.store(b"missing", b"arrived")?;
			assert_eq!(tx.load(b"missing")?, Some(b"arrived".to_vec()));
			tx.store(b"new", b"XYZW")?;
			assert_eq!(tx.load(b"new")?, Some(b"XYZW".to_vec()));
			tx.expect(b"new", Some(b"XYZW"))
		})
		.unwrap();
	assert_eq!(callbacks.get(), 1);
	// Only alpha, missing and empty were fetched. Five distinct original rows are validated;
	// the overwritten intermediate value and repeated loads are not committed or fetched again.
	assert_counts_and_reset(
		&counts,
		expected_counts(&[
			("loads", 11),
			("expects", 6),
			("stores", 5),
			("reads", 3),
			("writes", 4),
			("transactions", 1),
			("value_bytes_read", 3),
			("value_bytes_expected", 18),
			("validation_rows", 5),
			("validation_bytes_sent", 9),
			("value_bytes_written", 18),
			("sql_calls", if pg { 4 } else { 14 }),
			("network_exchanges", if pg { 4 } else { 0 }),
		]),
	);
	// Taking numeric counters leaves the independently collected trace intact.
	assert_trace_and_disable(
		&counts,
		epoch,
		&["row_load", "row_load", "row_load", "row_commit"],
	);
	let mut observer = f.rows();
	for (key, expected) in [
		(b"alpha".as_slice(), Some(b"final".as_slice())),
		(b"beta", Some(b"BB")),
		(b"missing", Some(b"arrived")),
		(b"new", Some(b"XYZW")),
		(b"empty", Some(b"")),
		(b"absent", None),
	] {
		assert_eq!(get(&mut *observer, key).as_deref(), expected);
	}

	let epoch = Instant::now();
	counts.enable_trace(epoch, 4);
	assert_eq!(
		store.transaction(&mut |tx| {
			assert_eq!(tx.load(b"alpha")?, Some(b"final".to_vec()));
			tx.expect(b"beta", Some(b"BB"))?;
			tx.store(b"discarded", b"not committed")?;
			Err(RowError::OutputEncoding)
		}),
		Err(RowError::OutputEncoding)
	);
	assert_counts_and_reset(
		&counts,
		expected_counts(&[
			("loads", 1),
			("expects", 1),
			("stores", 1),
			("reads", 1),
			("value_bytes_read", 5),
			("value_bytes_expected", 2),
			("sql_calls", 1),
			("network_exchanges", u64::from(pg)),
		]),
	);
	assert_trace_and_disable(&counts, epoch, &["row_load"]);
	assert_eq!(get(&mut *observer, b"discarded"), None);

	let epoch = Instant::now();
	counts.enable_trace(epoch, 4);
	assert_eq!(
		store.transaction(&mut |tx| {
			tx.expect(b"alpha", Some(b"one"))?;
			tx.store(b"discarded", b"stale candidate")
		}),
		Err(RowError::Conflict)
	);
	// Transactions count attempted commits, but writes and written bytes count committed values.
	assert_counts_and_reset(
		&counts,
		expected_counts(&[
			("expects", 1),
			("stores", 1),
			("transactions", 1),
			("value_bytes_expected", 3),
			("validation_rows", 1),
			("validation_bytes_sent", 3),
			("sql_calls", if pg { 1 } else { 2 }),
			("network_exchanges", u64::from(pg)),
		]),
	);
	assert_trace_and_disable(&counts, epoch, &["row_commit"]);
	assert_eq!(get(&mut *observer, b"discarded"), None);
	assert_eq!(get(&mut *observer, b"alpha"), Some(b"final".to_vec()));
	assert_eq!(get(&mut *store, b"alpha"), Some(b"final".to_vec()));
	assert!(
		counts.take_trace().is_empty(),
		"taking a trace disables tracing until explicitly enabled again"
	);
}

fn snapshot_counters_cover_empty_repeated_loads_success_and_stale_cas(f: &Factory) {
	let pg = matches!(f, Factory::Postgres(_));
	let saved = Rc::new(RefCell::new(None));
	let mut server = PersistentServer::create(
		19,
		Some(&[82; 32]),
		Some(&[83; 32]),
		Capture(Rc::clone(&saved)),
	)
	.unwrap();
	let initial = ServerSnapshot::from_bytes(saved.borrow().clone().unwrap());
	let initial_head = initial.head().unwrap();
	server.get_shared_secret(b"invalid registration").unwrap();
	let next = ServerSnapshot::from_bytes(saved.borrow().clone().unwrap());
	let next_head = next.head().unwrap();
	assert_eq!(next_head.generation(), initial_head.generation() + 1);
	assert_ne!(initial.as_bytes(), next.as_bytes());
	let (mut store, counts) = f.snapshot_with_counts();
	assert_counts_and_reset(&counts, expected_counts(&[]));
	for _ in 0..2 {
		let epoch = Instant::now();
		counts.enable_trace(epoch, 4);
		assert!(store.load().is_none());
		assert_counts_and_reset(
			&counts,
			expected_counts(&[
				("reads", 1),
				("sql_calls", 1),
				("network_exchanges", u64::from(pg)),
			]),
		);
		assert_trace_and_disable(&counts, epoch, &["snapshot_load"]);
	}
	let epoch = Instant::now();
	counts.enable_trace(epoch, 8);
	assert!(store.compare_and_swap(None, &initial));
	for _ in 0..2 {
		let loaded = store.load().unwrap();
		assert_eq!(loaded.as_bytes(), initial.as_bytes());
		assert_eq!(loaded.head().unwrap(), initial_head);
	}
	let initial_bytes = initial.as_bytes().len() as u64;
	assert_counts_and_reset(
		&counts,
		expected_counts(&[
			("reads", if pg { 2 } else { 3 }),
			("writes", 1),
			("transactions", 1),
			("value_bytes_read", 2 * initial_bytes),
			("value_bytes_written", initial_bytes),
			("sql_calls", if pg { 3 } else { 6 }),
			("network_exchanges", if pg { 3 } else { 0 }),
		]),
	);
	assert_trace_and_disable(
		&counts,
		epoch,
		&["snapshot_commit", "snapshot_load", "snapshot_load"],
	);
	let epoch = Instant::now();
	counts.enable_trace(epoch, 8);
	assert!(store.compare_and_swap(Some(&initial_head), &next));
	assert!(!store.compare_and_swap(Some(&initial_head), &next));
	for _ in 0..2 {
		let loaded = store.load().unwrap();
		assert_eq!(loaded.as_bytes(), next.as_bytes());
		assert_eq!(loaded.head().unwrap(), next_head);
	}
	let next_bytes = next.as_bytes().len() as u64;
	assert_counts_and_reset(
		&counts,
		expected_counts(&[
			("reads", if pg { 2 } else { 4 }),
			("writes", 1),
			("transactions", 2),
			("value_bytes_read", 2 * next_bytes),
			("value_bytes_written", next_bytes),
			("head_bytes_read", if pg { 0 } else { 144 }),
			("validation_rows", if pg { 2 } else { 0 }),
			("validation_bytes_sent", if pg { 144 } else { 0 }),
			("sql_calls", if pg { 4 } else { 8 }),
			("network_exchanges", if pg { 4 } else { 0 }),
		]),
	);
	assert_trace_and_disable(
		&counts,
		epoch,
		&[
			"snapshot_commit",
			"snapshot_commit",
			"snapshot_load",
			"snapshot_load",
		],
	);
	let reopened = f.snapshot().load().unwrap();
	assert_eq!(reopened.as_bytes(), next.as_bytes());
	assert_eq!(reopened.head().unwrap(), next_head);
	assert_eq!(store.load().unwrap().as_bytes(), next.as_bytes());
	assert!(counts.take_trace().is_empty());
}

macro_rules! cases {
	($($sqlite:ident,$pg:ident,$test:ident);+ $(;)?)=> {$ (
		#[test] fn $sqlite(){fixture(false,$test);}
		#[test] #[ignore="requires dedicated live loopback PostgreSQL; root coordinates server"] fn $pg(){fixture(true,$test);}
	)+};
}
cases! {
	sqlite_empty,postgres_empty,empty_and_read_your_writes;
	sqlite_multirow,postgres_multirow,stale_multirow_is_atomic;
	sqlite_read_only,postgres_read_only,absent_and_read_only_conflicts;
	sqlite_errors,postgres_errors,errors_are_sticky_and_rollback;
	sqlite_no_partial_writes,postgres_no_partial_writes,database_error_rolls_back_prior_write;
	sqlite_race,postgres_race,concurrent_conflict;
	sqlite_snapshot_cas,postgres_snapshot_cas,concurrent_snapshot_cas;
	sqlite_row_counters,postgres_row_counters,row_counters_distinguish_callbacks_fetches_validation_and_committed_values;
	sqlite_snapshot_counters,postgres_snapshot_counters,snapshot_counters_cover_empty_repeated_loads_success_and_stale_cas;
}
