// SPDX-License-Identifier: 0BSD

use std::{
	cell::RefCell,
	path::PathBuf,
	rc::Rc,
	sync::{Arc, Barrier},
};

use beaconcrypt::{
	PersistentServer, RowError, RowStore, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};

use super::{
	database::{Counters, SqlRowStore, SqlSnapshotStore},
	postgres::{PgFixture, PgRowStore, PgSnapshotStore},
};

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
		let counts = Rc::new(Counters::default());
		match self {
			Self::Sqlite(p) => Box::new(SqlRowStore::open(p, counts).unwrap()),
			Self::Postgres(p) => {
				Box::new(PgRowStore::open(Rc::new(p.worker_copy()), counts).unwrap())
			}
		}
	}
	fn snapshot(&self) -> Box<dyn SnapshotStore> {
		let counts = Rc::new(Counters::default());
		match self {
			Self::Sqlite(p) => Box::new(SqlSnapshotStore::open(p, counts).unwrap()),
			Self::Postgres(p) => {
				Box::new(PgSnapshotStore::open(Rc::new(p.worker_copy()), counts).unwrap())
			}
		}
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
			let _ = tx.store(b"discard", b"value");
			Ok(())
		}),
		Err(RowError::Conflict)
	);
	assert_eq!(get(&mut *a, b"discard"), None);
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
}
