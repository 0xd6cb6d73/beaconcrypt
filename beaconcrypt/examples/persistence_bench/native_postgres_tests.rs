// SPDX-License-Identifier: 0BSD

//! Opt-in native protocol tests against the dedicated loopback PostgreSQL fixture.

use std::{
	cell::Cell,
	path::PathBuf,
	process::Command,
	rc::Rc,
	sync::{
		Arc, Barrier,
		atomic::{AtomicUsize, Ordering},
	},
	thread,
};

use beaconcrypt::{
	Beacon, CachedRowServer, ProviderBeacon, RowError, RowServer, RowStore, RowTransaction,
	SnapshotLineage,
};

use super::{
	database::Counters,
	postgres::{PgFixture, PgRowStore},
};

fn fixture() -> (Rc<PgFixture>, SnapshotLineage) {
	let dsn = std::env::var("BC_PERSISTENCE_PG_DSN")
		.expect("set BC_PERSISTENCE_PG_DSN to a dedicated loopback PostgreSQL test database");
	let mut bytes = [0; 32];
	libsodium_rs::random::fill_bytes(&mut bytes);
	let lineage = SnapshotLineage::from_bytes(bytes);
	(PgFixture::create(&dsn, lineage).unwrap(), lineage)
}

fn store(fixture: &Rc<PgFixture>, counts: &Rc<Counters>) -> PgRowStore {
	PgRowStore::open(Rc::clone(fixture), Rc::clone(counts)).unwrap()
}

fn register<S: RowStore>(server: &mut CachedRowServer<S>) -> (Beacon, u64) {
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

struct LoseAcknowledgement {
	inner: PgRowStore,
	fail: Rc<Cell<bool>>,
}

impl RowStore for LoseAcknowledgement {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		self.inner.transaction(operation)?;
		if self.fail.replace(false) {
			return Err(RowError::Storage(
				"lost acknowledgement after PostgreSQL commit".into(),
			));
		}
		Ok(())
	}
}

#[test]
#[ignore = "requires dedicated BC_PERSISTENCE_PG_DSN"]
fn postgres_cached_native_state_and_receipt_survive_conflict_and_lost_acknowledgement() {
	let (fixture, lineage) = fixture();
	let counts = Rc::new(Counters::default());
	let fail = Rc::new(Cell::new(false));
	let mut server = CachedRowServer::create(
		71,
		Some(&[72; 32]),
		Some(&[73; 32]),
		LoseAcknowledgement {
			inner: store(&fixture, &counts),
			fail: Rc::clone(&fail),
		},
		lineage,
		2,
	)
	.unwrap();
	let (mut beacon, kid) = register(&mut server);
	counts.take();
	beacon
		.decrypt_message(
			&server
				.encrypt_message(b"cold", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	let cold = counts.take();
	assert_eq!(
		(cold.loads, cold.expects, cold.network_exchanges),
		(1, 0, 2)
	);
	beacon
		.decrypt_message(
			&server
				.encrypt_message(b"warm", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	let warm = counts.take();
	assert_eq!(
		(warm.loads, warm.expects, warm.network_exchanges),
		(0, 1, 1)
	);
	let mut other =
		RowServer::open(store(&fixture, &Rc::new(Counters::default())), lineage).unwrap();
	beacon
		.decrypt_message(
			&other
				.encrypt_message(b"foreign", kid)
				.unwrap()
				.unwrap()
				.ciphertext,
		)
		.unwrap();
	assert!(matches!(
		server.encrypt_message(b"stale", kid),
		Err(RowError::Conflict)
	));
	assert_eq!(server.cached_peer_count(), 0);
	let incoming = beacon.encrypt_message(b"durable received result").unwrap();
	fail.set(true);
	assert!(
		server
			.transaction(|session| {
				let pending = session
					.decrypt_message(&incoming.ciphertext)?
					.message
					.unwrap();
				session.store_application(b"request", pending.data())?;
				Ok(pending.data().to_vec())
			})
			.is_err()
	);
	assert_eq!(server.cached_peer_count(), 0);
	drop(server);
	let mut reopened = CachedRowServer::open(store(&fixture, &counts), lineage, 2).unwrap();
	let receipt = reopened
		.transaction(|session| session.load_application(b"request"))
		.unwrap()
		.unwrap();
	assert_eq!(receipt.as_slice(), b"durable received result");
	assert!(
		reopened
			.decrypt_message(&incoming.ciphertext)
			.unwrap()
			.is_none()
	);
	let later = beacon.encrypt_message(b"next").unwrap();
	assert_eq!(
		reopened
			.decrypt_message(&later.ciphertext)
			.unwrap()
			.unwrap()
			.plaintext,
		b"next"
	);
}

#[test]
#[ignore = "requires dedicated BC_PERSISTENCE_PG_DSN"]
fn postgres_cached_request_race_commits_one_response_and_retry_recovers_exact_bytes() {
	let (fixture, lineage) = fixture();
	let mut owner = CachedRowServer::create(
		71,
		Some(&[72; 32]),
		Some(&[73; 32]),
		store(&fixture, &Rc::new(Counters::default())),
		lineage,
		2,
	)
	.unwrap();
	let (mut beacon, kid) = register(&mut owner);
	let prime = beacon
		.encrypt_message(b"prime cached receive")
		.unwrap()
		.ciphertext;
	owner.decrypt_message(&prime).unwrap().unwrap();
	let barrier = Arc::new(Barrier::new(2));
	let native_calls = Arc::new(AtomicUsize::new(0));
	let workers: Vec<_> = (0..2)
		.map(|_| {
			let owned = fixture.worker_copy();
			let barrier = Arc::clone(&barrier);
			let native_calls = Arc::clone(&native_calls);
			let prime = prime.clone();
			thread::spawn(move || {
				let fixture = Rc::new(owned);
				let mut server = CachedRowServer::open(
					store(&fixture, &Rc::new(Counters::default())),
					lineage,
					1,
				)
				.unwrap();
				assert!(server.decrypt_message(&prime).unwrap().is_none());
				assert_eq!(server.cached_peer_count(), 1);
				let attempted = server.transaction(|session| {
					assert!(session.load_application(b"same request")?.is_none());
					// Both candidates observe absence and the same cached ratchet predecessor.
					barrier.wait();
					native_calls.fetch_add(1, Ordering::SeqCst);
					let message = session
						.encrypt_message(b"one committed response", kid)?
						.message
						.unwrap();
					session.store_application(b"same request", message.data())?;
					Ok(message.data().to_vec())
				});
				let conflicted = match &attempted {
					Ok(_) => false,
					Err(RowError::Conflict) => {
						assert_eq!(server.cached_peer_count(), 0);
						true
					}
					Err(error) => panic!("unexpected error: {error}"),
				};
				let recovered = server
					.transaction(|session| {
						if let Some(receipt) = session.load_application(b"same request")? {
							return Ok(receipt.to_vec());
						}
						native_calls.fetch_add(1, Ordering::SeqCst);
						panic!("committed receipt must prevent another native transition")
					})
					.unwrap();
				if let Ok(output) = attempted {
					assert_eq!(output, recovered);
				}
				(conflicted, recovered)
			})
		})
		.collect();
	let outcomes: Vec<_> = workers
		.into_iter()
		.map(|worker| worker.join().unwrap())
		.collect();
	assert_eq!(
		outcomes
			.iter()
			.filter(|(conflicted, _)| *conflicted)
			.count(),
		1
	);
	assert_eq!(outcomes[0].1, outcomes[1].1);
	// Two private candidates were computed; only one was committed. Recovery computes neither again.
	assert_eq!(native_calls.load(Ordering::SeqCst), 2);
	assert_eq!(
		beacon.decrypt_message(&outcomes[0].1).unwrap().plaintext,
		b"one committed response"
	);
	assert!(beacon.decrypt_message(&outcomes[1].1).is_none());
}

#[test]
#[ignore = "restarts only the explicitly supplied dedicated BC_PG_TEST_OWNED_DATA cluster"]
fn postgres_crash_restart_preserves_committed_receipt_and_discards_uncommitted_rows() {
	let (fixture, lineage) = fixture();
	let data = PathBuf::from(
		std::env::var("BC_PG_TEST_OWNED_DATA").expect("explicit owned test cluster required"),
	);
	let pg_ctl =
		PathBuf::from(std::env::var("BC_PG_TEST_PG_CTL").expect("explicit pg_ctl required"));
	let actual: String = fixture
		.connect()
		.unwrap()
		.query_one("SHOW data_directory", &[])
		.unwrap()
		.get(0);
	assert_eq!(
		data.canonicalize().unwrap(),
		PathBuf::from(actual).canonicalize().unwrap()
	);
	assert!(
		data.join("BC_TEST_CLUSTER_ONLY").is_file(),
		"refuse to restart an unmarked cluster"
	);
	let mut server = CachedRowServer::create(
		71,
		Some(&[72; 32]),
		Some(&[73; 32]),
		store(&fixture, &Rc::new(Counters::default())),
		lineage,
		1,
	)
	.unwrap();
	let (mut beacon, kid) = register(&mut server);
	let ciphertext = server
		.transaction(|session| {
			let message = session
				.encrypt_message(b"durable before crash", kid)?
				.message
				.unwrap();
			session.store_application(b"durable receipt", message.data())?;
			Ok(message.data().to_vec())
		})
		.unwrap();
	let sent = beacon.decrypt_message(&ciphertext).unwrap();
	let mut uncommitted = fixture.connect().unwrap();
	uncommitted.batch_execute("BEGIN").unwrap();
	uncommitted
		.execute(
			&format!(
				"INSERT INTO {}.peer_rows(key,value) VALUES($1,$2)",
				fixture.schema
			),
			&[&b"uncommitted".as_slice(), &b"discard me".as_slice()],
		)
		.unwrap();
	let stopped = Command::new(&pg_ctl)
		.args(["stop", "-m", "immediate", "-w", "-t", "15", "-D"])
		.arg(&data)
		.status()
		.unwrap();
	assert!(stopped.success());
	let started = Command::new(&pg_ctl)
		.args(["start", "-w", "-t", "30", "-D"])
		.arg(&data)
		.arg("-l")
		.arg(data.join("restart-test.log"))
		.status()
		.unwrap();
	assert!(started.success());
	assert!(server.encrypt_message(b"broken connection", kid).is_err());
	assert_eq!(server.cached_peer_count(), 0);
	let mut reopened =
		CachedRowServer::open(store(&fixture, &Rc::new(Counters::default())), lineage, 1).unwrap();
	let recovered = reopened
		.transaction(|session| session.load_application(b"durable receipt"))
		.unwrap()
		.unwrap();
	assert_eq!(recovered.as_slice(), ciphertext.as_slice());
	let next = reopened
		.encrypt_message(b"after recovery", kid)
		.unwrap()
		.unwrap();
	assert_eq!(next.seq, sent.seq + 1);
	assert_eq!(
		beacon.decrypt_message(&next.ciphertext).unwrap().plaintext,
		b"after recovery"
	);
	let value = fixture
		.connect()
		.unwrap()
		.query_opt(
			&format!(
				"SELECT value FROM {}.peer_rows WHERE key=$1",
				fixture.schema
			),
			&[&b"uncommitted".as_slice()],
		)
		.unwrap();
	assert!(value.is_none());
}
