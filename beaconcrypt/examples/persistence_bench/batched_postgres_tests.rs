// SPDX-License-Identifier: 0BSD

//! Native publication and recovery contracts for the opt-in durable PostgreSQL batch adapter.

use std::{
	cell::Cell,
	rc::Rc,
	sync::mpsc,
	thread,
	time::{Duration, Instant},
};

use beaconcrypt::{
	Beacon, CachedRowServer, Decrypted, Encrypted, ProviderBeacon, RowError, RowServer, RowSession,
	RowStore, RowTransaction, SnapshotLineage,
};
use postgres::Client;

use super::{
	database::Counters,
	postgres::{PgFixture, PgRowStore},
	postgres_batch::BatchConfig,
};

const SENTINEL: &[u8] = b"batch-test-sentinel";

struct LoseAcknowledgement {
	inner: PgRowStore,
	armed: Rc<Cell<bool>>,
}

impl RowStore for LoseAcknowledgement {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		self.inner.transaction(operation)?;
		if self.armed.replace(false) {
			return Err(RowError::Storage(
				"lost acknowledgement after shared commit".into(),
			));
		}
		Ok(())
	}
}

enum Native {
	Row(RowServer<LoseAcknowledgement>),
	Cached(CachedRowServer<LoseAcknowledgement>),
}

impl Native {
	fn open(
		fixture: &Rc<PgFixture>,
		lineage: SnapshotLineage,
		cached: bool,
		armed: Rc<Cell<bool>>,
	) -> Self {
		let store = LoseAcknowledgement {
			inner: store(fixture),
			armed,
		};
		if cached {
			Self::Cached(CachedRowServer::open(store, lineage, 1).unwrap())
		} else {
			Self::Row(RowServer::open(store, lineage).unwrap())
		}
	}

	fn transaction<T>(
		&mut self,
		operation: impl FnOnce(&mut RowSession<'_>) -> Result<T, RowError>,
	) -> Result<T, RowError> {
		match self {
			Self::Row(server) => server.transaction(operation),
			Self::Cached(server) => server.transaction(operation),
		}
	}

	fn encrypt(&mut self, data: &[u8], kid: u64) -> Encrypted {
		match self {
			Self::Row(server) => server.encrypt_message(data, kid),
			Self::Cached(server) => server.encrypt_message(data, kid),
		}
		.unwrap()
		.unwrap()
	}

	fn decrypt(&mut self, data: &[u8]) -> Option<Decrypted> {
		match self {
			Self::Row(server) => server.decrypt_message(data),
			Self::Cached(server) => server.decrypt_message(data),
		}
		.unwrap()
	}

	fn cached_peers(&self) -> Option<usize> {
		match self {
			Self::Row(_) => None,
			Self::Cached(server) => Some(server.cached_peer_count()),
		}
	}
}

struct Peer {
	beacon: Beacon,
	kid: u64,
	prime: Vec<u8>,
	last_server_seq: u64,
}

fn store(fixture: &Rc<PgFixture>) -> PgRowStore {
	PgRowStore::open(Rc::clone(fixture), Rc::new(Counters::default())).unwrap()
}

fn fixture() -> (Rc<PgFixture>, SnapshotLineage, Vec<Peer>) {
	let mut bytes = [0; 32];
	beaconcrypt::crypto::random::fill_bytes(&mut bytes);
	let lineage = SnapshotLineage::from_bytes(bytes);
	let fixture = PgFixture::create_batched(
		&std::env::var("BC_PERSISTENCE_PG_DSN").expect("set dedicated loopback PostgreSQL DSN"),
		lineage,
		BatchConfig {
			max_requests: 2,
			max_bytes: 1024 * 1024,
			queue_capacity: 8,
			max_delay: Duration::from_millis(10),
		},
	)
	.unwrap();
	let mut server = CachedRowServer::create(
		71,
		Some(&[72; 32]),
		Some(&[73; 32]),
		store(&fixture),
		lineage,
		2,
	)
	.unwrap();
	let mut peers = Vec::new();
	for _ in 0..2 {
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
		let prime = beacon.encrypt_message(b"receive prime").unwrap().ciphertext;
		assert_eq!(
			server.decrypt_message(&prime).unwrap().unwrap().plaintext,
			b"receive prime"
		);
		let outgoing = server
			.encrypt_message(b"send prime", response.kid)
			.unwrap()
			.unwrap();
		assert_eq!(
			beacon
				.decrypt_message(&outgoing.ciphertext)
				.unwrap()
				.plaintext,
			b"send prime"
		);
		peers.push(Peer {
			beacon,
			kid: response.kid,
			prime,
			last_server_seq: outgoing.seq,
		});
	}
	(fixture, lineage, peers)
}

/// Session locks disappear if a failing assertion drops this client. No test-owned lock can
/// outlive the test's control connection, including during a mutation-induced early return.
struct CommitGates {
	client: Client,
	schema: String,
}

impl CommitGates {
	fn install(fixture: &PgFixture) -> Self {
		let mut client = fixture.connect().unwrap();
		let schema = fixture.schema.clone();
		for phase in ["sentinel", "native"] {
			client
				.query_one(
					"SELECT pg_advisory_lock(hashtextextended($1,0))",
					&[&format!("{schema}:{phase}")],
				)
				.unwrap();
		}
		client
			.batch_execute(&format!(
				r#"
CREATE TABLE {schema}.commit_audit(value bytea NOT NULL, xid bigint NOT NULL);
CREATE FUNCTION {schema}.observe_native_commit() RETURNS trigger LANGUAGE plpgsql AS $body$
BEGIN
 IF NEW.key=convert_to('batch-test-sentinel','UTF8') THEN
  PERFORM pg_advisory_xact_lock(hashtextextended('{schema}:sentinel',0));
 ELSE
  PERFORM pg_advisory_xact_lock(hashtextextended('{schema}:native',0));
 END IF;
 INSERT INTO {schema}.commit_audit VALUES(NEW.value,txid_current());
 IF NEW.value=convert_to('batch-fail','UTF8') THEN
  RAISE EXCEPTION 'injected deferred failure for the entire shared commit';
 END IF;
 RETURN NEW;
END $body$;
CREATE CONSTRAINT TRIGGER native_commit_gate AFTER INSERT OR UPDATE ON {schema}.peer_rows
 DEFERRABLE INITIALLY DEFERRED FOR EACH ROW EXECUTE FUNCTION {schema}.observe_native_commit();
"#
			))
			.unwrap();
		Self { client, schema }
	}

	fn wait_for_waiter(&mut self, phase: &str) {
		let token = format!("{}:{phase}", self.schema);
		wait_until(
			"shared transaction must reach the deferred commit lock",
			|| {
				self.client.query_one(
				"SELECT EXISTS(SELECT FROM pg_locks WHERE locktype='advisory' AND NOT granted AND objsubid=1 AND classid=((hashtextextended($1,0)>>32)&4294967295)::oid AND objid=(hashtextextended($1,0)&4294967295)::oid)",
				&[&token],
			).unwrap().get(0)
			},
		);
	}

	fn release(&mut self, phase: &str) {
		assert!(
			self.client
				.query_one(
					"SELECT pg_advisory_unlock(hashtextextended($1,0))",
					&[&format!("{}:{phase}", self.schema)],
				)
				.unwrap()
				.get::<_, bool>(0)
		);
	}

	fn rows_without_sentinel(&mut self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.client
			.query(
				&format!(
					"SELECT key,value FROM {}.peer_rows WHERE key<>$1 ORDER BY key",
					self.schema
				),
				&[&SENTINEL],
			)
			.unwrap()
			.into_iter()
			.map(|row| (row.get(0), row.get(1)))
			.collect()
	}

	fn transaction_ids(&mut self, value: &[u8]) -> Vec<i64> {
		self.client
			.query(
				&format!(
					"SELECT xid FROM {}.commit_audit WHERE value=$1 ORDER BY xid",
					self.schema
				),
				&[&value],
			)
			.unwrap()
			.into_iter()
			.map(|row| row.get(0))
			.collect()
	}
}

fn wait_until(label: &str, mut observed: impl FnMut() -> bool) {
	let deadline = Instant::now() + Duration::from_secs(5);
	while !observed() {
		assert!(Instant::now() < deadline, "{label}");
		thread::sleep(Duration::from_millis(10));
	}
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Outcome {
	Committed,
	SqlFailure,
	LostAcknowledgement,
}

#[derive(Debug)]
struct Published {
	key_id: u64,
	sequence: u64,
	bytes: Vec<u8>,
}

struct WorkerResult {
	index: usize,
	output: Result<Published, RowError>,
	cache_after: Option<usize>,
	native_calls: usize,
}

fn native_cohort(cached: bool, outcome: Outcome) {
	let (fixture, lineage, mut peers) = fixture();
	let (ready_tx, ready_rx) = mpsc::channel();
	let (published_tx, published_rx) = mpsc::channel();
	let mut starters = Vec::new();
	let mut workers = Vec::new();
	for (index, peer) in peers.iter().enumerate() {
		let owned = fixture.worker_copy();
		let prime = peer.prime.clone();
		let kid = peer.kid;
		let ready = ready_tx.clone();
		let published = published_tx.clone();
		let (start_tx, start_rx) = mpsc::channel();
		starters.push(start_tx);
		workers.push(thread::spawn(move || {
			let fixture = Rc::new(owned);
			let armed = Rc::new(Cell::new(false));
			let mut server = Native::open(&fixture, lineage, cached, Rc::clone(&armed));
			assert!(server.decrypt(&prime).is_none());
			assert_eq!(server.cached_peers(), cached.then_some(1));
			ready.send(()).unwrap();
			if start_rx.recv().is_err() {
				return;
			}
			armed.set(outcome == Outcome::LostAcknowledgement);
			let mut native_calls = 0;
			let output = server.transaction(|session| {
				let request = format!("request-{index}");
				assert!(session.load_application(request.as_bytes())?.is_none());
				native_calls += 1;
				let pending = session
					.encrypt_message(format!("batched response {index}").as_bytes(), kid)?
					.message
					.unwrap();
				session.store_application(request.as_bytes(), pending.data())?;
				if outcome == Outcome::SqlFailure && index == 1 {
					session.store_application(b"reject whole batch", b"batch-fail")?;
				}
				Ok(Published {
					key_id: pending.key_id(),
					sequence: pending.sequence(),
					bytes: pending.data().to_vec(),
				})
			});
			published
				.send(WorkerResult {
					index,
					output,
					cache_after: server.cached_peers(),
					native_calls,
				})
				.unwrap();
		}));
	}
	drop(ready_tx);
	drop(published_tx);
	for _ in 0..2 {
		ready_rx.recv_timeout(Duration::from_secs(5)).unwrap();
	}
	let mut gates = CommitGates::install(&fixture);
	let original_rows = gates.rows_without_sentinel();
	let blocker_fixture = fixture.worker_copy();
	let (blocker_tx, blocker_rx) = mpsc::channel();
	let blocker = thread::spawn(move || {
		let mut store = store(&Rc::new(blocker_fixture));
		blocker_tx
			.send(store.transaction(&mut |tx| tx.store(SENTINEL, b"sentinel")))
			.unwrap();
	});
	gates.wait_for_waiter("sentinel");
	assert!(matches!(
		blocker_rx.try_recv(),
		Err(mpsc::TryRecvError::Empty)
	));
	for start in starters {
		start.send(()).unwrap();
	}
	wait_until("both independent native requests must be queued", || {
		fixture.batch_pending_for_test() == 2
	});
	assert!(matches!(
		published_rx.try_recv(),
		Err(mpsc::TryRecvError::Empty)
	));
	gates.release("sentinel");
	assert_eq!(
		blocker_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
		Ok(())
	);
	blocker.join().unwrap();
	gates.wait_for_waiter("native");
	assert!(
		matches!(published_rx.try_recv(), Err(mpsc::TryRecvError::Empty)),
		"native output escaped before shared durable commit"
	);
	assert_eq!(
		gates.rows_without_sentinel(),
		original_rows,
		"other connections must not see candidates before commit"
	);
	gates.release("native");
	let mut results = (0..2)
		.map(|_| published_rx.recv_timeout(Duration::from_secs(5)).unwrap())
		.collect::<Vec<_>>();
	for worker in workers {
		worker.join().unwrap();
	}
	results.sort_by_key(|result| result.index);
	for result in &results {
		assert_eq!(
			result.native_calls, 1,
			"one-use native callbacks must never be retried"
		);
		assert_eq!(
			result.cache_after,
			cached.then_some(usize::from(outcome == Outcome::Committed))
		);
		match outcome {
			Outcome::Committed => assert!(result.output.is_ok()),
			Outcome::SqlFailure => assert!(matches!(result.output, Err(RowError::Storage(_)))),
			Outcome::LostAcknowledgement => assert_eq!(
				result.output.as_ref().unwrap_err(),
				&RowError::Storage("lost acknowledgement after shared commit".into())
			),
		}
	}
	if outcome == Outcome::SqlFailure {
		assert_eq!(
			gates.rows_without_sentinel(),
			original_rows,
			"the failed shared SQL commit must roll back every ratchet and receipt"
		);
		let audit_rows: i64 = gates
			.client
			.query_one(
				&format!("SELECT count(*) FROM {}.commit_audit", gates.schema),
				&[],
			)
			.unwrap()
			.get(0);
		assert_eq!(
			audit_rows, 1,
			"only the separately committed sentinel may survive"
		);
	}
	let mut receipt_xids = Vec::new();
	for (index, peer) in peers.iter_mut().enumerate() {
		let mut restored = Native::open(&fixture, lineage, cached, Rc::new(Cell::new(false)));
		let request = format!("request-{index}");
		let receipt = restored
			.transaction(|session| {
				session
					.load_application(request.as_bytes())
					.map(|value| value.map(|bytes| bytes.to_vec()))
			})
			.unwrap();
		if outcome == Outcome::SqlFailure {
			assert!(receipt.is_none());
		} else {
			let receipt = receipt.unwrap();
			if let Ok(published) = &results[index].output {
				assert_eq!(published.key_id, peer.kid);
				assert_eq!(published.sequence, peer.last_server_seq + 1);
				assert_eq!(published.bytes, receipt);
			}
			let decoded = peer.beacon.decrypt_message(&receipt).unwrap();
			assert_eq!(
				decoded.plaintext,
				format!("batched response {index}").as_bytes()
			);
			assert_eq!(decoded.seq, peer.last_server_seq + 1);
			peer.last_server_seq = decoded.seq;
			assert!(peer.beacon.decrypt_message(&receipt).is_none());
			let again = restored
				.transaction(|session| session.load_application(request.as_bytes()))
				.unwrap()
				.unwrap();
			assert_eq!(again.as_slice(), receipt);
			let ids = gates.transaction_ids(&receipt);
			assert_eq!(ids.len(), 1);
			receipt_xids.push(ids[0]);
		}
		let outgoing = restored.encrypt(b"next durable send", peer.kid);
		assert_eq!(outgoing.seq, peer.last_server_seq + 1);
		assert_eq!(
			peer.beacon
				.decrypt_message(&outgoing.ciphertext)
				.unwrap()
				.plaintext,
			b"next durable send"
		);
		let incoming = peer
			.beacon
			.encrypt_message(b"next durable receive")
			.unwrap();
		let decoded = restored.decrypt(&incoming.ciphertext).unwrap();
		assert_eq!(decoded.key_id, peer.kid);
		assert_eq!(decoded.seq, incoming.seq);
		assert_eq!(decoded.plaintext, b"next durable receive");
		assert!(restored.decrypt(&incoming.ciphertext).is_none());
		let later = peer
			.beacon
			.encrypt_message(b"receive after replay")
			.unwrap();
		assert_eq!(
			restored.decrypt(&later.ciphertext).unwrap().plaintext,
			b"receive after replay"
		);
	}
	if outcome != Outcome::SqlFailure {
		assert_eq!(receipt_xids.len(), 2);
		assert_eq!(
			receipt_xids[0], receipt_xids[1],
			"independent ratchets and receipts must have shared one physical SQL transaction"
		);
		assert_ne!(receipt_xids[0], gates.transaction_ids(b"sentinel")[0]);
	}
}

#[test]
#[ignore = "requires dedicated BC_PERSISTENCE_PG_DSN"]
fn batched_postgres_native_outputs_wait_for_shared_commit_and_restore_order() {
	for cached in [false, true] {
		native_cohort(cached, Outcome::Committed);
	}
}

#[test]
#[ignore = "requires dedicated BC_PERSISTENCE_PG_DSN"]
fn batched_postgres_sql_failure_rolls_back_all_native_outputs_and_clears_caches() {
	for cached in [false, true] {
		native_cohort(cached, Outcome::SqlFailure);
	}
}

#[test]
#[ignore = "requires dedicated BC_PERSISTENCE_PG_DSN"]
fn batched_postgres_lost_ack_recovers_exact_shared_receipts_without_native_retry() {
	for cached in [false, true] {
		native_cohort(cached, Outcome::LostAcknowledgement);
	}
}
