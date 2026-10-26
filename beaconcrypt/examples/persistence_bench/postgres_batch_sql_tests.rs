// SPDX-License-Identifier: 0BSD

use super::*;
use std::{
	sync::mpsc,
	time::{Duration, Instant},
};

fn fixture() -> Rc<PgFixture> {
	let mut lineage = [0; 32];
	beaconcrypt::crypto::random::fill_bytes(&mut lineage);
	PgFixture::create_batched(
		&std::env::var("BEACONCRYPT_BENCH_POSTGRES").expect("set live PostgreSQL DSN"),
		SnapshotLineage::from_bytes(lineage),
		BatchConfig::default(),
	)
	.unwrap()
}

fn client(fixture: &PgFixture) -> (Client, Statement) {
	let mut client = fixture.connect().unwrap();
	let statement = client
		.prepare(&format!(
			"SELECT {}.commit_batch($1,$2,$3,$4,$5,$6)",
			fixture.schema
		))
		.unwrap();
	(client, statement)
}

fn change(reads: &[(&[u8], Option<&[u8]>)], writes: &[(&[u8], &[u8])]) -> ChangeSet {
	ChangeSet::new(RowChanges {
		reads: reads
			.iter()
			.map(|(key, value)| (key.to_vec(), value.map(<[u8]>::to_vec)))
			.collect(),
		writes: writes
			.iter()
			.map(|(key, value)| (key.to_vec(), value.to_vec()))
			.collect(),
	})
}

fn value(client: &mut Client, fixture: &PgFixture, key: &[u8]) -> Option<Vec<u8>> {
	client
		.query_opt(
			&format!(
				"SELECT value FROM {}.peer_rows WHERE key=$1",
				fixture.schema
			),
			&[&key],
		)
		.unwrap()
		.map(|row| row.get(0))
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn batch_sql_preserves_absence_empty_values_and_independent_conflicts() {
	let fixture = fixture();
	let (mut client, statement) = client(&fixture);
	assert_eq!(
		commit_batch(
			&mut client,
			&statement,
			&[change(&[], &[(b"empty", b""), (b"shared", b"old")]),]
		)
		.unwrap(),
		vec![true]
	);
	let changes = [
		change(&[(b"absent", None)], &[(b"a", b"accepted")]),
		change(&[(b"empty", Some(b""))], &[(b"b", b"accepted")]),
		change(&[(b"empty", None)], &[(b"c", b"must not exist")]),
		change(&[(b"absent", Some(b""))], &[(b"d", b"must not exist")]),
		change(&[(b"shared", Some(b"stale"))], &[(b"e", b"must not exist")]),
		change(&[(b"shared", Some(b"old"))], &[(b"f", b"accepted")]),
	];
	assert_eq!(
		commit_batch(&mut client, &statement, &changes).unwrap(),
		vec![true, true, false, false, false, true]
	);
	for key in [b"a", b"b", b"f"] {
		assert_eq!(
			value(&mut client, &fixture, key),
			Some(b"accepted".to_vec())
		);
	}
	for key in [b"c", b"d", b"e"] {
		assert_eq!(value(&mut client, &fixture, key), None);
	}
	assert_eq!(value(&mut client, &fixture, b"empty"), Some(Vec::new()));
	assert_eq!(value(&mut client, &fixture, b"absent"), None);
	assert_eq!(
		value(&mut client, &fixture, b"shared"),
		Some(b"old".to_vec())
	);
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn batch_sql_exception_rolls_back_prior_successful_requests() {
	let fixture = fixture();
	fixture.reject_z();
	let (mut client, statement) = client(&fixture);
	let error = commit_batch(
		&mut client,
		&statement,
		&[
			change(&[(b"first", None)], &[(b"first", b"tentative")]),
			change(&[], &[(b"z", b"injected SQL failure")]),
		],
	)
	.unwrap_err();
	assert!(matches!(error, RowError::Storage(_)));
	assert_eq!(value(&mut client, &fixture, b"first"), None);
	assert_eq!(value(&mut client, &fixture, b"z"), None);
	assert_eq!(
		commit_batch(
			&mut client,
			&statement,
			&[change(&[(b"first", None)], &[(b"first", b"later commit")]),]
		)
		.unwrap(),
		vec![true]
	);
	assert_eq!(
		value(&mut client, &fixture, b"first"),
		Some(b"later commit".to_vec())
	);
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn batched_row_counters_count_each_singleton_leader_and_logical_row_activity() {
	let fixture = fixture();
	let counts = Rc::new(Counters::default());
	let mut store = PgRowStore::open(Rc::clone(&fixture), Rc::clone(&counts)).unwrap();
	store
		.transaction(&mut |tx| tx.store(b"alpha", b"old"))
		.unwrap();
	counts.take();
	counts.enable_trace(Instant::now(), 4);
	store
		.transaction(&mut |tx| {
			assert_eq!(tx.load(b"alpha")?, Some(b"old".to_vec()));
			tx.expect(b"alpha", Some(b"old"))?;
			tx.expect(b"side", None)?;
			tx.store(b"alpha", b"next")?;
			tx.store(b"side", b"xyz")
		})
		.unwrap();
	store
		.transaction(&mut |tx| {
			assert_eq!(tx.load(b"alpha")?, Some(b"next".to_vec()));
			tx.expect(b"alpha", Some(b"next"))?;
			tx.expect(b"side", Some(b"xyz"))?;
			tx.store(b"alpha", b"final")
		})
		.unwrap();
	// Serial callers make two singleton batches: each has one physical load and one durable
	// commit, while the second expectation in each request is validated without another fetch.
	assert_eq!(
		serde_json::to_value(counts.take()).unwrap(),
		json!({
			"network_exchanges": 4, "sql_calls": 4, "transactions": 2,
			"loads": 2, "reads": 2, "expects": 4, "stores": 3, "writes": 3,
			"validation_rows": 4, "validation_bytes_sent": 10, "value_bytes_expected": 10,
			"value_bytes_read": 7, "value_bytes_written": 12, "head_bytes_read": 0,
		})
	);
	assert!(
		serde_json::to_value(counts.take())
			.unwrap()
			.as_object()
			.unwrap()
			.values()
			.all(|value| value == &json!(0))
	);
	assert_eq!(
		counts
			.take_trace()
			.iter()
			.map(|span| span.kind)
			.collect::<Vec<_>>(),
		vec![
			"row_load",
			"row_batch_commit",
			"row_load",
			"row_batch_commit"
		]
	);
	let mut observer = fixture.connect().unwrap();
	assert_eq!(
		value(&mut observer, &fixture, b"alpha"),
		Some(b"final".to_vec())
	);
	assert_eq!(
		value(&mut observer, &fixture, b"side"),
		Some(b"xyz".to_vec())
	);
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn batch_sql_locks_the_global_union_before_validation_and_observes_waited_commit() {
	let fixture = fixture();
	let (mut control, statement) = client(&fixture);
	assert_eq!(
		commit_batch(
			&mut control,
			&statement,
			&[change(&[], &[(b"a", b"old"), (b"b", b"old")]),]
		)
		.unwrap(),
		vec![true]
	);
	let ordered = control.query(
		"SELECT k,hashtextextended($1 || encode(k,'hex'),0) AS id FROM unnest($2::bytea[]) AS keys(k) ORDER BY id",
		&[&format!("{}:", fixture.schema), &vec![b"a".as_slice(),b"b".as_slice()]],
	).unwrap();
	let low: Vec<u8> = ordered[0].get(0);
	let high: Vec<u8> = ordered[1].get(0);
	let low_hash: i64 = ordered[0].get(1);
	assert_ne!(low_hash, ordered[1].get::<_, i64>(1));
	let worker_fixture = fixture.worker_copy();
	let (started, ready) = mpsc::sync_channel(1);
	std::thread::scope(|scope| {
		let mut held = control.transaction().unwrap();
		held.query_one("SELECT pg_advisory_xact_lock($1)", &[&low_hash])
			.unwrap();
		let low_worker = low.clone();
		let high_worker = high.clone();
		let worker = scope.spawn(move || {
			let (mut connection, statement) = client(&worker_fixture);
			let pid: i32 = connection
				.query_one("SELECT pg_backend_pid()", &[])
				.unwrap()
				.get(0);
			started.send(pid).unwrap();
			// Deliberately reverse the requests' lock order. Prelocking must still wait for low
			// before taking high, and validation must see the holder's newly committed value.
			commit_batch(
				&mut connection,
				&statement,
				&[
					change(
						&[(&high_worker, Some(b"old"))],
						&[(&high_worker, b"accepted")],
					),
					change(&[(&low_worker, Some(b"old"))], &[(&low_worker, b"stale")]),
				],
			)
		});
		let pid = ready.recv_timeout(Duration::from_secs(5)).unwrap();
		let deadline = Instant::now() + Duration::from_secs(5);
		loop {
			let locks = held.query_one(
				"SELECT count(*) FILTER(WHERE NOT granted),count(*) FILTER(WHERE granted) FROM pg_locks WHERE pid=$1 AND locktype='advisory'",
				&[&pid],
			).unwrap();
			if locks.get::<_, i64>(0) > 0 {
				assert_eq!(
					locks.get::<_, i64>(1),
					0,
					"higher request lock acquired before the lower union lock"
				);
				break;
			}
			assert!(
				Instant::now() < deadline,
				"batch never waited for the held union lock"
			);
			std::thread::sleep(Duration::from_millis(10));
		}
		held.execute(
			&format!(
				"UPDATE {}.peer_rows SET value=$1 WHERE key=$2",
				fixture.schema
			),
			&[&b"winner".as_slice(), &low],
		)
		.unwrap();
		held.commit().unwrap();
		assert_eq!(worker.join().unwrap().unwrap(), vec![true, false]);
	});
	assert_eq!(
		value(&mut control, &fixture, &low),
		Some(b"winner".to_vec())
	);
	assert_eq!(
		value(&mut control, &fixture, &high),
		Some(b"accepted".to_vec())
	);
}
