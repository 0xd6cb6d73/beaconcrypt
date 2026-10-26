// SPDX-License-Identifier: 0BSD

//! Benchmark-only PostgreSQL adapter. Every writer must use the same advisory-lock protocol.

use std::{
	cell::RefCell,
	net::{IpAddr, Ipv4Addr, Ipv6Addr},
	rc::Rc,
	str::FromStr,
};

use beaconcrypt::{
	RowError, RowStore, RowTransaction, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};
use postgres::{Client, Config, NoTls, Statement, config::Host};
use serde_json::{Value, json};

use super::{
	Result,
	buffered::Buffered,
	database::Counters,
	postgres_batch::{BatchConfig, Batcher, ChangeSet, RowChanges},
};

#[cfg(test)]
#[path = "postgres_batch_sql_tests.rs"]
mod batch_sql_tests;

pub struct PgFixture {
	config: Config,
	pub(super) schema: String,
	pub settings: Value,
	cleanup: bool,
	batcher: Option<Batcher>,
}

/// Validate both host names and address overrides before any connection is attempted.
fn validate_loopback_config(config: &Config) -> Result<()> {
	if config.get_hosts().is_empty()
		|| !config
			.get_hosts()
			.iter()
			.all(|host| matches!(host, Host::Tcp(name) if name == "127.0.0.1" || name == "::1"))
		|| !config.get_hostaddrs().iter().all(|address| {
			*address == IpAddr::V4(Ipv4Addr::LOCALHOST)
				|| *address == IpAddr::V6(Ipv6Addr::LOCALHOST)
		}) {
		return Err(
			"PostgreSQL benchmark requires an explicit loopback TCP host (127.0.0.1 or ::1)".into(),
		);
	}
	Ok(())
}

impl PgFixture {
	pub fn create(dsn: &str, lineage: SnapshotLineage) -> Result<Rc<Self>> {
		let config = Config::from_str(dsn)?;
		validate_loopback_config(&config)?;
		let schema = format!(
			"bcbench_{}",
			lineage.as_bytes()[..16]
				.iter()
				.map(|b| format!("{b:02x}"))
				.collect::<String>()
		);
		let mut client = config.connect(NoTls)?;
		let settings = settings(&mut client)?;
		client.batch_execute(&format!("CREATE SCHEMA {schema}"))?;
		let result = Rc::new(Self {
			config,
			schema,
			settings,
			cleanup: true,
			batcher: None,
		});
		// A VOLATILE function's statements obtain fresh READ COMMITTED snapshots. In particular,
		// validation runs AFTER any advisory-lock wait, rather than using the calling SELECT's
		// pre-wait snapshot. Locks cover both reads (including absence) and blind writes.
		client.batch_execute(&format!(r#"
CREATE TABLE {s}.snapshot (
 id integer PRIMARY KEY CHECK(id=1), lineage bytea NOT NULL,
 generation bytea NOT NULL, digest bytea NOT NULL, value bytea NOT NULL
);
CREATE TABLE {s}.peer_rows (key bytea PRIMARY KEY, value bytea NOT NULL);
CREATE FUNCTION {s}.commit_rows(read_keys bytea[], expected_values bytea[], write_keys bytea[], write_values bytea[])
RETURNS boolean LANGUAGE plpgsql VOLATILE AS $body$
DECLARE lock_id bigint; item record; actual bytea;
BEGIN
 IF cardinality(read_keys) <> cardinality(expected_values) OR cardinality(write_keys) <> cardinality(write_values) THEN
  RAISE EXCEPTION 'invalid benchmark read/write batch';
 END IF;
 FOR lock_id IN
  SELECT DISTINCT hashtextextended('{s}:' || encode(k, 'hex'), 0) AS id
  FROM unnest(read_keys || write_keys) AS keys(k) ORDER BY id
 LOOP
  PERFORM pg_advisory_xact_lock(lock_id);
 END LOOP;
 FOR item IN SELECT * FROM unnest(read_keys, expected_values) AS r(key, expected) LOOP
  SELECT value INTO actual FROM {s}.peer_rows WHERE key=item.key;
  IF actual IS DISTINCT FROM item.expected THEN RETURN false; END IF;
 END LOOP;
 FOR item IN SELECT * FROM unnest(write_keys, write_values) AS w(key, value) LOOP
  INSERT INTO {s}.peer_rows(key,value) VALUES(item.key,item.value)
  ON CONFLICT(key) DO UPDATE SET value=excluded.value;
 END LOOP;
 RETURN true;
END $body$;
"#, s=result.schema))?;
		Ok(result)
	}

	/// Share one durable commit connection across independent resident row owners.
	pub fn create_batched(
		dsn: &str,
		lineage: SnapshotLineage,
		config: BatchConfig,
	) -> Result<Rc<Self>> {
		let mut fixture = Self::create(dsn, lineage)?;
		let mut client = fixture.connect()?;
		// Prelock the whole union, rather than acquiring differently ordered subsets for each
		// request. Each request validates separately: a stale expectation has no writes, while a
		// SQL exception rolls back this entire outer statement, including earlier requests.
		client.batch_execute(&format!(r#"
CREATE FUNCTION {s}.commit_batch(read_keys bytea[], expected_values bytea[], write_keys bytea[], write_values bytea[], read_sizes integer[], write_sizes integer[])
RETURNS boolean[] LANGUAGE plpgsql VOLATILE AS $body$
DECLARE lock_id bigint; i integer; read_start integer := 1; write_start integer := 1;
 outcomes boolean[] := ARRAY[]::boolean[];
BEGIN
 IF cardinality(read_keys) <> cardinality(expected_values)
  OR cardinality(write_keys) <> cardinality(write_values)
  OR cardinality(read_sizes) <> cardinality(write_sizes)
  OR EXISTS(SELECT FROM unnest(read_sizes || write_sizes) AS sizes(n) WHERE n < 0)
  OR (SELECT coalesce(sum(n),0) FROM unnest(read_sizes) AS sizes(n)) <> cardinality(read_keys)
  OR (SELECT coalesce(sum(n),0) FROM unnest(write_sizes) AS sizes(n)) <> cardinality(write_keys) THEN
  RAISE EXCEPTION 'invalid benchmark durable batch';
 END IF;
 FOR lock_id IN
  SELECT DISTINCT hashtextextended('{s}:' || encode(k, 'hex'), 0) AS id
  FROM unnest(read_keys || write_keys) AS keys(k) ORDER BY id
 LOOP
  PERFORM pg_advisory_xact_lock(lock_id);
 END LOOP;
 FOR i IN 1..cardinality(read_sizes) LOOP
  outcomes := array_append(outcomes, {s}.commit_rows(
   read_keys[read_start:read_start+read_sizes[i]-1],
   expected_values[read_start:read_start+read_sizes[i]-1],
   write_keys[write_start:write_start+write_sizes[i]-1],
   write_values[write_start:write_start+write_sizes[i]-1]));
  read_start := read_start + read_sizes[i];
  write_start := write_start + write_sizes[i];
 END LOOP;
 RETURN outcomes;
END $body$;
"#, s=fixture.schema))?;
		let statement = client.prepare(&format!(
			"SELECT {}.commit_batch($1,$2,$3,$4,$5,$6)",
			fixture.schema
		))?;
		let batcher = Batcher::start(config, move |changes| {
			commit_batch(&mut client, &statement, changes)
		})?;
		let owned = Rc::get_mut(&mut fixture).expect("new fixture has one owner");
		owned.batcher = Some(batcher);
		owned.settings["transport"] = json!(
			"loopback TCP, prepared statements, owner read connections and one shared durable commit connection"
		);
		Ok(fixture)
	}

	pub(super) fn connect(&self) -> Result<Client> {
		let mut client = self.config.connect(NoTls)?;
		client.batch_execute("SET synchronous_commit=on; SET default_transaction_isolation='read committed'; SET statement_timeout='30s'; SET lock_timeout='10s'")?;
		// Validate durability for every adapter connection, outside native-operation timing.
		settings(&mut client)?;
		Ok(client)
	}

	pub fn checkpoint(&self) -> Result<()> {
		self.connect()?.batch_execute("CHECKPOINT")?;
		Ok(())
	}

	pub fn footprint(&self, row_store: bool) -> Result<Value> {
		let table = if row_store { "peer_rows" } else { "snapshot" };
		let relation = format!("{}.{}", self.schema, table);
		let row = self.connect()?.query_one(&format!("SELECT count(*),coalesce(sum(octet_length(value)),0)::bigint,pg_total_relation_size('{relation}'::regclass) FROM {relation}"), &[])?;
		let rows: i64 = row.get(0);
		let value_bytes: i64 = row.get(1);
		let relation_bytes: i64 = row.get(2);
		Ok(
			json!({"rows":rows,"stored_value_bytes":value_bytes,"relation_bytes_including_indexes_and_toast":relation_bytes}),
		)
	}

	pub fn worker_copy(&self) -> Self {
		Self {
			config: self.config.clone(),
			schema: self.schema.clone(),
			settings: self.settings.clone(),
			cleanup: false,
			batcher: self.batcher.clone(),
		}
	}

	#[cfg(test)]
	pub(super) fn batch_pending_for_test(&self) -> usize {
		self.batcher.as_ref().map_or(0, Batcher::pending_for_test)
	}

	#[cfg(test)]
	pub fn reject_z(&self) {
		self.connect().unwrap().batch_execute(&format!(r#"
CREATE FUNCTION {s}.reject_z() RETURNS trigger LANGUAGE plpgsql AS $body$
BEGIN IF NEW.key=decode('7a','hex') THEN RAISE EXCEPTION 'injected failure'; END IF; RETURN NEW; END $body$;
CREATE TRIGGER reject_z BEFORE INSERT OR UPDATE ON {s}.peer_rows FOR EACH ROW EXECUTE FUNCTION {s}.reject_z();
"#,s=self.schema)).unwrap();
	}
}

impl Drop for PgFixture {
	fn drop(&mut self) {
		if !self.cleanup {
			return;
		}
		if let Some(batcher) = &self.batcher
			&& let Err(error) = batcher.shutdown()
		{
			eprintln!("could not shut down benchmark batch coordinator: {error}");
			return; // Preserve the owned schema if coordinator termination cannot be confirmed.
		}
		if let Ok(mut client) = self.config.connect(NoTls)
			&& let Err(error) =
				client.batch_execute(&format!("DROP SCHEMA {} CASCADE", self.schema))
		{
			eprintln!("could not clean benchmark schema {}: {error}", self.schema);
		}
	}
}

fn commit_batch(
	client: &mut Client,
	statement: &Statement,
	changes: &[ChangeSet],
) -> std::result::Result<Vec<bool>, RowError> {
	let mut read_keys = Vec::new();
	let mut expected = Vec::new();
	let mut write_keys = Vec::new();
	let mut values = Vec::new();
	let mut read_sizes = Vec::new();
	let mut write_sizes = Vec::new();
	for change in changes {
		read_sizes.push(i32::try_from(change.reads.len()).map_err(|_| {
			RowError::Storage("batch read set exceeds PostgreSQL array limits".into())
		})?);
		write_sizes.push(i32::try_from(change.writes.len()).map_err(|_| {
			RowError::Storage("batch write set exceeds PostgreSQL array limits".into())
		})?);
		for (key, value) in &change.reads {
			read_keys.push(key.as_slice());
			expected.push(value.as_deref());
		}
		for (key, value) in &change.writes {
			write_keys.push(key.as_slice());
			values.push(value.as_slice());
		}
	}
	// query_one drains the response through ReadyForQuery, so successful return includes the
	// implicit outer transaction's durable COMMIT acknowledgement (synchronous_commit=on).
	// DataRow alone would not establish that boundary. Any error, including a lost COMMIT
	// acknowledgement, propagates to every caller; the coordinator must never retry callbacks.
	client
		.query_one(
			statement,
			&[
				&read_keys,
				&expected,
				&write_keys,
				&values,
				&read_sizes,
				&write_sizes,
			],
		)
		.map_err(storage)?
		.try_get(0)
		.map_err(storage)
}

fn settings(client: &mut Client) -> Result<Value> {
	// An explicit inet::text cast retains /32 or /128; host() returns just the IP address.
	let row = client.query_one("SELECT version(),host(inet_server_addr()),inet_server_port(),current_setting('fsync'),current_setting('synchronous_commit'),current_setting('full_page_writes'),current_setting('default_transaction_isolation'),current_setting('shared_buffers'),current_setting('checkpoint_timeout'),current_setting('max_wal_size'),current_setting('wal_sync_method'),current_setting('autovacuum')", &[])?;
	let address: Option<String> = row.get(1);
	if !matches!(address.as_deref(), Some("127.0.0.1" | "::1")) {
		return Err("PostgreSQL connection is not loopback TCP".into());
	}
	for column in [3, 4, 5] {
		let setting: String = row.get(column);
		if setting != "on" {
			return Err("PostgreSQL benchmark requires fsync, synchronous_commit, and full_page_writes enabled".into());
		}
	}
	let isolation: String = row.get(6);
	if isolation != "read committed" {
		return Err(
			"PostgreSQL benchmark requires READ COMMITTED for fresh post-lock function snapshots"
				.into(),
		);
	}
	Ok(json!({
		"server_version":row.get::<_,String>(0),"address":address,"port":row.get::<_,i32>(2),
		"fsync":row.get::<_,String>(3),"synchronous_commit":row.get::<_,String>(4),
		"full_page_writes":row.get::<_,String>(5),"isolation":isolation,
		"shared_buffers":row.get::<_,String>(7),"checkpoint_timeout":row.get::<_,String>(8),
		"max_wal_size":row.get::<_,String>(9),"wal_sync_method":row.get::<_,String>(10),
		"autovacuum":row.get::<_,String>(11),"transport":"loopback TCP, prepared statements, one connection per resident owner"
	}))
}

fn request(counts: &Counters) {
	counts.sql_calls.set(counts.sql_calls.get() + 1);
	counts
		.network_exchanges
		.set(counts.network_exchanges.get() + 1);
}

pub struct PgSnapshotStore {
	client: RefCell<Client>,
	load: Statement,
	insert: Statement,
	update: Statement,
	counts: Rc<Counters>,
	_fixture: Rc<PgFixture>,
}

impl PgSnapshotStore {
	pub fn open(fixture: Rc<PgFixture>, counts: Rc<Counters>) -> Result<Self> {
		let mut client = fixture.connect()?;
		let table = format!("{}.snapshot", fixture.schema);
		let load = client.prepare(&format!("SELECT value FROM {table} WHERE id=1"))?;
		let insert = client.prepare(&format!("INSERT INTO {table}(id,lineage,generation,digest,value) VALUES(1,$1,$2,$3,$4) ON CONFLICT(id) DO NOTHING"))?;
		let update = client.prepare(&format!("UPDATE {table} SET lineage=$1,generation=$2,digest=$3,value=$4 WHERE id=1 AND lineage=$5 AND generation=$6 AND digest=$7"))?;
		Ok(Self {
			client: RefCell::new(client),
			load,
			insert,
			update,
			counts,
			_fixture: fixture,
		})
	}
}

impl SnapshotStore for PgSnapshotStore {
	fn load(&self) -> Option<ServerSnapshot> {
		let _call = self.counts.call("snapshot_load");
		request(&self.counts);
		self.counts.reads.set(self.counts.reads.get() + 1);
		self.client
			.borrow_mut()
			.query_opt(&self.load, &[])
			.expect("benchmark snapshot load failed")
			.map(|row| {
				let value: Vec<u8> = row.get(0);
				self.counts
					.value_bytes_read
					.set(self.counts.value_bytes_read.get() + value.len() as u64);
				ServerSnapshot::from_bytes(value)
			})
	}
	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let next = replacement
			.validate_successor(expected)
			.expect("valid snapshot successor");
		request(&self.counts);
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		let lineage = next.lineage();
		let generation = next.generation().to_le_bytes();
		let digest = next.digest();
		let params: [&(dyn postgres::types::ToSql + Sync); 4] = [
			&lineage.as_bytes().as_slice(),
			&generation.as_slice(),
			&digest.as_slice(),
			&replacement.as_bytes(),
		];
		let call = self.counts.call("snapshot_commit");
		let changed = match expected {
			None => self.client.borrow_mut().execute(&self.insert, &params),
			Some(previous) => {
				self.counts
					.validation_rows
					.set(self.counts.validation_rows.get() + 1);
				self.counts
					.validation_bytes_sent
					.set(self.counts.validation_bytes_sent.get() + 72);
				self.client.borrow_mut().execute(
					&self.update,
					&[
						params[0],
						params[1],
						params[2],
						params[3],
						&previous.lineage().as_bytes().as_slice(),
						&previous.generation().to_le_bytes().as_slice(),
						&previous.digest().as_slice(),
					],
				)
			}
		}
		.expect("benchmark snapshot commit failed");
		drop(call);
		if changed == 1 {
			self.counts.writes.set(self.counts.writes.get() + 1);
			self.counts
				.value_bytes_written
				.set(self.counts.value_bytes_written.get() + replacement.as_bytes().len() as u64);
		}
		changed == 1
	}
}

pub struct PgRowStore {
	client: Client,
	load: Statement,
	commit: Statement,
	counts: Rc<Counters>,
	_fixture: Rc<PgFixture>,
}

impl PgRowStore {
	pub fn open(fixture: Rc<PgFixture>, counts: Rc<Counters>) -> Result<Self> {
		let mut client = fixture.connect()?;
		let load = client.prepare(&format!(
			"SELECT value FROM {}.peer_rows WHERE key=$1",
			fixture.schema
		))?;
		let commit = client.prepare(&format!(
			"SELECT {}.commit_rows($1,$2,$3,$4)",
			fixture.schema
		))?;
		Ok(Self {
			client,
			load,
			commit,
			counts,
			_fixture: fixture,
		})
	}
}

impl RowStore for PgRowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> std::result::Result<(), RowError>,
	) -> std::result::Result<(), RowError> {
		let mut pending = Buffered::new(
			|key: &[u8]| {
				let _call = self.counts.call("row_load");
				request(&self.counts);
				self.counts.reads.set(self.counts.reads.get() + 1);
				let value = self
					.client
					.query_opt(&self.load, &[&key])
					.map_err(storage)?
					.map(|row| row.get::<_, Vec<u8>>(0));
				self.counts.value_bytes_read.set(
					self.counts.value_bytes_read.get()
						+ value.as_ref().map_or(0, |v| v.len() as u64),
				);
				Ok(value)
			},
			&self.counts,
		);
		operation(&mut pending)?;
		if let Some(error) = pending.failure {
			return Err(error);
		}
		self.counts
			.validation_rows
			.set(self.counts.validation_rows.get() + pending.reads.len() as u64);
		self.counts.validation_bytes_sent.set(
			self.counts.validation_bytes_sent.get()
				+ pending
					.reads
					.values()
					.filter_map(Option::as_ref)
					.map(|v| v.len() as u64)
					.sum::<u64>(),
		);
		if let Some(batcher) = &self._fixture.batcher {
			let writes = pending.writes.len() as u64;
			let written_bytes = pending.writes.values().map(|v| v.len() as u64).sum::<u64>();
			let call = self.counts.call("row_batch_commit");
			let receipt = batcher.commit(ChangeSet::new(RowChanges {
				reads: pending.reads,
				writes: pending.writes,
			}))?;
			drop(call);
			if receipt.leader {
				request(&self.counts);
				self.counts
					.transactions
					.set(self.counts.transactions.get() + 1);
			}
			receipt.status?;
			self.counts.writes.set(self.counts.writes.get() + writes);
			self.counts
				.value_bytes_written
				.set(self.counts.value_bytes_written.get() + written_bytes);
			return Ok(());
		}
		let (read_keys, expected): (Vec<_>, Vec<_>) = pending.reads.into_iter().unzip();
		let (write_keys, values): (Vec<_>, Vec<_>) = pending.writes.into_iter().unzip();
		request(&self.counts);
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		let call = self.counts.call("row_commit");
		let committed: bool = self
			.client
			.query_one(&self.commit, &[&read_keys, &expected, &write_keys, &values])
			.map_err(storage)?
			.get(0);
		drop(call);
		if !committed {
			return Err(RowError::Conflict);
		}
		self.counts
			.writes
			.set(self.counts.writes.get() + values.len() as u64);
		self.counts.value_bytes_written.set(
			self.counts.value_bytes_written.get()
				+ values.iter().map(|v| v.len() as u64).sum::<u64>(),
		);
		Ok(())
	}
}

fn storage(error: postgres::Error) -> RowError {
	RowError::Storage(error.to_string())
}

#[test]
fn loopback_configuration_accepts_explicit_canonical_hosts_without_connecting() {
	for (host, addresses) in [
		("127.0.0.1", ""),
		("::1", ""),
		("127.0.0.1,::1", ""),
		("127.0.0.1", "127.0.0.1"),
		("127.0.0.1", "::1"),
		("::1", "::1"),
		("127.0.0.1,::1", "127.0.0.1,::1"),
	] {
		let override_option = if addresses.is_empty() {
			String::new()
		} else {
			format!(" hostaddr={addresses}")
		};
		let config = Config::from_str(&format!(
			"host={host}{override_option} port=55439 user=bcbench dbname=postgres"
		))
		.unwrap();
		validate_loopback_config(&config).unwrap();
		let hosts: Vec<_> = config
			.get_hosts()
			.iter()
			.map(|host| match host {
				Host::Tcp(name) => name.as_str(),
				_ => panic!("accepted a non-TCP host"),
			})
			.collect();
		assert_eq!(hosts, host.split(',').collect::<Vec<_>>());
		let parsed_addresses: Vec<_> = config
			.get_hostaddrs()
			.iter()
			.map(ToString::to_string)
			.collect();
		let expected_addresses: Vec<_> = addresses
			.split(',')
			.filter(|address| !address.is_empty())
			.collect();
		assert_eq!(parsed_addresses, expected_addresses);
		assert_eq!(config.get_ports(), &[55439]);
		assert_eq!(config.get_user(), Some("bcbench"));
		assert_eq!(config.get_dbname(), Some("postgres"));
	}
}

#[test]
fn loopback_configuration_rejects_missing_socket_hostname_and_external_overrides() {
	// These tests call only the parser/policy helper. Even an accepting mutant cannot dial a host.
	for dsn in [
		"",
		"user=bcbench dbname=postgres",
		"host=''",
		"host=/tmp",
		"host=localhost",
		"host=203.0.113.1",
		"host=127.0.0.2",
		"host=::ffff:127.0.0.1",
		"host=127.0.0.1,localhost",
		"host=localhost,::1",
		"host=127.0.0.1,203.0.113.1",
		"host=127.0.0.1,/tmp",
		"hostaddr=127.0.0.1",
		"host=127.0.0.1 hostaddr=203.0.113.1",
		"host=::1 hostaddr=2001:db8::1",
		"host=127.0.0.1 hostaddr=127.0.0.2",
		"host=127.0.0.1 hostaddr=::ffff:127.0.0.1",
		"host=127.0.0.1,::1 hostaddr=127.0.0.1,203.0.113.1",
		"host=127.0.0.1,::1 hostaddr=2001:db8::1,::1",
	] {
		let config = Config::from_str(dsn).unwrap();
		let error =
			validate_loopback_config(&config).expect_err("noncanonical connection target accepted");
		assert_eq!(
			error.to_string(),
			"PostgreSQL benchmark requires an explicit loopback TCP host (127.0.0.1 or ::1)",
			"unexpected rejection for {dsn:?}"
		);
	}
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn postgres_fixture_lifetime_preserves_shared_owners_and_rejects_duplicate_ownership() {
	struct OwnedSchema {
		client: Client,
		schema: String,
	}
	impl OwnedSchema {
		fn exists(&mut self) -> bool {
			self.client
				.query_one(
					"SELECT EXISTS(SELECT FROM pg_namespace WHERE nspname=$1)",
					&[&self.schema],
				)
				.unwrap()
				.get(0)
		}
		fn assert_marker(&mut self) {
			let value: Vec<u8> = self
				.client
				.query_one(
					&format!("SELECT value FROM {}.peer_rows WHERE key=$1", self.schema),
					&[&b"marker".as_slice()],
				)
				.unwrap()
				.get(0);
			assert_eq!(value, b"owned data survives");
		}
	}
	impl Drop for OwnedSchema {
		fn drop(&mut self) {
			// Cleanup only this test's successfully created random namespace, also after a failing
			// assertion under mutation. It runs after the fixture-lifetime assertions, not before.
			if let Err(error) = self
				.client
				.batch_execute(&format!("DROP SCHEMA IF EXISTS {} CASCADE", self.schema))
			{
				eprintln!("could not clean owned fixture-lifetime schema: {error}");
			}
		}
	}

	let mut lineage = [0; 32];
	beaconcrypt::crypto::random::fill_bytes(&mut lineage);
	let dsn = std::env::var("BEACONCRYPT_BENCH_POSTGRES").expect("set live PostgreSQL DSN");
	let fixture = PgFixture::create(&dsn, SnapshotLineage::from_bytes(lineage)).unwrap();
	let mut observer = OwnedSchema {
		client: fixture.connect().unwrap(),
		schema: fixture.schema.clone(),
	};
	assert!(observer.exists());
	observer
		.client
		.batch_execute(&format!(
			"INSERT INTO {}.peer_rows VALUES(decode('6d61726b6572','hex'),convert_to('owned data survives','UTF8'))",
			observer.schema
		))
		.unwrap();
	let shared_owner = Rc::clone(&fixture);
	drop(fixture.worker_copy());
	assert!(
		observer.exists(),
		"a worker copy must not own schema cleanup"
	);
	observer.assert_marker();
	let duplicate = PgFixture::create(&dsn, SnapshotLineage::from_bytes(lineage))
		.err()
		.expect("creating an already owned namespace must fail");
	assert_eq!(
		duplicate
			.downcast_ref::<postgres::Error>()
			.unwrap()
			.as_db_error()
			.unwrap()
			.code(),
		&postgres::error::SqlState::DUPLICATE_SCHEMA
	);
	assert!(
		observer.exists(),
		"a failed duplicate creation must not remove the first owner's schema"
	);
	observer.assert_marker();
	drop(fixture);
	assert!(
		observer.exists(),
		"an Rc owner still keeps the fixture alive"
	);
	observer.assert_marker();
	let nonowning_worker = shared_owner.worker_copy();
	drop(shared_owner);
	assert!(
		!observer.exists(),
		"the final owning reference must remove its namespace"
	);
	drop(nonowning_worker);
	assert!(!observer.exists());
}

#[test]
#[ignore = "requires dedicated durable PostgreSQL over loopback TCP"]
fn postgres_validation_observes_commit_after_advisory_lock_wait() {
	use std::{
		sync::mpsc,
		time::{Duration, Instant},
	};
	let mut lineage = [0; 32];
	beaconcrypt::crypto::random::fill_bytes(&mut lineage);
	let fixture = PgFixture::create(
		&std::env::var("BEACONCRYPT_BENCH_POSTGRES").expect("set live PostgreSQL DSN"),
		SnapshotLineage::from_bytes(lineage),
	)
	.unwrap();
	let mut initial = PgRowStore::open(Rc::clone(&fixture), Rc::new(Counters::default())).unwrap();
	initial
		.transaction(&mut |tx| tx.store(b"held", b"old"))
		.unwrap();
	let mut control = fixture.connect().unwrap();
	let mut held = control.transaction().unwrap();
	// The direct writer participates in exactly the adapter's schema/key lock protocol.
	held.query_one(
		"SELECT pg_advisory_xact_lock(hashtextextended($1,0))",
		&[&format!("{}:68656c64", fixture.schema)],
	)
	.unwrap();
	let worker_fixture = fixture.worker_copy();
	let (started, pid) = mpsc::sync_channel(1);
	let worker = std::thread::spawn(move || {
		let mut store =
			PgRowStore::open(Rc::new(worker_fixture), Rc::new(Counters::default())).unwrap();
		let backend_pid: i32 = store
			.client
			.query_one("SELECT pg_backend_pid()", &[])
			.unwrap()
			.get(0);
		started.send(backend_pid).unwrap();
		store.transaction(&mut |tx| {
			tx.expect(b"held", Some(b"old"))?;
			tx.store(b"held", b"candidate")
		})
	});
	let backend_pid = pid.recv_timeout(Duration::from_secs(5)).unwrap();
	let deadline = Instant::now() + Duration::from_secs(5);
	loop {
		let waiting: bool = held
			.query_one(
				"SELECT EXISTS(SELECT FROM pg_locks WHERE pid=$1 AND locktype='advisory' AND NOT granted)",
				&[&backend_pid],
			)
			.unwrap()
			.get(0);
		if waiting {
			break;
		}
		assert!(
			Instant::now() < deadline,
			"contender never waited on the held advisory lock"
		);
		// Poll observed lock state; the delay is not used as evidence that waiting began.
		std::thread::sleep(Duration::from_millis(10));
	}
	held.execute(
		&format!(
			"UPDATE {}.peer_rows SET value=$1 WHERE key=$2",
			fixture.schema
		),
		&[&b"winner".as_slice(), &b"held".as_slice()],
	)
	.unwrap();
	held.commit().unwrap();
	assert_eq!(worker.join().unwrap(), Err(RowError::Conflict));
	initial
		.transaction(&mut |tx| {
			assert_eq!(tx.load(b"held")?, Some(b"winner".to_vec()));
			Ok(())
		})
		.unwrap();
}

#[test]
#[ignore = "requires dedicated PostgreSQL with authority to create and drop an owned test role"]
fn postgres_checkpoint_propagates_permission_error_for_an_owned_unprivileged_role() {
	struct OwnedRole {
		client: Client,
		name: Option<String>,
	}
	impl Drop for OwnedRole {
		fn drop(&mut self) {
			if let Some(name) = &self.name
				&& let Err(error) = self.client.batch_execute(&format!("DROP ROLE {name}"))
			{
				eprintln!("could not remove owned checkpoint-test role {name}: {error}");
			}
		}
	}

	let mut lineage = [0; 32];
	beaconcrypt::crypto::random::fill_bytes(&mut lineage);
	let fixture = PgFixture::create(
		&std::env::var("BEACONCRYPT_BENCH_POSTGRES").expect("set live PostgreSQL DSN"),
		SnapshotLineage::from_bytes(lineage),
	)
	.unwrap();
	// The random fixture schema supplies a unique, identifier-safe role name under 63 bytes.
	let role = format!("{}_checkpoint_role", fixture.schema);
	let mut administrator = fixture.connect().unwrap();
	administrator
		.batch_execute(&format!(
			"CREATE ROLE {role} LOGIN NOSUPERUSER NOINHERIT NOCREATEDB NOCREATEROLE NOREPLICATION"
		))
		.unwrap();
	let mut cleanup = OwnedRole {
		client: administrator,
		name: Some(role.clone()),
	};
	let mut restricted = fixture.worker_copy();
	restricted.config.user(&role);
	{
		let mut ordinary = restricted.connect().unwrap();
		assert_eq!(
			ordinary
				.query_one("SELECT 1::integer", &[])
				.unwrap()
				.get::<_, i32>(0),
			1
		);
	} // Ordinary connection is closed before testing the privileged statement.
	let error = restricted
		.checkpoint()
		.expect_err("CHECKPOINT must not succeed for this new unprivileged role");
	let error = error
		.downcast_ref::<postgres::Error>()
		.expect("preserve the typed PostgreSQL error");
	assert_eq!(
		error.as_db_error().unwrap().code(),
		&postgres::error::SqlState::INSUFFICIENT_PRIVILEGE
	);
	drop(restricted); // No restricted client or handle remains during role cleanup.
	cleanup
		.client
		.batch_execute(&format!("DROP ROLE {role}"))
		.unwrap();
	cleanup.name = None;
	let exists: bool = cleanup
		.client
		.query_one(
			"SELECT EXISTS(SELECT FROM pg_roles WHERE rolname=$1)",
			&[&role],
		)
		.unwrap()
		.get(0);
	assert!(!exists);
}
