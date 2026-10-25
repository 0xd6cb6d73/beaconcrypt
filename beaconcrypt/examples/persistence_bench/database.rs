// SPDX-License-Identifier: 0BSD

use std::{
	cell::{Cell, RefCell},
	path::Path,
	rc::Rc,
	time::{Duration, Instant},
};

use beaconcrypt::{
	RowError, RowStore, RowTransaction, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};
use rusqlite::{Connection, OptionalExtension, TransactionBehavior};

use super::buffered::Buffered;
use serde::Serialize;

pub const SQL_SETTINGS: &str = "journal_mode=WAL;synchronous=FULL;page_size=4096;cache_size=-20000;wal_autocheckpoint=1000;busy_timeout_ms=5000";

#[derive(Default)]
pub struct Counters {
	trace: RefCell<Option<(Instant, Vec<DatabaseSpan>)>>,
	pub network_exchanges: Cell<u64>,
	pub sql_calls: Cell<u64>,
	pub validation_bytes_sent: Cell<u64>,
	pub validation_rows: Cell<u64>,
	pub value_bytes_expected: Cell<u64>,
	pub stores: Cell<u64>,
	pub expects: Cell<u64>,
	pub loads: Cell<u64>,
	pub reads: Cell<u64>,
	pub writes: Cell<u64>,
	pub transactions: Cell<u64>,
	pub value_bytes_read: Cell<u64>,
	pub value_bytes_written: Cell<u64>,
	pub head_bytes_read: Cell<u64>,
}

/// A client-side database call interval, including lock/network/commit waits, not server CPU time.
#[derive(Debug, Serialize)]
pub struct DatabaseSpan {
	pub kind: &'static str,
	pub start_ns: u64,
	pub end_ns: u64,
}

pub struct DatabaseCall<'a> {
	counts: &'a Counters,
	start: Option<Instant>,
	kind: &'static str,
}

impl Drop for DatabaseCall<'_> {
	fn drop(&mut self) {
		if let Some(start) = self.start {
			let end = Instant::now();
			if let Some((epoch, spans)) = self.counts.trace.borrow_mut().as_mut() {
				#[cfg(test)]
				assert!(
					spans.len() < spans.capacity(),
					"database tracing must be preallocated before measured callbacks"
				);
				spans.push(DatabaseSpan {
					kind: self.kind,
					start_ns: super::nanos(start.duration_since(*epoch)),
					end_ns: super::nanos(end.duration_since(*epoch)),
				});
			}
		}
	}
}

#[derive(Debug, Serialize)]
pub struct Counts {
	pub network_exchanges: u64,
	pub sql_calls: u64,
	pub validation_bytes_sent: u64,
	pub validation_rows: u64,
	pub value_bytes_expected: u64,
	pub stores: u64,
	pub expects: u64,
	pub loads: u64,
	reads: u64,
	writes: u64,
	transactions: u64,
	value_bytes_read: u64,
	value_bytes_written: u64,
	head_bytes_read: u64,
}

impl Counters {
	pub fn enable_trace(&self, epoch: Instant, capacity: usize) {
		*self.trace.borrow_mut() = Some((epoch, Vec::with_capacity(capacity)));
	}
	pub fn take_trace(&self) -> Vec<DatabaseSpan> {
		self.trace
			.borrow_mut()
			.take()
			.map_or_else(Vec::new, |(_, spans)| spans)
	}
	pub fn call(&self, kind: &'static str) -> DatabaseCall<'_> {
		let start = self.trace.borrow().as_ref().map(|_| Instant::now());
		DatabaseCall {
			counts: self,
			start,
			kind,
		}
	}
	pub fn take(&self) -> Counts {
		Counts {
			network_exchanges: self.network_exchanges.replace(0),
			sql_calls: self.sql_calls.replace(0),
			validation_bytes_sent: self.validation_bytes_sent.replace(0),
			validation_rows: self.validation_rows.replace(0),
			value_bytes_expected: self.value_bytes_expected.replace(0),
			stores: self.stores.replace(0),
			expects: self.expects.replace(0),
			loads: self.loads.replace(0),
			reads: self.reads.replace(0),
			writes: self.writes.replace(0),
			transactions: self.transactions.replace(0),
			value_bytes_read: self.value_bytes_read.replace(0),
			value_bytes_written: self.value_bytes_written.replace(0),
			head_bytes_read: self.head_bytes_read.replace(0),
		}
	}
}

fn open(path: &Path) -> rusqlite::Result<Connection> {
	let connection = Connection::open(path)?;
	connection.busy_timeout(Duration::from_secs(5))?;
	connection.pragma_update(None, "page_size", 4096)?;
	connection.pragma_update(None, "journal_mode", "WAL")?;
	connection.pragma_update(None, "synchronous", "FULL")?;
	connection.pragma_update(None, "cache_size", -20_000)?;
	connection.pragma_update(None, "wal_autocheckpoint", 1000)?;
	let mode: String = connection.pragma_query_value(None, "journal_mode", |row| row.get(0))?;
	let sync: i64 = connection.pragma_query_value(None, "synchronous", |row| row.get(0))?;
	let page_size: i64 = connection.pragma_query_value(None, "page_size", |row| row.get(0))?;
	assert_eq!(mode, "wal");
	assert_eq!(sync, 2);
	assert_eq!(page_size, 4096);
	Ok(connection)
}

pub struct SqlSnapshotStore {
	connection: Connection,
	counts: Rc<Counters>,
}

impl SqlSnapshotStore {
	pub fn open(path: &Path, counts: Rc<Counters>) -> rusqlite::Result<Self> {
		let connection = open(path)?;
		connection.execute_batch(
			"CREATE TABLE IF NOT EXISTS snapshot (
				id INTEGER PRIMARY KEY CHECK(id=1),
				lineage BLOB NOT NULL, generation BLOB NOT NULL, digest BLOB NOT NULL,
				value BLOB NOT NULL
			);",
		)?;
		Ok(Self { connection, counts })
	}

	fn commit(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> rusqlite::Result<bool> {
		let _call = self.counts.call("snapshot_commit");
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		let tx = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)?;
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		self.counts.reads.set(self.counts.reads.get() + 1);
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		let stored: Option<(Vec<u8>, Vec<u8>, Vec<u8>)> = tx
			.query_row(
				"SELECT lineage, generation, digest FROM snapshot WHERE id=1",
				[],
				|row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
			)
			.optional()?;
		let current = stored.map(|(lineage, generation, digest)| {
			self.counts
				.head_bytes_read
				.set(self.counts.head_bytes_read.get() + 72);
			SnapshotHead::from_parts(
				SnapshotLineage::from_bytes(lineage.try_into().expect("stored lineage length")),
				u64::from_le_bytes(generation.try_into().expect("stored generation length")),
				digest.try_into().expect("stored digest length"),
			)
		});
		if current.as_ref() != expected {
			return Ok(false);
		}
		let next = replacement
			.validate_successor(expected)
			.expect("valid snapshot successor");
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		tx.execute(
			"INSERT INTO snapshot (id,lineage,generation,digest,value) VALUES (1,?1,?2,?3,?4)
			 ON CONFLICT(id) DO UPDATE SET lineage=excluded.lineage,
			 generation=excluded.generation,digest=excluded.digest,value=excluded.value",
			rusqlite::params![
				next.lineage().as_bytes().as_slice(),
				next.generation().to_le_bytes().as_slice(),
				next.digest().as_slice(),
				replacement.as_bytes(),
			],
		)?;
		self.counts.writes.set(self.counts.writes.get() + 1);
		self.counts
			.value_bytes_written
			.set(self.counts.value_bytes_written.get() + replacement.as_bytes().len() as u64);
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		tx.commit()?;
		Ok(true)
	}
}

impl SnapshotStore for SqlSnapshotStore {
	fn load(&self) -> Option<ServerSnapshot> {
		let _call = self.counts.call("snapshot_load");
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		self.counts.reads.set(self.counts.reads.get() + 1);
		let bytes: Option<Vec<u8>> = self
			.connection
			.query_row("SELECT value FROM snapshot WHERE id=1", [], |row| {
				row.get(0)
			})
			.optional()
			.expect("benchmark snapshot read must succeed");
		bytes.map(|bytes| {
			self.counts
				.value_bytes_read
				.set(self.counts.value_bytes_read.get() + bytes.len() as u64);
			ServerSnapshot::from_bytes(bytes)
		})
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		// The benchmark fails rather than converting a database error into a misleading rejection.
		self.commit(expected, replacement)
			.expect("benchmark snapshot commit must succeed")
	}
}

pub struct SqlRowStore {
	connection: Connection,
	counts: Rc<Counters>,
}

impl SqlRowStore {
	pub fn open(path: &Path, counts: Rc<Counters>) -> rusqlite::Result<Self> {
		let connection = open(path)?;
		connection.execute_batch(
			"CREATE TABLE IF NOT EXISTS peer_rows (
				key BLOB PRIMARY KEY NOT NULL, value BLOB NOT NULL
			) WITHOUT ROWID;",
		)?;
		Ok(Self { connection, counts })
	}
}

fn storage(error: rusqlite::Error) -> RowError {
	RowError::Storage(error.to_string())
}

impl RowStore for SqlRowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		let mut pending = Buffered::new(
			|key: &[u8]| {
				let _call = self.counts.call("row_load");
				self.counts.reads.set(self.counts.reads.get() + 1);
				self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
				let value: Option<Vec<u8>> = self
					.connection
					.query_row("SELECT value FROM peer_rows WHERE key=?1", [key], |row| {
						row.get(0)
					})
					.optional()
					.map_err(storage)?;
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
		let reads = pending.reads;
		let writes = pending.writes;
		let _call = self.counts.call("row_commit");
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		let tx = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)
			.map_err(storage)?;
		self.counts.validation_bytes_sent.set(
			self.counts.validation_bytes_sent.get()
				+ reads
					.values()
					.filter_map(Option::as_ref)
					.map(|v| v.len() as u64)
					.sum::<u64>(),
		);
		for (key, expected) in &reads {
			self.counts
				.validation_rows
				.set(self.counts.validation_rows.get() + 1);
			self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
			let matches: bool = tx
				.query_row(
					"SELECT (SELECT value FROM peer_rows WHERE key=?1) IS ?2",
					rusqlite::params![key, expected],
					|row| row.get(0),
				)
				.map_err(storage)?;
			if !matches {
				return Err(RowError::Conflict);
			}
		}
		for (key, value) in &writes {
			self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
			tx.execute("INSERT INTO peer_rows(key,value) VALUES(?1,?2) ON CONFLICT(key) DO UPDATE SET value=excluded.value", [key, value]).map_err(storage)?;
		}
		self.counts.sql_calls.set(self.counts.sql_calls.get() + 1);
		tx.commit().map_err(storage)?;
		self.counts
			.writes
			.set(self.counts.writes.get() + writes.len() as u64);
		self.counts.value_bytes_written.set(
			self.counts.value_bytes_written.get()
				+ writes.values().map(|v| v.len() as u64).sum::<u64>(),
		);
		Ok(())
	}
}

/// Checkpoint before each measured batch, not on the timed path. Automatic checkpoints during
/// the batch remain enabled and their costs stay in the timing.
pub fn checkpoint(path: &Path) -> rusqlite::Result<()> {
	let connection = open(path)?;
	let (busy, _, _): (i64, i64, i64) =
		connection.query_row("PRAGMA wal_checkpoint(TRUNCATE)", [], |row| {
			Ok((row.get(0)?, row.get(1)?, row.get(2)?))
		})?;
	assert_eq!(
		busy, 0,
		"no concurrent transaction may prevent the benchmark checkpoint"
	);
	Ok(())
}

pub fn footprint(path: &Path, row_store: bool) -> rusqlite::Result<serde_json::Value> {
	let connection = Connection::open(path)?;
	let table = if row_store { "peer_rows" } else { "snapshot" };
	let (rows, value_bytes): (i64, i64) = connection.query_row(
		&format!("SELECT count(*),coalesce(sum(length(value)),0) FROM {table}"),
		[],
		|row| Ok((row.get(0)?, row.get(1)?)),
	)?;
	let rows =
		u64::try_from(rows).map_err(|_| rusqlite::Error::IntegralValueOutOfRange(0, rows))?;
	let value_bytes = u64::try_from(value_bytes)
		.map_err(|_| rusqlite::Error::IntegralValueOutOfRange(1, value_bytes))?;
	let file_bytes = |path: &Path| std::fs::metadata(path).map(|m| m.len()).unwrap_or(0);
	let mut wal_path = path.as_os_str().to_os_string();
	wal_path.push("-wal");
	Ok(serde_json::json!({
		"rows": rows, "stored_value_bytes": value_bytes,
		"main_file_bytes": file_bytes(path), "wal_file_bytes": file_bytes(Path::new(&wal_path)),
	}))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn sqlite_connection_uses_the_declared_durability_cache_and_wait_settings() {
		let directory = tempfile::tempdir().unwrap();
		let connection = open(&directory.path().join("settings.sqlite")).unwrap();
		let journal: String = connection
			.pragma_query_value(None, "journal_mode", |row| row.get(0))
			.unwrap();
		assert_eq!(journal, "wal");
		for (pragma, expected) in [
			("synchronous", 2_i64),
			("page_size", 4096),
			// A negative value declares KiB; positive 20000 would mean 20000 pages.
			("cache_size", -20_000),
			("wal_autocheckpoint", 1000),
			("busy_timeout", 5000),
		] {
			let actual: i64 = connection
				.pragma_query_value(None, pragma, |row| row.get(0))
				.unwrap();
			assert_eq!(actual, expected, "actual setting for {pragma}");
		}
	}
}
