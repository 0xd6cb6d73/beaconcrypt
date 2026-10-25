// SPDX-License-Identifier: 0BSD

use std::{cell::Cell, path::Path, rc::Rc, time::Duration};

use beaconcrypt::{
	RowError, RowStore, RowTransaction, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};
use rusqlite::{Connection, OptionalExtension, Transaction, TransactionBehavior};
use serde::Serialize;

pub const SQL_SETTINGS: &str = "journal_mode=WAL;synchronous=FULL;page_size=4096;cache_size=-20000;wal_autocheckpoint=1000;busy_timeout_ms=5000";

#[derive(Default)]
pub struct Counters {
	pub reads: Cell<u64>,
	pub writes: Cell<u64>,
	pub transactions: Cell<u64>,
	pub value_bytes_read: Cell<u64>,
	pub value_bytes_written: Cell<u64>,
	pub head_bytes_read: Cell<u64>,
}

#[derive(Serialize)]
pub struct Counts {
	reads: u64,
	writes: u64,
	transactions: u64,
	value_bytes_read: u64,
	value_bytes_written: u64,
	head_bytes_read: u64,
}

impl Counters {
	pub fn take(&self) -> Counts {
		Counts {
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
		let tx = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)?;
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		self.counts.reads.set(self.counts.reads.get() + 1);
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
		tx.commit()?;
		Ok(true)
	}
}

impl SnapshotStore for SqlSnapshotStore {
	fn load(&self) -> Option<ServerSnapshot> {
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

struct Rows<'a, 'connection> {
	tx: &'a Transaction<'connection>,
	counts: &'a Counters,
}

impl RowTransaction for Rows<'_, '_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.counts.reads.set(self.counts.reads.get() + 1);
		let value: Option<Vec<u8>> = self
			.tx
			.query_row("SELECT value FROM peer_rows WHERE key=?1", [key], |row| {
				row.get(0)
			})
			.optional()
			.map_err(storage)?;
		if let Some(value) = &value {
			self.counts
				.value_bytes_read
				.set(self.counts.value_bytes_read.get() + value.len() as u64);
		}
		Ok(value)
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.tx
			.execute(
				"INSERT INTO peer_rows (key,value) VALUES (?1,?2)
			 ON CONFLICT(key) DO UPDATE SET value=excluded.value",
				[key, value],
			)
			.map_err(storage)?;
		self.counts.writes.set(self.counts.writes.get() + 1);
		self.counts
			.value_bytes_written
			.set(self.counts.value_bytes_written.get() + value.len() as u64);
		Ok(())
	}
}

impl RowStore for SqlRowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		let tx = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)
			.map_err(storage)?;
		self.counts
			.transactions
			.set(self.counts.transactions.get() + 1);
		operation(&mut Rows {
			tx: &tx,
			counts: &self.counts,
		})?;
		tx.commit().map_err(storage)
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
