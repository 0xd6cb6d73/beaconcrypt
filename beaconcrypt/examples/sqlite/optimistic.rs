// SPDX-License-Identifier: 0BSD

//! Example application-owned optimistic adapter, including cached row expectations.
//!
//! The callback runs once against buffered reads and writes. The final SQLite transaction
//! validates every observed value (including absence) before publishing any writes. `expect`
//! can therefore record a cached predecessor without issuing a separate SELECT. All writers
//! still commit through the authoritative database; this is not a write-behind cache.

use std::{collections::BTreeMap, path::Path, time::Duration};

use beaconcrypt::{RowError, RowStore, RowTransaction};
use rusqlite::{Connection, OptionalExtension, TransactionBehavior};
use zeroize::Zeroizing;

pub struct OptimisticSqliteRowStore {
	connection: Connection,
}

type Secret = Zeroizing<Vec<u8>>;

fn storage(error: rusqlite::Error) -> RowError {
	RowError::Storage(error.to_string())
}

fn read(connection: &Connection, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
	connection
		.query_row(
			"SELECT value FROM beaconcrypt_rows WHERE key=?1",
			[key],
			|row| row.get(0),
		)
		.optional()
		.map_err(storage)
}

impl OptimisticSqliteRowStore {
	pub fn open(path: &Path) -> Result<Self, RowError> {
		let connection = Connection::open(path).map_err(storage)?;
		connection
			.busy_timeout(Duration::from_secs(5))
			.map_err(storage)?;
		connection
			.pragma_update(None, "journal_mode", "WAL")
			.map_err(storage)?;
		connection
			.pragma_update(None, "synchronous", "FULL")
			.map_err(storage)?;
		connection
			.execute_batch(
				"CREATE TABLE IF NOT EXISTS beaconcrypt_rows (
				key BLOB PRIMARY KEY NOT NULL,
				value BLOB NOT NULL
			) WITHOUT ROWID;",
			)
			.map_err(storage)?;
		Ok(Self { connection })
	}
}

struct Buffered<'a> {
	connection: &'a Connection,
	reads: BTreeMap<Vec<u8>, Option<Secret>>,
	writes: BTreeMap<Vec<u8>, Secret>,
	failure: Option<RowError>,
}

impl Buffered<'_> {
	fn ready(&self) -> Result<(), RowError> {
		self.failure.clone().map_or(Ok(()), Err)
	}
}

impl RowTransaction for Buffered<'_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.ready()?;
		if let Some(value) = self.writes.get(key) {
			return Ok(Some(value.to_vec()));
		}
		if let Some(value) = self.reads.get(key) {
			return Ok(value.as_ref().map(|value| value.to_vec()));
		}
		let value =
			read(self.connection, key).inspect_err(|error| self.failure = Some(error.clone()))?;
		self.reads
			.insert(key.to_vec(), value.clone().map(Zeroizing::new));
		Ok(value)
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.ready()?;
		self.writes
			.insert(key.to_vec(), Zeroizing::new(value.to_vec()));
		Ok(())
	}

	fn expect(&mut self, key: &[u8], expected: Option<&[u8]>) -> Result<(), RowError> {
		self.ready()?;
		let known = if let Some(value) = self.writes.get(key) {
			Some(Some(value.as_slice()))
		} else {
			self.reads
				.get(key)
				.map(|value| value.as_ref().map(|value| value.as_slice()))
		};
		if let Some(value) = known {
			return if value == expected {
				Ok(())
			} else {
				self.failure = Some(RowError::Conflict);
				Err(RowError::Conflict)
			};
		}
		self.reads.insert(
			key.to_vec(),
			expected.map(|value| Zeroizing::new(value.to_vec())),
		);
		Ok(())
	}
}

impl RowStore for OptimisticSqliteRowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		let mut buffered = Buffered {
			connection: &self.connection,
			reads: BTreeMap::new(),
			writes: BTreeMap::new(),
			failure: None,
		};
		operation(&mut buffered)?;
		buffered.ready()?;
		let Buffered { reads, writes, .. } = buffered;
		let tx = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)
			.map_err(storage)?;
		for (key, expected) in reads {
			let actual = read(&tx, &key)?.map(Zeroizing::new);
			if actual.as_ref().map(|value| value.as_slice())
				!= expected.as_ref().map(|value| value.as_slice())
			{
				return Err(RowError::Conflict);
			}
		}
		for (key, value) in writes {
			tx.execute(
				"INSERT INTO beaconcrypt_rows (key,value) VALUES (?1,?2)
				ON CONFLICT(key) DO UPDATE SET value=excluded.value",
				rusqlite::params![key, value.as_slice()],
			)
			.map_err(storage)?;
		}
		tx.commit().map_err(storage)
	}
}
