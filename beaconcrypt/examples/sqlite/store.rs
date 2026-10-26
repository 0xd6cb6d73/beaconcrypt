// SPDX-License-Identifier: 0BSD

//! Application-owned SQLite implementation of beaconcrypt's database-neutral storage contract.

use std::{path::Path, time::Duration};

use rusqlite::{Connection, OptionalExtension, Transaction, TransactionBehavior};

use beaconcrypt::{RowError, RowStore, RowTransaction};

/// A file-backed row store with durable, serializable transactions.
///
/// Separate server workers may open separate connections to the same database. SQLite serializes
/// their write transactions; only the rows used by the operation are decoded or replaced.
/// Applications requiring concurrent writers to different peers can implement [`RowStore`] using
/// a database with row locks. Protect this database, including its WAL and backups, as secret
/// state. SQLite durability does not itself prevent an administrator restoring an old backup.
pub struct SqliteRowStore {
	connection: Connection,
}

impl SqliteRowStore {
	/// Open a database and initialize the row table if necessary.
	///
	/// This connection uses WAL journaling, FULL synchronous commits, and a five-second busy
	/// timeout. The store owns its transactions; successful operations have committed the outer
	/// transaction before returning. Use a persistent file path for crash recovery.
	pub fn open(path: impl AsRef<Path>) -> Result<Self, RowError> {
		let connection = Connection::open(path).map_err(storage_error)?;
		connection
			.busy_timeout(Duration::from_secs(5))
			.map_err(storage_error)?;
		connection
			.pragma_update(None, "journal_mode", "WAL")
			.map_err(storage_error)?;
		connection
			.pragma_update(None, "synchronous", "FULL")
			.map_err(storage_error)?;
		connection
			.execute_batch(
				"CREATE TABLE IF NOT EXISTS beaconcrypt_rows (
					key BLOB PRIMARY KEY NOT NULL,
					value BLOB NOT NULL
				) WITHOUT ROWID;",
			)
			.map_err(storage_error)?;
		Ok(Self { connection })
	}
}

fn storage_error(error: rusqlite::Error) -> RowError {
	RowError::Storage(error.to_string())
}

struct SqliteTransaction<'a, 'connection>(&'a Transaction<'connection>);

impl RowTransaction for SqliteTransaction<'_, '_> {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.0
			.query_row(
				"SELECT value FROM beaconcrypt_rows WHERE key = ?1",
				[key],
				|row| row.get(0),
			)
			.optional()
			.map_err(storage_error)
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.0
			.execute(
				"INSERT INTO beaconcrypt_rows (key, value) VALUES (?1, ?2)
				 ON CONFLICT(key) DO UPDATE SET value = excluded.value",
				[key, value],
			)
			.map_err(storage_error)?;
		Ok(())
	}
}

impl RowStore for SqliteRowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		// Acquiring the write lock before any reads also protects absent-row checks. Deferred
		// transactions would allow two workers to observe the same predecessor before upgrading.
		let transaction = self
			.connection
			.transaction_with_behavior(TransactionBehavior::Immediate)
			.map_err(storage_error)?;
		operation(&mut SqliteTransaction(&transaction))?;
		transaction.commit().map_err(storage_error)
	}
}
