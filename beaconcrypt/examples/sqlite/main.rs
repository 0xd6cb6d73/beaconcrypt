// SPDX-License-Identifier: 0BSD

use std::{error::Error, path::PathBuf};

use beaconcrypt::{Beacon, ProviderBeacon, RowError, RowServer, SnapshotLineage};

mod store;
use store::SqliteRowStore;

fn main() -> Result<(), Box<dyn Error>> {
	let path = std::env::args_os()
		.nth(1)
		.map(PathBuf::from)
		.ok_or("usage: cargo run -p beaconcrypt --example sqlite -- DATABASE")?;
	// This example assigns one lineage to this authoritative database. Real applications should
	// provision unique lineages and never activate copies of one lineage in independent stores.
	let lineage = SnapshotLineage::from_bytes([1; 32]);
	let mut server = match RowServer::open(SqliteRowStore::open(&path)?, lineage) {
		Ok(server) => server,
		Err(RowError::MissingIdentity) => {
			RowServer::create(0, None, None, SqliteRowStore::open(&path)?, lineage)?
		}
		Err(error) => return Err(error.into()),
	};
	let mut beacon = Beacon::try_new(
		server.identity_key_kid(),
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)?;
	let registration = beacon
		.get_registration_bundle()
		.ok_or("could not create registration")?;
	let response = server
		.register_beacon(&registration, Some(b"registered"))?
		.ok_or("registration rejected")?;
	beacon
		.finish_registration(&response.serialized)
		.ok_or("registration response rejected")?;

	let request = beacon
		.encrypt_message(b"hello from beacon")
		.ok_or("could not encrypt request")?;
	let received = server
		.decrypt_message(&request.ciphertext)?
		.ok_or("request rejected")?;
	println!("Received: {}", String::from_utf8_lossy(&received.plaintext));

	// A new process can open this identity without loading other peers or rewriting state.
	drop(server);
	let mut server = RowServer::open(SqliteRowStore::open(&path)?, lineage)?;
	let response = server
		.encrypt_message(b"hello after database reopen", response.kid)?
		.ok_or("could not encrypt response")?;
	let received = beacon
		.decrypt_message(&response.ciphertext)
		.ok_or("response rejected")?;
	println!("Received: {}", String::from_utf8_lossy(&received.plaintext));
	Ok(())
}
