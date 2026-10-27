// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "std", feature = "server", feature = "beacon"))]

use beaconcrypt::crypto::{CryptoError, OsRng, TryCryptoRng, TryRng};
use beaconcrypt::{Beacon, CachedRowServer, ProviderBeacon, RowError, RowServer, SnapshotLineage};
use proptest::{prelude::*, test_runner::FileFailurePersistence};
use std::{collections::BTreeMap, path::Path};

#[path = "../examples/sqlite/store.rs"]
mod store;
use store::SqliteRowStore;

const LINEAGE: SnapshotLineage = SnapshotLineage::from_bytes([0x87; 32]);

// Real entropy until the selected failure, including a partially written failure destination.
struct FailAfter(usize);
impl TryRng for FailAfter {
	type Error = CryptoError;
	fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
		let mut bytes = [0; 4];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u32::from_le_bytes(bytes))
	}
	fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
		let mut bytes = [0; 8];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u64::from_le_bytes(bytes))
	}
	fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Self::Error> {
		if self.0 == 0 {
			bytes.fill(0xa5);
			return Err(CryptoError);
		}
		self.0 -= 1;
		OsRng.try_fill_bytes(bytes).map_err(|_| CryptoError)
	}
}
impl TryCryptoRng for FailAfter {}

fn rows(path: &Path) -> BTreeMap<Vec<u8>, Vec<u8>> {
	let conn = rusqlite::Connection::open(path).unwrap();
	conn.prepare("SELECT key,value FROM beaconcrypt_rows ORDER BY key")
		.unwrap()
		.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
		.unwrap()
		.collect::<rusqlite::Result<_>>()
		.unwrap()
}

#[test]
fn failed_identity_entropy_never_creates_partial_rows() {
	for cached in [false, true] {
		for fail_after in 0..2 {
			let directory = tempfile::tempdir().unwrap();
			let path = directory.path().join("entropy.sqlite");
			let store = SqliteRowStore::open(&path).unwrap();
			let mut rng = FailAfter(fail_after);
			let error = if cached {
				CachedRowServer::create_with_rng(7, None, None, store, LINEAGE, 4, &mut rng).err()
			} else {
				RowServer::create_with_rng(7, None, None, store, LINEAGE, &mut rng).err()
			};
			assert_eq!(error, Some(RowError::Initialization));
			assert!(rows(&path).is_empty());
			let mut healthy = OsRng;
			let restored = RowServer::create_with_rng(
				7,
				None,
				None,
				SqliteRowStore::open(&path).unwrap(),
				LINEAGE,
				&mut healthy,
			)
			.unwrap();
			assert_eq!(restored.identity_key_kid(), 7);
			assert_eq!(rows(&path).len(), 2);
		}
	}
}

proptest! {
	#![proptest_config(ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok().and_then(|value| value.parse().ok()).unwrap_or(24),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"), "/proptest-regressions/row_rng.txt"
		)))),
		..ProptestConfig::default()
	})]
	#[test]
	fn registration_entropy_failure_is_retryable_without_a_marker(
		cached in any::<bool>(), fail_after in 0usize..2,
		payload in prop::collection::vec(any::<u8>(), 0..513),
	) {
		let directory = tempfile::tempdir().unwrap();
		let path = directory.path().join("registration.sqlite");
		let mut server = CachedRowServer::create_with_rng(
			7, None, None, SqliteRowStore::open(&path).unwrap(), LINEAGE,
			if cached { 4 } else { 0 }, &mut OsRng,
		).unwrap();
		let mut beacon = Beacon::try_new_with_rng(7, server.identity_pk().as_bytes(),
			&server.mldsa_public_key(), &mut OsRng).unwrap();
		let request = beacon.get_registration_bundle_with_rng(&mut OsRng).unwrap();
		let before = rows(&path);
		let rejected = server.register_beacon_with_rng(&request, Some(&payload), &mut FailAfter(fail_after)).unwrap();
		prop_assert!(rejected.is_none());
		prop_assert_eq!(&rows(&path), &before);
		let response = server.register_beacon_with_rng(&request, Some(&payload), &mut OsRng).unwrap();
		if payload.is_empty() {
			// Explicitly empty response data is rejected after acceptance. Its marker survives.
			prop_assert!(response.is_none());
			prop_assert_eq!(rows(&path).len(), before.len() + 1);
			prop_assert!(server.register_beacon_with_rng(&request, Some(b"retry"), &mut OsRng).unwrap().is_none());
			return Ok(());
		}
		let response = response.unwrap();
		prop_assert_eq!(beacon.finish_registration(&response.serialized).unwrap(), payload.clone());
		prop_assert!(server.register_beacon_with_rng(&request, None, &mut OsRng).unwrap().is_none());
		drop(server);
		let mut reopened = CachedRowServer::open(SqliteRowStore::open(&path).unwrap(), LINEAGE, 4).unwrap();
		let sent = beacon.encrypt_message(&payload).unwrap();
		prop_assert_eq!(reopened.decrypt_message(&sent.ciphertext).unwrap().unwrap().plaintext, payload.clone());
		let sent = reopened.encrypt_message(&payload, response.kid).unwrap().unwrap();
		prop_assert_eq!(beacon.decrypt_message(&sent.ciphertext).unwrap().plaintext, payload);
	}
}
