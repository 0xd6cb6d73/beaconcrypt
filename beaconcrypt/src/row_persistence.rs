// SPDX-License-Identifier: 0BSD

//! Database-independent persistence of individual peers.

use std::{error::Error, fmt};

use libsodium_rs::{crypto_generichash, crypto_sign, ensure_init};
use zeroize::Zeroizing;

use crate::shared::EstablishedRemote;
use crate::{Decrypted, Encrypted, ProviderServer, RegResponse, Server, SnapshotLineage};

const MAGIC: &[u8; 16] = b"beaconcrypt-row\0";
const VERSION: u8 = 1;
const IDENTITY: u8 = 0;
const ALLOCATOR: u8 = 1;
const PEER: u8 = 2;
const REGISTRATION: u8 = 3;

/// Failure of row storage, validation, or durable publication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RowError {
	/// A database error, including an unknown commit outcome. No operation output is released.
	Storage(String),
	Conflict,
	MissingIdentity,
	InvalidRow,
	GenerationExhausted,
	Initialization,
	OutputEncoding,
}

impl fmt::Display for RowError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			Self::Storage(message) => write!(f, "row storage failed: {message}"),
			Self::Conflict => f.write_str("row already exists or transaction conflicted"),
			Self::MissingIdentity => f.write_str("server identity row is missing"),
			Self::InvalidRow => f.write_str("invalid or mismatched persistence row"),
			Self::GenerationExhausted => f.write_str("row generation exhausted"),
			Self::Initialization => f.write_str("failed to initialize server identity"),
			Self::OutputEncoding => f.write_str("failed to encode persistence row"),
		}
	}
}

impl Error for RowError {}

/// The row operations available inside one application-owned database transaction.
///
/// Keys and values are opaque beaconcrypt bytes. Values contain plaintext secrets. `load` must
/// distinguish absence from storage failure. Reads, including absence checks, and subsequent writes
/// must be isolated from conflicting transactions until the outer commit. Do not implement this
/// with independent autocommit reads and writes or a last-writer-wins cache.
pub trait RowTransaction {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError>;
	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError>;
}

/// Trusted, serializable, durable transactions over opaque rows.
///
/// Invoke `operation` exactly once. Commit all its writes atomically only if it returns `Ok`, and
/// report success only after the outer transaction is durably committed. A savepoint inside an
/// uncommitted application transaction is insufficient. On an error, roll back and return the
/// error. On a lost commit acknowledgement return an error even if the commit may have succeeded.
/// Do not retry the callback: it owns one-use cryptographic transitions.
///
/// Backends may use row locks or serializable transactions with conflict detection. Different peer
/// keys need not conflict. The backend must protect integrity, provenance, and freshness, including
/// absent registration markers. Revisions and unkeyed digests do not prevent database rollback.
/// One lineage must have exactly one authoritative database; never clone it into independent stores.
pub trait RowStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError>;
}

impl<S: RowStore + ?Sized> RowStore for Box<S> {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		(**self).transaction(operation)
	}
}

fn transact<T>(
	store: &mut impl RowStore,
	operation: impl FnOnce(&mut dyn RowTransaction) -> Result<T, RowError>,
) -> Result<T, RowError> {
	let mut operation = Some(operation);
	let mut result = None;
	let mut repeated = false;
	store.transaction(&mut |transaction| {
		let Some(operation) = operation.take() else {
			repeated = true;
			return Err(RowError::Storage(
				"transaction callback was repeated".into(),
			));
		};
		let outcome = operation(transaction);
		let status = outcome.as_ref().map(|_| ()).map_err(Clone::clone);
		result = Some(outcome);
		status
	})?;
	if repeated {
		return Err(RowError::Storage(
			"transaction callback was repeated".into(),
		));
	}
	result.ok_or_else(|| RowError::Storage("transaction callback was not invoked".into()))?
}

fn storage_key(lineage: SnapshotLineage, kind: u8, id: &[u8]) -> Vec<u8> {
	let mut key = b"beaconcrypt/rows/v1/".to_vec();
	key.extend_from_slice(lineage.as_bytes());
	key.push(kind);
	key.extend_from_slice(id);
	key
}

fn digest(bytes: &[u8]) -> Result<[u8; 32], RowError> {
	crypto_generichash::generichash(bytes, None, 32)
		.map_err(|_| RowError::Initialization)?
		.try_into()
		.map_err(|_| RowError::Initialization)
}

fn encode_row(
	key: &[u8],
	generation: u64,
	identity: &[u8; 32],
	payload: &[u8],
) -> Zeroizing<Vec<u8>> {
	let mut bytes = Zeroizing::new(Vec::new());
	bytes.extend_from_slice(MAGIC);
	bytes.push(VERSION);
	bytes.extend_from_slice(&generation.to_le_bytes());
	bytes.extend_from_slice(identity);
	// Every caller uses the fixed namespace, lineage, kind and at most 64 identifier bytes.
	bytes.extend_from_slice(&(key.len() as u16).to_le_bytes());
	bytes.extend_from_slice(key);
	bytes.extend_from_slice(payload);
	bytes
}

struct Row<'a> {
	generation: u64,
	identity: [u8; 32],
	payload: &'a [u8],
}

fn decode_row<'a>(key: &[u8], bytes: &'a [u8]) -> Result<Row<'a>, RowError> {
	const HEADER: usize = 16 + 1 + 8 + 32 + 2;
	if bytes.len() < HEADER || &bytes[..16] != MAGIC || bytes[16] != VERSION {
		return Err(RowError::InvalidRow);
	}
	let key_len = u16::from_le_bytes(bytes[57..59].try_into().unwrap()) as usize;
	if bytes.get(HEADER..HEADER + key_len) != Some(key) {
		return Err(RowError::InvalidRow);
	}
	Ok(Row {
		generation: u64::from_le_bytes(bytes[17..25].try_into().unwrap()),
		identity: bytes[25..57].try_into().unwrap(),
		payload: &bytes[HEADER + key_len..],
	})
}

fn bound_row<'a>(key: &[u8], bytes: &'a [u8], identity: &[u8; 32]) -> Result<Row<'a>, RowError> {
	let row = decode_row(key, bytes)?;
	if &row.identity != identity {
		return Err(RowError::InvalidRow);
	}
	Ok(row)
}

fn encode_peer(
	peer: &EstablishedRemote<crypto_sign::PublicKey>,
) -> Result<Zeroizing<Vec<u8>>, RowError> {
	serde_json::to_vec(peer)
		.map(Zeroizing::new)
		.map_err(|_| RowError::OutputEncoding)
}

fn decode_peer(payload: &[u8]) -> Result<EstablishedRemote<crypto_sign::PublicKey>, RowError> {
	let peer = serde_json::from_slice(payload).map_err(|_| RowError::InvalidRow)?;
	if encode_peer(&peer)?.as_slice() != payload {
		return Err(RowError::InvalidRow);
	}
	Ok(peer)
}

/// A database-independent server that loads and commits only the affected peer.
///
/// The handle retains immutable identity keys, never live peer ratchets or registration history.
/// Each operation obtains its mutable state inside a [`RowStore`] transaction, discards it on every
/// outcome, and releases output only after commit. Open one handle per database connection/worker;
/// workers for the same lineage must share an authoritative store. Opening does not write an
/// activation generation or load the peer table. The existing full-snapshot APIs remain separate.
pub struct RowServer<S: RowStore> {
	identity: Server,
	identity_digest: [u8; 32],
	lineage: SnapshotLineage,
	store: S,
}

impl<S: RowStore> RowServer<S> {
	/// Atomically create identity and allocator rows in an unused, application-provisioned lineage.
	pub fn create(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		mut store: S,
		lineage: SnapshotLineage,
	) -> Result<Self, RowError> {
		let identity = Server::try_new(server_kid, id_seed, mldsa_seed)
			.map_err(|_| RowError::Initialization)?;
		let payload = Zeroizing::new(
			identity
				.serialize_row_identity()
				.ok_or(RowError::OutputEncoding)?,
		);
		let identity_digest = digest(payload.as_bytes())?;
		let identity_key = storage_key(lineage, IDENTITY, &[]);
		let allocator_key = storage_key(lineage, ALLOCATOR, &[]);
		transact(&mut store, |transaction| {
			if transaction.load(&identity_key)?.is_some()
				|| transaction.load(&allocator_key)?.is_some()
			{
				return Err(RowError::Conflict);
			}
			transaction.store(
				&identity_key,
				&encode_row(&identity_key, 0, &identity_digest, payload.as_bytes()),
			)?;
			transaction.store(
				&allocator_key,
				&encode_row(
					&allocator_key,
					0,
					&identity_digest,
					&server_kid.to_le_bytes(),
				),
			)
		})?;
		Ok(Self {
			identity,
			identity_digest,
			lineage,
			store,
		})
	}

	/// Load only immutable identity state. No peer activation or whole-server rewrite is necessary.
	pub fn open(mut store: S, lineage: SnapshotLineage) -> Result<Self, RowError> {
		ensure_init().map_err(|_| RowError::Initialization)?;
		let key = storage_key(lineage, IDENTITY, &[]);
		let (identity, identity_digest) = transact(&mut store, |transaction| {
			let bytes = Zeroizing::new(transaction.load(&key)?.ok_or(RowError::MissingIdentity)?);
			let row = decode_row(&key, &bytes)?;
			let identity_digest = digest(row.payload)?;
			if row.generation != 0 || row.identity != identity_digest {
				return Err(RowError::InvalidRow);
			}
			let text = std::str::from_utf8(row.payload).map_err(|_| RowError::InvalidRow)?;
			let identity = Server::deserialize_state(text).ok_or(RowError::InvalidRow)?;
			let canonical = Zeroizing::new(
				identity
					.serialize_row_identity()
					.ok_or(RowError::OutputEncoding)?,
			);
			if canonical.as_bytes() != row.payload {
				return Err(RowError::InvalidRow);
			}
			Ok((identity, identity_digest))
		})?;
		Ok(Self {
			identity,
			identity_digest,
			lineage,
			store,
		})
	}

	pub const fn lineage(&self) -> SnapshotLineage {
		self.lineage
	}
	pub fn identity_key_kid(&self) -> u64 {
		self.identity.identity_key_kid()
	}
	pub fn identity_pk(&self) -> &crypto_sign::PublicKey {
		self.identity.identity_pk()
	}
	pub fn mldsa_public_key(&self) -> [u8; crate::MLDSA_PUBLIC_KEY_LEN] {
		self.identity.mldsa_public_key()
	}

	/// Accept an InitKex, durably consume its replay marker, then commit its response and peer.
	///
	/// These are two transactions: the consumed marker survives response failure and crashes. Pending
	/// registration material is never exported or persisted. A retry must use a fresh registration.
	pub fn register_beacon(
		&mut self,
		bytes: &[u8],
		data: Option<&[u8]>,
	) -> Result<Option<RegResponse>, RowError> {
		if bytes.len() > crate::MAX_MESSAGE_SIZE {
			return Ok(None);
		}
		let mut session = self.identity.row_session(self.identity_key_kid());
		let Some(pending) = session.get_shared_secret(bytes) else {
			return Ok(None);
		};
		let replay_key = storage_key(self.lineage, REGISTRATION, &pending.row_registration_id());
		let accepted = transact(&mut self.store, |transaction| {
			if let Some(bytes) = transaction.load(&replay_key)? {
				let bytes = Zeroizing::new(bytes);
				let row = bound_row(&replay_key, &bytes, &self.identity_digest)?;
				if row.generation != 0 || !row.payload.is_empty() {
					return Err(RowError::InvalidRow);
				}
				return Ok(false);
			}
			transaction.store(
				&replay_key,
				&encode_row(&replay_key, 0, &self.identity_digest, &[]),
			)?;
			Ok(true)
		})?;
		if !accepted {
			return Ok(None);
		}
		let allocator_key = storage_key(self.lineage, ALLOCATOR, &[]);
		transact(&mut self.store, |transaction| {
			let bytes = Zeroizing::new(
				transaction
					.load(&allocator_key)?
					.ok_or(RowError::InvalidRow)?,
			);
			let row = bound_row(&allocator_key, &bytes, &self.identity_digest)?;
			let last =
				u64::from_le_bytes(row.payload.try_into().map_err(|_| RowError::InvalidRow)?);
			if last < self.identity.identity_key_kid() {
				return Err(RowError::InvalidRow);
			}
			let Some(kid) = last.checked_add(1) else {
				return Ok(None);
			};
			let peer_key = storage_key(self.lineage, PEER, &kid.to_le_bytes());
			if transaction.load(&peer_key)?.is_some() {
				return Err(RowError::Conflict);
			}
			let mut session = self.identity.row_session(last);
			let Some(response) = session.build_registration_response(pending, data) else {
				return Ok(None);
			};
			let peer = session.take_row_peer(kid).ok_or(RowError::InvalidRow)?;
			let generation = row
				.generation
				.checked_add(1)
				.ok_or(RowError::GenerationExhausted)?;
			transaction.store(
				&allocator_key,
				&encode_row(
					&allocator_key,
					generation,
					&self.identity_digest,
					&kid.to_le_bytes(),
				),
			)?;
			transaction.store(
				&peer_key,
				&encode_row(&peer_key, 0, &self.identity_digest, &encode_peer(&peer)?),
			)?;
			Ok(Some(response))
		})
	}

	/// Encrypt and durably commit only this peer. A consumed send key is saved even on seal failure.
	pub fn encrypt_message(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<Encrypted>, RowError> {
		if bytes.is_empty() || bytes.len() > crate::MAX_MESSAGE_SIZE {
			return Ok(None);
		}
		self.with_peer(kid, |session| {
			let before = session
				.ratchet_status(kid)
				.ok_or(RowError::InvalidRow)?
				.send_sequence();
			let encrypted = session.encrypt_message(bytes, kid);
			let after = session
				.ratchet_status(kid)
				.ok_or(RowError::InvalidRow)?
				.send_sequence();
			Ok((encrypted, before != after))
		})
	}

	/// Authenticate once and commit the resulting peer before releasing plaintext. Rejection writes nothing.
	pub fn decrypt_message(&mut self, bytes: &[u8]) -> Result<Option<Decrypted>, RowError> {
		let Some(kid) = crate::ratchet::encrypted_frame_sender(bytes) else {
			return Ok(None);
		};
		// Keep tentative plaintext in a wiping buffer until the outer transaction has committed.
		let pending = self.with_peer(kid, |session| {
			let decrypted = session
				.decrypt_message(bytes)
				.map(|value| (Zeroizing::new(value.plaintext), value.key_id, value.seq));
			let changed = decrypted.is_some();
			Ok((decrypted, changed))
		})?;
		Ok(pending.map(|(mut plaintext, key_id, seq)| Decrypted {
			plaintext: std::mem::take(&mut *plaintext),
			key_id,
			seq,
		}))
	}

	fn with_peer<T>(
		&mut self,
		kid: u64,
		operation: impl FnOnce(&mut Server) -> Result<(Option<T>, bool), RowError>,
	) -> Result<Option<T>, RowError> {
		let key = storage_key(self.lineage, PEER, &kid.to_le_bytes());
		transact(&mut self.store, |transaction| {
			let Some(bytes) = transaction.load(&key)? else {
				return Ok(None);
			};
			let bytes = Zeroizing::new(bytes);
			let row = bound_row(&key, &bytes, &self.identity_digest)?;
			let peer = decode_peer(row.payload)?;
			let mut session = self.identity.row_session(self.identity.identity_key_kid());
			session.put_row_peer(kid, peer);
			let (output, changed) = operation(&mut session)?;
			if changed {
				let peer = session.take_row_peer(kid).ok_or(RowError::InvalidRow)?;
				let generation = row
					.generation
					.checked_add(1)
					.ok_or(RowError::GenerationExhausted)?;
				transaction.store(
					&key,
					&encode_row(
						&key,
						generation,
						&self.identity_digest,
						&encode_peer(&peer)?,
					),
				)?;
			}
			Ok(output)
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{
		collections::BTreeMap,
		sync::{
			Arc,
			atomic::{AtomicUsize, Ordering},
		},
	};

	const LINEAGE: SnapshotLineage = SnapshotLineage::from_bytes([0x61; 32]);
	const SERVER_KID: u64 = 7;
	const PEER_KID: u64 = 8;

	#[derive(Clone, Default)]
	struct TestStore {
		rows: BTreeMap<Vec<u8>, Vec<u8>>,
		transactions: usize,
		fail_load: bool,
		fail_store: bool,
		fail_commit: bool,
	}

	struct TestTransaction<'a> {
		rows: &'a mut BTreeMap<Vec<u8>, Vec<u8>>,
		fail_load: bool,
		fail_store: bool,
	}

	impl RowTransaction for TestTransaction<'_> {
		fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
			if self.fail_load {
				return Err(RowError::Storage("load failed".into()));
			}
			Ok(self.rows.get(key).cloned())
		}

		fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
			if self.fail_store {
				return Err(RowError::Storage("write failed".into()));
			}
			self.rows.insert(key.to_vec(), value.to_vec());
			Ok(())
		}
	}

	impl RowStore for TestStore {
		fn transaction(
			&mut self,
			operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
		) -> Result<(), RowError> {
			self.transactions += 1;
			let mut rows = self.rows.clone();
			operation(&mut TestTransaction {
				rows: &mut rows,
				fail_load: self.fail_load,
				fail_store: self.fail_store,
			})?;
			if self.fail_commit {
				return Err(RowError::Storage("commit failed".into()));
			}
			self.rows = rows;
			Ok(())
		}
	}

	fn server() -> RowServer<TestStore> {
		RowServer::create(
			SERVER_KID,
			Some(&[0x62; 32]),
			Some(&[0x63; 32]),
			TestStore::default(),
			LINEAGE,
		)
		.unwrap()
	}

	fn install_peer(server: &mut RowServer<TestStore>, generation: u64) -> Vec<u8> {
		let mut session = server.identity.row_session(SERVER_KID);
		let public_key = crypto_sign::KeyPair::from_seed(&[0x64; 32])
			.unwrap()
			.public_key;
		session.add_known_kid(PEER_KID, public_key);
		let peer = session.take_row_peer(PEER_KID).unwrap();
		let key = storage_key(LINEAGE, PEER, &PEER_KID.to_le_bytes());
		server.store.rows.insert(
			key.clone(),
			encode_row(
				&key,
				generation,
				&server.identity_digest,
				&encode_peer(&peer).unwrap(),
			)
			.to_vec(),
		);
		key
	}

	#[test]
	fn row_envelope_binds_namespace_kind_identifier_and_identity() {
		ensure_init().unwrap();
		let key = storage_key(LINEAGE, PEER, &PEER_KID.to_le_bytes());
		let identity = digest(b"server identity").unwrap();
		assert_ne!(identity, digest(b"another identity").unwrap());
		let bytes = encode_row(&key, 41, &identity, b"payload");
		let row = bound_row(&key, &bytes, &identity).unwrap();
		assert_eq!(row.generation, 41);
		assert_eq!(row.identity, identity);
		assert_eq!(row.payload, b"payload");
		for other in [
			storage_key(
				SnapshotLineage::from_bytes([0x65; 32]),
				PEER,
				&PEER_KID.to_le_bytes(),
			),
			storage_key(LINEAGE, ALLOCATOR, &PEER_KID.to_le_bytes()),
			storage_key(LINEAGE, PEER, &9u64.to_le_bytes()),
		] {
			assert_ne!(other, key);
			assert_eq!(decode_row(&other, &bytes).err(), Some(RowError::InvalidRow));
		}
		assert_eq!(
			bound_row(&key, &bytes, &[0; 32]).err(),
			Some(RowError::InvalidRow)
		);
		for length in 0..59 + key.len() {
			assert_eq!(
				decode_row(&key, &bytes[..length]).err(),
				Some(RowError::InvalidRow),
				"length {length}"
			);
		}
		for offset in [0, 15, 16, 57, 58, 59] {
			let mut corrupted = bytes.to_vec();
			corrupted[offset] ^= 1;
			assert_eq!(
				decode_row(&key, &corrupted).err(),
				Some(RowError::InvalidRow),
				"offset {offset}"
			);
		}
		let maximum = encode_row(&key, u64::MAX, &identity, &[]);
		assert_eq!(decode_row(&key, &maximum).unwrap().generation, u64::MAX);
	}

	#[test]
	fn peer_codec_rejects_noncanonical_and_malformed_payloads() {
		let mut server = server();
		let key = install_peer(&mut server, 0);
		let bytes = &server.store.rows[&key];
		let row = decode_row(&key, bytes).unwrap();
		let peer = decode_peer(row.payload).unwrap();
		assert_eq!(encode_peer(&peer).unwrap().as_slice(), row.payload);
		let mut whitespace = row.payload.to_vec();
		whitespace.push(b'\n');
		assert_eq!(decode_peer(&whitespace).err(), Some(RowError::InvalidRow));
		assert_eq!(decode_peer(b"not JSON").err(), Some(RowError::InvalidRow));
		let value: serde_json::Value = serde_json::from_slice(row.payload).unwrap();
		let mut missing = value.clone();
		missing
			.as_object_mut()
			.unwrap()
			.remove("mldsa_public_key_hash");
		let mut short = value.clone();
		short["mldsa_public_key_hash"] = serde_json::json!([1, 2]);
		let mut extra = value;
		extra["unexpected"] = serde_json::json!(0);
		for malformed in [missing, short, extra] {
			assert_eq!(
				decode_peer(&serde_json::to_vec(&malformed).unwrap()).err(),
				Some(RowError::InvalidRow)
			);
		}
	}

	#[test]
	fn identity_open_rejects_changed_generation_binding_and_payload() {
		let server = server();
		let key = storage_key(LINEAGE, IDENTITY, &[]);
		let bytes = &server.store.rows[&key];
		let row = decode_row(&key, bytes).unwrap();
		let payload = row.payload.to_vec();
		let mut whitespace = payload.clone();
		whitespace.push(b' ');
		let mut invalid_seed: serde_json::Value = serde_json::from_slice(&payload).unwrap();
		invalid_seed["mldsa_identity_seed"] = serde_json::json!([1]);
		let invalid_seed = serde_json::to_vec(&invalid_seed).unwrap();
		let mut wrong_counter: serde_json::Value = serde_json::from_slice(&payload).unwrap();
		wrong_counter["server_kid"] = serde_json::json!(SERVER_KID + 1);
		let wrong_counter = serde_json::to_vec(&wrong_counter).unwrap();
		for replacement in [
			encode_row(&key, 1, &row.identity, &payload),
			encode_row(&key, 0, &[0; 32], &payload),
			encode_row(&key, 0, &digest(&whitespace).unwrap(), &whitespace),
			encode_row(&key, 0, &digest(&invalid_seed).unwrap(), &invalid_seed),
			encode_row(&key, 0, &digest(&wrong_counter).unwrap(), &wrong_counter),
			encode_row(&key, 0, &digest(&[0xff]).unwrap(), &[0xff]),
		] {
			let mut store = server.store.clone();
			store.rows.insert(key.clone(), replacement.to_vec());
			assert_eq!(
				RowServer::open(store, LINEAGE).err(),
				Some(RowError::InvalidRow)
			);
		}
		assert_eq!(
			RowServer::open(TestStore::default(), LINEAGE).err(),
			Some(RowError::MissingIdentity)
		);
		let opened = RowServer::open(server.store.clone(), LINEAGE).unwrap();
		assert_eq!(opened.lineage(), LINEAGE);
		assert_eq!(opened.identity_key_kid(), SERVER_KID);
		assert_eq!(opened.identity_pk(), server.identity_pk());
		assert_eq!(opened.mldsa_public_key(), server.mldsa_public_key());
		assert_eq!(opened.store.rows, server.store.rows);
	}

	#[test]
	fn creation_checks_both_metadata_rows_and_propagates_database_failures() {
		let server = server();
		let create = |store| {
			RowServer::create(
				SERVER_KID,
				Some(&[0x62; 32]),
				Some(&[0x63; 32]),
				store,
				LINEAGE,
			)
			.err()
		};
		assert_eq!(create(server.store.clone()), Some(RowError::Conflict));
		let mut orphan_allocator = server.store.clone();
		orphan_allocator
			.rows
			.remove(&storage_key(LINEAGE, IDENTITY, &[]));
		assert_eq!(create(orphan_allocator), Some(RowError::Conflict));
		for store in [
			TestStore {
				fail_load: true,
				..TestStore::default()
			},
			TestStore {
				fail_store: true,
				..TestStore::default()
			},
			TestStore {
				fail_commit: true,
				..TestStore::default()
			},
		] {
			assert!(matches!(create(store), Some(RowError::Storage(_))));
		}
		assert_eq!(
			RowServer::create(SERVER_KID, Some(&[]), None, TestStore::default(), LINEAGE).err(),
			Some(RowError::Initialization)
		);
	}

	#[test]
	fn peer_generation_overflow_and_storage_errors_never_publish_or_retain_tentative_state() {
		let mut server = server();
		let key = install_peer(&mut server, u64::MAX);
		let before = server.store.rows.clone();
		assert_eq!(
			server.encrypt_message(b"exhausted", PEER_KID).err(),
			Some(RowError::GenerationExhausted)
		);
		assert_eq!(server.store.rows, before);
		assert!(server.decrypt_message(b"malformed").unwrap().is_none());
		assert!(server.encrypt_message(&[], PEER_KID).unwrap().is_none());
		assert!(server.encrypt_message(b"unknown", 100).unwrap().is_none());
		assert_eq!(server.store.rows, before);

		install_peer(&mut server, 0);
		let before = server.store.rows.clone();
		server.store.fail_load = true;
		assert!(matches!(
			server.encrypt_message(b"load", PEER_KID),
			Err(RowError::Storage(_))
		));
		server.store.fail_load = false;
		server.store.fail_store = true;
		assert!(matches!(
			server.encrypt_message(b"write", PEER_KID),
			Err(RowError::Storage(_))
		));
		server.store.fail_store = false;
		server.store.fail_commit = true;
		assert!(matches!(
			server.encrypt_message(b"commit", PEER_KID),
			Err(RowError::Storage(_))
		));
		server.store.fail_commit = false;
		assert_eq!(server.store.rows, before);
		let encrypted = server.encrypt_message(b"fresh", PEER_KID).unwrap().unwrap();
		assert_eq!(encrypted.seq, 1);
		let row = decode_row(&key, &server.store.rows[&key]).unwrap();
		assert_eq!(row.generation, 1);
		assert_eq!(
			decode_peer(row.payload)
				.unwrap()
				.ratchet()
				.status()
				.send_sequence(),
			1
		);
	}

	#[test]
	fn loaded_peer_binding_and_codec_errors_are_not_reported_as_protocol_rejection() {
		let mut server = server();
		let key = install_peer(&mut server, 0);
		let original = server.store.rows[&key].clone();
		let row = decode_row(&key, &original).unwrap();
		for bytes in [
			encode_row(&key, 0, &[0; 32], row.payload),
			encode_row(&key, 0, &server.identity_digest, b"bad peer"),
			encode_row(b"wrong key", 0, &server.identity_digest, row.payload),
		] {
			server.store.rows.insert(key.clone(), bytes.to_vec());
			assert_eq!(
				server.encrypt_message(b"invalid", PEER_KID).err(),
				Some(RowError::InvalidRow)
			);
			assert_eq!(&server.store.rows[&key], bytes.as_slice());
		}
	}

	#[test]
	fn transaction_gate_handles_skipped_repeated_and_swallowed_callback_failures() {
		enum Behaviour {
			Skip,
			Repeat,
			Swallow,
		}
		impl RowStore for Behaviour {
			fn transaction(
				&mut self,
				operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
			) -> Result<(), RowError> {
				let mut rows = BTreeMap::new();
				let mut transaction = TestTransaction {
					rows: &mut rows,
					fail_load: false,
					fail_store: false,
				};
				match self {
					Self::Skip => (),
					Self::Repeat => {
						let _ = operation(&mut transaction);
						let _ = operation(&mut transaction);
					}
					Self::Swallow => {
						let _ = operation(&mut transaction);
					}
				}
				Ok(())
			}
		}
		assert!(matches!(
			transact(&mut Behaviour::Skip, |_| Ok(7)),
			Err(RowError::Storage(_))
		));
		let mut calls = 0;
		assert!(matches!(
			transact(&mut Behaviour::Repeat, |_| {
				calls += 1;
				Ok(7)
			}),
			Err(RowError::Storage(_))
		));
		assert_eq!(calls, 1);
		assert_eq!(
			transact::<()>(&mut Behaviour::Swallow, |_| Err(RowError::InvalidRow)),
			Err(RowError::InvalidRow)
		);
		let mut boxed: Box<dyn RowStore> = Box::new(TestStore::default());
		assert_eq!(transact(&mut boxed, |_| Ok(19)).unwrap(), 19);

		struct Pending(Arc<AtomicUsize>);
		impl Drop for Pending {
			fn drop(&mut self) {
				self.0.fetch_add(1, Ordering::SeqCst);
			}
		}
		let dropped = Arc::new(AtomicUsize::new(0));
		let mut store = TestStore {
			fail_commit: true,
			..TestStore::default()
		};
		assert!(matches!(
			transact(&mut store, |_| Ok(Pending(Arc::clone(&dropped)))),
			Err(RowError::Storage(_))
		));
		assert_eq!(dropped.load(Ordering::SeqCst), 1);
	}

	#[test]
	fn persistence_errors_have_distinct_stable_descriptions() {
		for (error, expected) in [
			(RowError::Storage("disk".into()), "row storage failed: disk"),
			(
				RowError::Conflict,
				"row already exists or transaction conflicted",
			),
			(RowError::MissingIdentity, "server identity row is missing"),
			(
				RowError::InvalidRow,
				"invalid or mismatched persistence row",
			),
			(RowError::GenerationExhausted, "row generation exhausted"),
			(
				RowError::Initialization,
				"failed to initialize server identity",
			),
			(RowError::OutputEncoding, "failed to encode persistence row"),
		] {
			assert_eq!(error.to_string(), expected);
			assert!(error.source().is_none());
		}
	}

	#[cfg(feature = "beacon")]
	fn registration(server: &RowServer<TestStore>) -> Vec<u8> {
		use crate::ProviderBeacon;
		let mut beacon = crate::Beacon::new(
			server.identity_key_kid(),
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		beacon.get_registration_bundle().unwrap()
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn allocator_failures_preserve_metadata_and_the_accepted_replay_marker() {
		let key = storage_key(LINEAGE, ALLOCATOR, &[]);
		for scenario in 0..7 {
			let mut server = server();
			let expected = match scenario {
				0 => {
					server.store.rows.remove(&key);
					Some(RowError::InvalidRow)
				}
				1 => {
					server.store.rows.insert(
						key.clone(),
						encode_row(
							&key,
							0,
							&server.identity_digest,
							&(SERVER_KID - 1).to_le_bytes(),
						)
						.to_vec(),
					);
					Some(RowError::InvalidRow)
				}
				2 => {
					server.store.rows.insert(
						key.clone(),
						encode_row(&key, 0, &server.identity_digest, &[0; 7]).to_vec(),
					);
					Some(RowError::InvalidRow)
				}
				3 => {
					server.store.rows.insert(
						key.clone(),
						encode_row(
							&key,
							u64::MAX,
							&server.identity_digest,
							&SERVER_KID.to_le_bytes(),
						)
						.to_vec(),
					);
					Some(RowError::GenerationExhausted)
				}
				4 => {
					server.store.rows.insert(
						key.clone(),
						encode_row(&key, 0, &server.identity_digest, &u64::MAX.to_le_bytes())
							.to_vec(),
					);
					None
				}
				5 => {
					server
						.store
						.rows
						.insert(storage_key(LINEAGE, PEER, &PEER_KID.to_le_bytes()), vec![0]);
					Some(RowError::Conflict)
				}
				_ => {
					server.store.rows.insert(
						key.clone(),
						encode_row(&key, 0, &[0; 32], &SERVER_KID.to_le_bytes()).to_vec(),
					);
					Some(RowError::InvalidRow)
				}
			};
			let request = registration(&server);
			let before = server.store.rows.clone();
			let result = server.register_beacon(&request, Some(b"accepted"));
			if let Some(error) = expected {
				assert_eq!(result.err(), Some(error), "scenario {scenario}");
			} else {
				assert!(result.unwrap().is_none());
			}
			assert_eq!(server.store.rows.len(), before.len() + 1);
			for (key, value) in before {
				assert_eq!(server.store.rows[&key], value, "scenario {scenario}");
			}
			let accepted = server.store.rows.clone();
			assert!(
				server
					.register_beacon(&request, Some(b"retry"))
					.unwrap()
					.is_none()
			);
			assert_eq!(server.store.rows, accepted);
		}
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn malformed_replay_markers_fail_closed_without_allocating_a_peer() {
		let mut server = server();
		let request = registration(&server);
		let mut session = server.identity.row_session(SERVER_KID);
		let pending = session.get_shared_secret(&request).unwrap();
		let key = storage_key(LINEAGE, REGISTRATION, &pending.row_registration_id());
		for replacement in [
			encode_row(&key, 1, &server.identity_digest, &[]),
			encode_row(&key, 0, &server.identity_digest, b"unexpected"),
			encode_row(&key, 0, &[0; 32], &[]),
		] {
			server.store.rows.insert(key.clone(), replacement.to_vec());
			let before = server.store.rows.clone();
			assert_eq!(
				server.register_beacon(&request, Some(b"blocked")).err(),
				Some(RowError::InvalidRow)
			);
			assert_eq!(server.store.rows, before);
		}
	}
}
