// SPDX-License-Identifier: 0BSD

//! Database-independent persistence of individual peers.

use std::{collections::BTreeMap, error::Error, fmt};

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
	/// The callback attempted an operation outside its phase or used its native transition twice.
	InvalidSession,
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
			Self::InvalidSession => f.write_str("invalid operation in row transaction session"),
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

	/// Require this exact value, or absence, in the transaction's read set.
	///
	/// `Some(&[])` is a present empty value, distinct from `None`. The default loads and compares
	/// under the ordinary transaction isolation contract. An optimistic backend may instead stage
	/// the expectation without reading; it must validate all expectations atomically with the outer
	/// commit, including transactions that make no writes, and return `Conflict` on a mismatch.
	/// Deferred success is tentative: callers must not publish output before the outer commit.
	fn expect(&mut self, key: &[u8], expected: Option<&[u8]>) -> Result<(), RowError> {
		let actual = self.load(key)?.map(Zeroizing::new);
		if actual.as_deref().map(Vec::as_slice) == expected {
			Ok(())
		} else {
			Err(RowError::Conflict)
		}
	}
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
	let header = bytes.get(..HEADER).ok_or(RowError::InvalidRow)?;
	if &header[..16] != MAGIC || header[16] != VERSION {
		return Err(RowError::InvalidRow);
	}
	let key_len = u16::from_le_bytes(header[57..59].try_into().unwrap()) as usize;
	if bytes.get(HEADER..HEADER + key_len) != Some(key) {
		return Err(RowError::InvalidRow);
	}
	Ok(Row {
		generation: u64::from_le_bytes(header[17..25].try_into().unwrap()),
		identity: header[25..57].try_into().unwrap(),
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

/// Message material available to a trusted transaction callback before commit.
///
/// The owned buffer is wiped on drop, including when commit fails. Copies made by the application
/// remain its responsibility. Do not publish this message outside the transaction before commit.
pub struct RowMessage {
	data: Zeroizing<Vec<u8>>,
	key_id: u64,
	sequence: u64,
}

impl RowMessage {
	pub fn data(&self) -> &[u8] {
		&self.data
	}
	pub const fn key_id(&self) -> u64 {
		self.key_id
	}
	pub const fn sequence(&self) -> u64 {
		self.sequence
	}
}

/// The effect of one native operation in the current transaction.
///
/// A rejected operation has no message and `changed == false`. A send that consumed a key but
/// failed to produce a message has `changed == true`; an application can record that terminal
/// outcome without accidentally treating it as an unchanged rejection.
pub struct RowTransition {
	pub message: Option<RowMessage>,
	pub changed: bool,
}

impl RowTransition {
	fn unchanged() -> Self {
		Self {
			message: None,
			changed: false,
		}
	}
}

/// Choose an application result after registration preflight, or continue after durable acceptance.
pub enum RowRegistrationDecision<A, T> {
	/// Commit the current application writes and return without constructing a registration response.
	Return(T),
	/// Commit an accepted registration and carry application context into the completion callback.
	Continue(A),
}

/// The transaction that reported a registration failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RowRegistrationPhase {
	/// Acceptance was not confirmed. A storage error may still mean the first commit succeeded.
	Acceptance,
	/// Acceptance definitely committed; completion did not report a confirmed successful commit.
	Completion,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RowRegistrationError {
	pub phase: RowRegistrationPhase,
	pub source: RowError,
}

impl fmt::Display for RowRegistrationError {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "registration {:?} failed: {}", self.phase, self.source)
	}
}

impl Error for RowRegistrationError {
	fn source(&self) -> Option<&(dyn Error + 'static)> {
		Some(&self.source)
	}
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum SessionPhase {
	Message,
	Acceptance,
	Completion,
}

/// A callback-scoped view of one trusted storage transaction.
///
/// Application rows are isolated from beaconcrypt's private keys. A session permits zero or one
/// native operation, including rejected attempts. Any method error aborts the transaction even if
/// the callback catches it. Native ratchets never leave the library. A [`CachedRowServer`] may retain
/// the committed peer after this session and its outer transaction succeed.
///
/// The callback is part of the trusted persistence boundary: it may encode and store pending
/// results, but must not publish them or perform irreversible external effects before commit.
/// Library-owned message buffers are wiped on failure; application-created copies and callback
/// return values need their own erasure policy, such as `Zeroizing` for secret byte buffers.
pub struct RowSession<'a> {
	identity: &'a Server,
	identity_digest: &'a [u8; 32],
	lineage: SnapshotLineage,
	transaction: &'a mut dyn RowTransaction,
	phase: SessionPhase,
	native_used: bool,
	failure: Option<RowError>,
	pending_registration: Option<crate::RegistrationOutput>,
	cache: Option<&'a mut PeerCache>,
	pending_peer: Option<(u64, CachedPeer)>,
}

struct CachedPeer {
	peer: EstablishedRemote<crypto_sign::PublicKey>,
	bytes: Zeroizing<Vec<u8>>,
	generation: u64,
}

struct PeerCache {
	capacity: usize,
	peers: BTreeMap<u64, CachedPeer>,
}

impl PeerCache {
	fn insert(&mut self, kid: u64, peer: CachedPeer) {
		if self.peers.len() == self.capacity {
			self.peers.pop_first();
		}
		self.peers.insert(kid, peer);
	}
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

/// A row server with a bounded cache of decoded peers and their exact committed row bytes.
///
/// A cache hit calls [`RowTransaction::expect`] instead of loading and decoding the peer. An
/// optimistic adapter can validate that expectation in its commit request; the default expectation
/// implementation still performs a storage read. Application reads remain the adapter's concern.
/// Every successful transaction, including a rejected native operation, must validate its reads.
///
/// Peers are moved into tentative operation state and retained only after confirmed durable commit.
/// Any transaction error clears the entire cache, including uncertain commit outcomes. Callbacks
/// are never retried. Registration uses the uncached two-phase path and does not populate the cache.
/// Cached secrets remain resident until eviction, clearing, or drop. When full, insertion evicts the
/// smallest cached peer ID; cache lookup and insertion do not scan all resident peers.
pub struct CachedRowServer<S: RowStore> {
	server: RowServer<S>,
	cache: PeerCache,
}

impl<S: RowStore> CachedRowServer<S> {
	pub fn create(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		store: S,
		lineage: SnapshotLineage,
		cache_capacity: usize,
	) -> Result<Self, RowError> {
		RowServer::create(server_kid, id_seed, mldsa_seed, store, lineage)
			.map(|server| Self::from_server(server, cache_capacity))
	}

	pub fn open(
		store: S,
		lineage: SnapshotLineage,
		cache_capacity: usize,
	) -> Result<Self, RowError> {
		RowServer::open(store, lineage).map(|server| Self::from_server(server, cache_capacity))
	}

	/// Wrap an existing row server. Capacity zero disables caching; no entries are allocated eagerly.
	pub fn from_server(server: RowServer<S>, cache_capacity: usize) -> Self {
		Self {
			server,
			cache: PeerCache {
				capacity: cache_capacity,
				peers: BTreeMap::new(),
			},
		}
	}

	/// Discard cached secrets and return the uncached server.
	pub fn into_server(self) -> RowServer<S> {
		self.server
	}

	pub const fn cache_capacity(&self) -> usize {
		self.cache.capacity
	}

	pub fn cached_peer_count(&self) -> usize {
		self.cache.peers.len()
	}

	pub fn clear_cache(&mut self) {
		self.cache.peers.clear();
	}

	pub const fn lineage(&self) -> SnapshotLineage {
		self.server.lineage()
	}
	pub fn identity_key_kid(&self) -> u64 {
		self.server.identity_key_kid()
	}
	pub fn identity_pk(&self) -> &crypto_sign::PublicKey {
		self.server.identity_pk()
	}
	pub fn mldsa_public_key(&self) -> [u8; crate::MLDSA_PUBLIC_KEY_LEN] {
		self.server.mldsa_public_key()
	}

	/// Compose one message transition and application rows with the same contract as [`RowServer::transaction`].
	pub fn transaction<T>(
		&mut self,
		operation: impl FnOnce(&mut RowSession<'_>) -> Result<T, RowError>,
	) -> Result<T, RowError> {
		if self.cache.capacity == 0 {
			return self.server.transaction(operation);
		}
		let server = &mut self.server;
		let result = transact(&mut server.store, |transaction| {
			let mut session = RowSession::new(
				&server.identity,
				&server.identity_digest,
				server.lineage,
				transaction,
				SessionPhase::Message,
				None,
			);
			session.cache = Some(&mut self.cache);
			let output = operation(&mut session);
			let output = session.finish(output)?;
			Ok((output, session.pending_peer.take()))
		});
		match result {
			Ok((output, pending)) => {
				if let Some((kid, peer)) = pending {
					self.cache.insert(kid, peer);
				}
				Ok(output)
			}
			Err(error) => {
				self.clear_cache();
				Err(error)
			}
		}
	}

	/// Use the uncached registration path, preserving its two separate durable phases.
	pub fn registration_transaction<A, T>(
		&mut self,
		accept: impl FnOnce(&mut RowSession<'_>) -> Result<RowRegistrationDecision<A, T>, RowError>,
		complete: impl FnOnce(&mut RowSession<'_>, A) -> Result<T, RowError>,
	) -> Result<T, RowRegistrationError> {
		let result = self.server.registration_transaction(accept, complete);
		if result.is_err() {
			self.clear_cache();
		}
		result
	}

	pub fn register_beacon(
		&mut self,
		bytes: &[u8],
		data: Option<&[u8]>,
	) -> Result<Option<RegResponse>, RowError> {
		let result = self.server.register_beacon(bytes, data);
		if result.is_err() {
			self.clear_cache();
		}
		result
	}

	pub fn encrypt_message(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<Encrypted>, RowError> {
		if !send_input_fits(bytes, self.identity_key_kid()) {
			return Ok(None);
		}
		let output = self.transaction(|session| session.encrypt_message(bytes, kid))?;
		Ok(output.message.map(|mut message| Encrypted {
			ciphertext: std::mem::take(&mut *message.data),
			key_id: message.key_id,
			seq: message.sequence,
		}))
	}

	pub fn decrypt_message(&mut self, bytes: &[u8]) -> Result<Option<Decrypted>, RowError> {
		if crate::ratchet::encrypted_frame_sender(bytes).is_none() {
			return Ok(None);
		}
		let output = self.transaction(|session| session.decrypt_message(bytes))?;
		Ok(output.message.map(|mut message| Decrypted {
			plaintext: std::mem::take(&mut *message.data),
			key_id: message.key_id,
			seq: message.sequence,
		}))
	}
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

	/// Compose application preflight, at most one message transition, and application writes.
	///
	/// The callback's result is returned only after the outer durable commit. Its session methods
	/// cannot be used afterward. A callback error rolls back all writes; any pending native output
	/// is discarded. Do not publish tentative output or irreversible effects from the callback.
	pub fn transaction<T>(
		&mut self,
		operation: impl FnOnce(&mut RowSession<'_>) -> Result<T, RowError>,
	) -> Result<T, RowError> {
		transact(&mut self.store, |transaction| {
			let mut session = RowSession::new(
				&self.identity,
				&self.identity_digest,
				self.lineage,
				transaction,
				SessionPhase::Message,
				None,
			);
			let output = operation(&mut session);
			session.finish(output)
		})
	}

	/// Compose registration across its separate acceptance and completion commits.
	///
	/// The first callback may return a cached or terminal result without accepting anything. To
	/// continue, it must call `accept_registration` successfully and return `Continue(context)`.
	/// Its application writes and replay marker then commit together. Only a confirmed commit
	/// transfers the private, one-use pending material into the second callback.
	///
	/// Completion may revalidate authorization, construct one response, and store its exact result
	/// and application metadata with the new peer. It may instead commit a terminal application
	/// result without constructing a response. A completion failure never removes the acceptance
	/// marker. No pending material is persisted or returned; a crash between phases requires the
	/// application's incomplete receipt policy, not a retry of the accepted InitKex.
	pub fn registration_transaction<A, T>(
		&mut self,
		accept: impl FnOnce(&mut RowSession<'_>) -> Result<RowRegistrationDecision<A, T>, RowError>,
		complete: impl FnOnce(&mut RowSession<'_>, A) -> Result<T, RowError>,
	) -> Result<T, RowRegistrationError> {
		let accepted = transact(&mut self.store, |transaction| {
			let mut session = RowSession::new(
				&self.identity,
				&self.identity_digest,
				self.lineage,
				transaction,
				SessionPhase::Acceptance,
				None,
			);
			let decision = accept(&mut session);
			let decision = session.finish(decision)?;
			match decision {
				RowRegistrationDecision::Return(output) => Ok(Ok(output)),
				RowRegistrationDecision::Continue(context) => {
					let pending = session
						.pending_registration
						.take()
						.ok_or(RowError::InvalidSession)?;
					Ok(Err((pending, context)))
				}
			}
		})
		.map_err(|source| RowRegistrationError {
			phase: RowRegistrationPhase::Acceptance,
			source,
		})?;
		let (pending, context) = match accepted {
			Ok(output) => return Ok(output),
			Err(continuation) => continuation,
		};
		transact(&mut self.store, |transaction| {
			let mut session = RowSession::new(
				&self.identity,
				&self.identity_digest,
				self.lineage,
				transaction,
				SessionPhase::Completion,
				Some(pending),
			);
			let output = complete(&mut session, context);
			session.finish(output)
		})
		.map_err(|source| RowRegistrationError {
			phase: RowRegistrationPhase::Completion,
			source,
		})
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
		// Preserve the convenience API's validation before any database access. Composed callbacks
		// instead choose their own preflight inside the acceptance transaction.
		let mut session = self.identity.row_session(self.identity_key_kid());
		let Some(pending) = session.get_shared_secret(bytes) else {
			return Ok(None);
		};
		let accepted = transact(&mut self.store, |transaction| {
			consume_registration_marker(transaction, self.lineage, &self.identity_digest, &pending)
		})?;
		if !accepted {
			return Ok(None);
		}
		let output = transact(&mut self.store, |transaction| {
			complete_registration(
				&self.identity,
				&self.identity_digest,
				self.lineage,
				transaction,
				pending,
				data,
			)
		})?;
		Ok(output.message.map(|mut message| RegResponse {
			serialized: std::mem::take(&mut *message.data),
			kid: message.key_id,
		}))
	}

	/// Encrypt and durably commit only this peer. A consumed send key is saved even on seal failure.
	pub fn encrypt_message(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<Encrypted>, RowError> {
		if !send_input_fits(bytes, self.identity_key_kid()) {
			return Ok(None);
		}
		let output = self.transaction(|session| session.encrypt_message(bytes, kid))?;
		Ok(output.message.map(|mut message| Encrypted {
			ciphertext: std::mem::take(&mut *message.data),
			key_id: message.key_id,
			seq: message.sequence,
		}))
	}

	/// Authenticate once and commit the resulting peer before releasing plaintext. Rejection writes nothing.
	pub fn decrypt_message(&mut self, bytes: &[u8]) -> Result<Option<Decrypted>, RowError> {
		if crate::ratchet::encrypted_frame_sender(bytes).is_none() {
			return Ok(None);
		}
		let output = self.transaction(|session| session.decrypt_message(bytes))?;
		Ok(output.message.map(|mut message| Decrypted {
			plaintext: std::mem::take(&mut *message.data),
			key_id: message.key_id,
			seq: message.sequence,
		}))
	}
}

fn send_input_fits(bytes: &[u8], sender: u64) -> bool {
	// Sequence one gives a conservative minimum framing size. The actual sequence is checked
	// by the native encryptor after loading the peer, before deriving any message key.
	!bytes.is_empty() && crate::wire::frame_len(bytes.len(), 1, sender).is_some()
}

impl<'a> RowSession<'a> {
	fn new(
		identity: &'a Server,
		identity_digest: &'a [u8; 32],
		lineage: SnapshotLineage,
		transaction: &'a mut dyn RowTransaction,
		phase: SessionPhase,
		pending_registration: Option<crate::RegistrationOutput>,
	) -> Self {
		Self {
			identity,
			identity_digest,
			lineage,
			transaction,
			phase,
			native_used: false,
			failure: None,
			pending_registration,
			cache: None,
			pending_peer: None,
		}
	}

	fn finish<T>(&self, output: Result<T, RowError>) -> Result<T, RowError> {
		match &self.failure {
			Some(error) => Err(error.clone()),
			None => output,
		}
	}

	fn checked<T>(
		&mut self,
		operation: impl FnOnce(&mut Self) -> Result<T, RowError>,
	) -> Result<T, RowError> {
		if let Some(error) = &self.failure {
			return Err(error.clone());
		}
		let output = operation(self);
		if let Err(error) = &output {
			self.failure = Some(error.clone());
		}
		output
	}

	fn begin_native(&mut self, phase: SessionPhase) -> Result<(), RowError> {
		if self.phase != phase || self.native_used {
			return Err(RowError::InvalidSession);
		}
		self.native_used = true;
		Ok(())
	}

	fn application_key(&self, key: &[u8]) -> Vec<u8> {
		let mut namespaced = b"beaconcrypt/application/v1/".to_vec();
		namespaced.extend_from_slice(self.lineage.as_bytes());
		namespaced.extend_from_slice(key);
		namespaced
	}

	/// Load application bytes from this lineage's separate application namespace.
	pub fn load_application(&mut self, key: &[u8]) -> Result<Option<Zeroizing<Vec<u8>>>, RowError> {
		self.checked(|session| {
			let key = session.application_key(key);
			session
				.transaction
				.load(&key)
				.map(|value| value.map(Zeroizing::new))
		})
	}

	/// Stage application bytes in the same transaction as the native state transition.
	pub fn store_application(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.checked(|session| {
			let key = session.application_key(key);
			session.transaction.store(&key, value)
		})
	}

	pub fn encrypt_message(&mut self, bytes: &[u8], kid: u64) -> Result<RowTransition, RowError> {
		self.checked(|session| {
			session.begin_native(SessionPhase::Message)?;
			if !send_input_fits(bytes, session.identity.identity_key_kid()) {
				return Ok(RowTransition::unchanged());
			}
			session.with_peer(kid, |server| {
				let before = server
					.ratchet_status(kid)
					.ok_or(RowError::InvalidRow)?
					.send_sequence();
				let encrypted = server.encrypt_message(bytes, kid);
				let after = server
					.ratchet_status(kid)
					.ok_or(RowError::InvalidRow)?
					.send_sequence();
				Ok(RowTransition {
					message: encrypted.map(|message| RowMessage {
						data: Zeroizing::new(message.ciphertext),
						key_id: message.key_id,
						sequence: message.seq,
					}),
					changed: before != after,
				})
			})
		})
	}

	pub fn decrypt_message(&mut self, bytes: &[u8]) -> Result<RowTransition, RowError> {
		self.checked(|session| {
			session.begin_native(SessionPhase::Message)?;
			let Some(kid) = crate::ratchet::encrypted_frame_sender(bytes) else {
				return Ok(RowTransition::unchanged());
			};
			session.with_peer(kid, |server| {
				let message = server.decrypt_message(bytes).map(|message| RowMessage {
					data: Zeroizing::new(message.plaintext),
					key_id: message.key_id,
					sequence: message.seq,
				});
				Ok(RowTransition {
					changed: message.is_some(),
					message,
				})
			})
		})
	}

	/// Accept once in the first registration phase; the private token cannot leave this session.
	pub fn accept_registration(&mut self, bytes: &[u8]) -> Result<bool, RowError> {
		self.checked(|session| {
			session.begin_native(SessionPhase::Acceptance)?;
			let mut server = session
				.identity
				.row_session(session.identity.identity_key_kid());
			let Some(pending) = server.get_shared_secret(bytes) else {
				return Ok(false);
			};
			if !consume_registration_marker(
				session.transaction,
				session.lineage,
				session.identity_digest,
				&pending,
			)? {
				return Ok(false);
			}
			session.pending_registration = Some(pending);
			Ok(true)
		})
	}

	/// Construct once in the completion phase; response, peer and application rows share one commit.
	pub fn complete_registration(
		&mut self,
		data: Option<&[u8]>,
	) -> Result<RowTransition, RowError> {
		self.checked(|session| {
			session.begin_native(SessionPhase::Completion)?;
			let pending = session
				.pending_registration
				.take()
				.ok_or(RowError::InvalidSession)?;
			complete_registration(
				session.identity,
				session.identity_digest,
				session.lineage,
				session.transaction,
				pending,
				data,
			)
		})
	}

	fn with_peer(
		&mut self,
		kid: u64,
		operation: impl FnOnce(&mut Server) -> Result<RowTransition, RowError>,
	) -> Result<RowTransition, RowError> {
		let key = storage_key(self.lineage, PEER, &kid.to_le_bytes());
		let cached = self
			.cache
			.as_mut()
			.and_then(|cache| cache.peers.remove(&kid));
		let (mut bytes, mut generation, peer) = match cached {
			Some(cached) => {
				self.transaction.expect(&key, Some(&cached.bytes))?;
				(cached.bytes, cached.generation, cached.peer)
			}
			None => {
				let Some(bytes) = self.transaction.load(&key)? else {
					return Ok(RowTransition::unchanged());
				};
				let bytes = Zeroizing::new(bytes);
				let row = bound_row(&key, &bytes, self.identity_digest)?;
				let generation = row.generation;
				let peer = decode_peer(row.payload)?;
				(bytes, generation, peer)
			}
		};
		let mut server = self.identity.row_session(self.identity.identity_key_kid());
		server.put_row_peer(kid, peer);
		let output = operation(&mut server)?;
		let peer = server.take_row_peer(kid).ok_or(RowError::InvalidRow)?;
		if output.changed {
			generation = generation
				.checked_add(1)
				.ok_or(RowError::GenerationExhausted)?;
			bytes = encode_row(&key, generation, self.identity_digest, &encode_peer(&peer)?);
			self.transaction.store(&key, &bytes)?;
		}
		if self.cache.is_some() {
			self.pending_peer = Some((
				kid,
				CachedPeer {
					peer,
					bytes,
					generation,
				},
			));
		}
		Ok(output)
	}
}

fn consume_registration_marker(
	transaction: &mut dyn RowTransaction,
	lineage: SnapshotLineage,
	identity_digest: &[u8; 32],
	pending: &crate::RegistrationOutput,
) -> Result<bool, RowError> {
	let replay_key = storage_key(lineage, REGISTRATION, &pending.row_registration_id());
	if let Some(bytes) = transaction.load(&replay_key)? {
		let bytes = Zeroizing::new(bytes);
		let row = bound_row(&replay_key, &bytes, identity_digest)?;
		if row.generation != 0 || !row.payload.is_empty() {
			return Err(RowError::InvalidRow);
		}
		return Ok(false);
	}
	transaction.store(
		&replay_key,
		&encode_row(&replay_key, 0, identity_digest, &[]),
	)?;
	Ok(true)
}

fn complete_registration(
	identity: &Server,
	identity_digest: &[u8; 32],
	lineage: SnapshotLineage,
	transaction: &mut dyn RowTransaction,
	pending: crate::RegistrationOutput,
	data: Option<&[u8]>,
) -> Result<RowTransition, RowError> {
	let allocator_key = storage_key(lineage, ALLOCATOR, &[]);
	let bytes = Zeroizing::new(
		transaction
			.load(&allocator_key)?
			.ok_or(RowError::InvalidRow)?,
	);
	let row = bound_row(&allocator_key, &bytes, identity_digest)?;
	let last = u64::from_le_bytes(row.payload.try_into().map_err(|_| RowError::InvalidRow)?);
	if last < identity.identity_key_kid() {
		return Err(RowError::InvalidRow);
	}
	let Some(kid) = last.checked_add(1) else {
		return Ok(RowTransition::unchanged());
	};
	let peer_key = storage_key(lineage, PEER, &kid.to_le_bytes());
	if transaction.load(&peer_key)?.is_some() {
		return Err(RowError::Conflict);
	}
	let mut server = identity.row_session(last);
	let Some(response) = server.build_registration_response(pending, data) else {
		return Ok(RowTransition::unchanged());
	};
	let peer = server.take_row_peer(kid).ok_or(RowError::InvalidRow)?;
	let sequence = peer.ratchet().status().send_sequence();
	let generation = row
		.generation
		.checked_add(1)
		.ok_or(RowError::GenerationExhausted)?;
	transaction.store(
		&allocator_key,
		&encode_row(
			&allocator_key,
			generation,
			identity_digest,
			&kid.to_le_bytes(),
		),
	)?;
	transaction.store(
		&peer_key,
		&encode_row(&peer_key, 0, identity_digest, &encode_peer(&peer)?),
	)?;
	Ok(RowTransition {
		message: Some(RowMessage {
			data: Zeroizing::new(response.serialized),
			key_id: response.kid,
			sequence,
		}),
		changed: true,
	})
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
		install_peer_id(server, PEER_KID, generation)
	}

	fn install_peer_id(server: &mut RowServer<TestStore>, kid: u64, generation: u64) -> Vec<u8> {
		let mut session = server.identity.row_session(SERVER_KID);
		let public_key = crypto_sign::KeyPair::from_seed(&[0x64; 32])
			.unwrap()
			.public_key;
		session.add_known_kid(kid, public_key);
		let peer = session.take_row_peer(kid).unwrap();
		let key = storage_key(LINEAGE, PEER, &kid.to_le_bytes());
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

	#[derive(Default)]
	struct DeferredStore {
		rows: BTreeMap<Vec<u8>, Vec<u8>>,
		loads: usize,
		expects: usize,
		fail_load: bool,
		fail_store: bool,
		fail_commit: bool,
		lose_acknowledgement: bool,
	}

	struct DeferredTransaction<'a> {
		inner: TestTransaction<'a>,
		loads: &'a mut usize,
		expects: &'a mut usize,
		expected: &'a mut BTreeMap<Vec<u8>, Option<Zeroizing<Vec<u8>>>>,
	}

	impl RowTransaction for DeferredTransaction<'_> {
		fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
			*self.loads += 1;
			self.inner.load(key)
		}

		fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
			self.inner.store(key, value)
		}

		fn expect(&mut self, key: &[u8], expected: Option<&[u8]>) -> Result<(), RowError> {
			*self.expects += 1;
			self.expected.insert(
				key.to_vec(),
				expected.map(|bytes| Zeroizing::new(bytes.to_vec())),
			);
			Ok(())
		}
	}

	impl RowStore for DeferredStore {
		fn transaction(
			&mut self,
			operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
		) -> Result<(), RowError> {
			let mut rows = self.rows.clone();
			let mut expected = BTreeMap::new();
			operation(&mut DeferredTransaction {
				inner: TestTransaction {
					rows: &mut rows,
					fail_load: self.fail_load,
					fail_store: self.fail_store,
				},
				loads: &mut self.loads,
				expects: &mut self.expects,
				expected: &mut expected,
			})?;
			for (key, value) in expected {
				if self.rows.get(&key).map(Vec::as_slice) != value.as_deref().map(Vec::as_slice) {
					return Err(RowError::Conflict);
				}
			}
			if self.fail_commit {
				return Err(RowError::Storage("commit failed".into()));
			}
			self.rows = rows;
			if self.lose_acknowledgement {
				return Err(RowError::Storage("commit acknowledgement lost".into()));
			}
			Ok(())
		}
	}

	fn deferred_server(capacity: usize) -> CachedRowServer<DeferredStore> {
		let mut server = server();
		install_peer(&mut server, 0);
		install_peer_id(&mut server, PEER_KID + 1, 0);
		CachedRowServer::open(
			DeferredStore {
				rows: server.store.rows,
				..DeferredStore::default()
			},
			LINEAGE,
			capacity,
		)
		.unwrap()
	}

	#[test]
	fn cache_hits_stage_expectations_without_loading_and_zero_capacity_disables_the_cache() {
		for capacity in [0, 1, usize::MAX] {
			let mut cached = deferred_server(capacity);
			assert_eq!(cached.cache_capacity(), capacity);
			assert_eq!(cached.cached_peer_count(), 0);
			assert_eq!(cached.lineage(), LINEAGE);
			assert_eq!(cached.identity_key_kid(), SERVER_KID);
			let public_key = cached.identity_pk().clone();
			let mldsa_key = cached.mldsa_public_key();
			let loads = cached.server.store.loads;
			assert_eq!(
				cached
					.encrypt_message(b"first", PEER_KID)
					.unwrap()
					.unwrap()
					.seq,
				1
			);
			assert_eq!(cached.server.store.loads, loads + 1);
			assert_eq!(cached.cached_peer_count(), usize::from(capacity != 0));
			let second = cached
				.encrypt_message(b"second", PEER_KID)
				.unwrap()
				.unwrap();
			assert_eq!(second.seq, 2);
			assert_eq!(cached.server.store.expects, usize::from(capacity != 0));
			assert_eq!(
				cached.server.store.loads,
				loads + 1 + usize::from(capacity == 0)
			);
			cached.clear_cache();
			assert_eq!(cached.cached_peer_count(), 0);
			assert_eq!(
				cached
					.encrypt_message(b"third", PEER_KID)
					.unwrap()
					.unwrap()
					.seq,
				3
			);
			let uncached = cached.into_server();
			assert_eq!(uncached.identity_pk(), &public_key);
			assert_eq!(uncached.mldsa_public_key(), mldsa_key);
			let mut reopened = CachedRowServer::open(uncached.store, LINEAGE, capacity).unwrap();
			assert_eq!(reopened.cached_peer_count(), 0);
			assert_eq!(
				reopened
					.encrypt_message(b"reopened", PEER_KID)
					.unwrap()
					.unwrap()
					.seq,
				4
			);
		}
	}

	#[test]
	fn cache_eviction_and_uncached_fallback_preserve_each_peer_sequence() {
		let mut server = server();
		install_peer(&mut server, 0);
		install_peer_id(&mut server, PEER_KID + 1, 0);
		let mut cached = CachedRowServer::from_server(server, 1);
		for (kid, sequence) in [(PEER_KID, 1), (PEER_KID + 1, 1), (PEER_KID, 2)] {
			assert_eq!(
				cached
					.encrypt_message(b"message", kid)
					.unwrap()
					.unwrap()
					.seq,
				sequence
			);
			assert_eq!(cached.cached_peer_count(), 1);
		}
		cached.server.store.fail_load = true;
		assert!(matches!(
			cached.encrypt_message(b"default expect reads", PEER_KID),
			Err(RowError::Storage(_))
		));
		assert_eq!(cached.cached_peer_count(), 0);
		cached.server.store.fail_load = false;
		assert_eq!(
			cached
				.encrypt_message(b"reload", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			3
		);
	}

	#[test]
	fn deferred_stale_expectation_suppresses_output_and_does_not_retry_the_callback() {
		let mut cached = deferred_server(2);
		assert_eq!(
			cached
				.encrypt_message(b"warm", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			1
		);
		let mut other = RowServer::open(
			TestStore {
				rows: cached.server.store.rows.clone(),
				..TestStore::default()
			},
			LINEAGE,
		)
		.unwrap();
		assert_eq!(
			other
				.encrypt_message(b"other worker", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			2
		);
		cached.server.store.rows = other.store.rows;
		let before = cached.server.store.rows.clone();
		let mut calls = 0;
		let result = cached.transaction(|session| {
			calls += 1;
			let message = session
				.encrypt_message(b"stale candidate", PEER_KID)?
				.message
				.unwrap();
			session.store_application(b"receipt", message.data())?;
			Ok(message)
		});
		assert_eq!(result.err(), Some(RowError::Conflict));
		assert_eq!(calls, 1);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(cached.server.store.rows, before);
		assert_eq!(
			cached
				.encrypt_message(b"fresh", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			3
		);
	}

	#[test]
	fn cached_callback_storage_and_commit_failures_discard_tentative_peers() {
		for failure in ["callback", "sticky", "store", "commit", "unknown"] {
			let mut cached = deferred_server(2);
			assert_eq!(
				cached
					.encrypt_message(b"warm", PEER_KID)
					.unwrap()
					.unwrap()
					.seq,
				1
			);
			cached
				.encrypt_message(b"other warm peer", PEER_KID + 1)
				.unwrap()
				.unwrap();
			assert_eq!(cached.cached_peer_count(), 2);
			let before = cached.server.store.rows.clone();
			cached.server.store.fail_store = failure == "store";
			cached.server.store.fail_commit = failure == "commit";
			cached.server.store.lose_acknowledgement = failure == "unknown";
			let mut calls = 0;
			let result = cached.transaction(|session| {
				calls += 1;
				let message = session
					.encrypt_message(b"tentative", PEER_KID)?
					.message
					.unwrap();
				session.store_application(b"receipt", message.data())?;
				if failure == "callback" {
					return Err(RowError::Storage("application rejected output".into()));
				}
				if failure == "sticky" {
					assert_eq!(
						session
							.encrypt_message(b"second native call", PEER_KID)
							.err(),
						Some(RowError::InvalidSession)
					);
				}
				Ok(message)
			});
			assert!(result.is_err(), "{failure}");
			assert_eq!(calls, 1);
			assert_eq!(cached.cached_peer_count(), 0, "{failure}");
			if failure != "unknown" {
				assert_eq!(cached.server.store.rows, before, "{failure}");
			}
			cached.server.store.fail_store = false;
			cached.server.store.fail_commit = false;
			cached.server.store.lose_acknowledgement = false;
			let receipt = cached
				.transaction(|session| session.load_application(b"receipt"))
				.unwrap();
			assert_eq!(receipt.is_some(), failure == "unknown");
			let loads = cached.server.store.loads;
			let next = cached.encrypt_message(b"fresh", PEER_KID).unwrap().unwrap();
			assert_eq!(
				next.seq,
				if failure == "unknown" { 3 } else { 2 },
				"{failure}"
			);
			assert_eq!(cached.server.store.loads, loads + 1);
		}
	}

	#[test]
	fn cached_preflight_rejection_and_application_only_callbacks_preserve_valid_entries() {
		let mut cached = deferred_server(1);
		cached.encrypt_message(b"warm", PEER_KID).unwrap().unwrap();
		let before = cached.server.store.rows.clone();
		let loads = cached.server.store.loads;
		let expects = cached.server.store.expects;
		cached.server.store.fail_load = true;
		assert!(cached.encrypt_message(b"", PEER_KID).unwrap().is_none());
		assert!(
			cached
				.encrypt_message(&vec![0; crate::MAX_MESSAGE_SIZE], PEER_KID)
				.unwrap()
				.is_none()
		);
		assert!(cached.decrypt_message(b"malformed").unwrap().is_none());
		assert!(
			cached
				.register_beacon(b"malformed", None)
				.unwrap()
				.is_none()
		);
		assert_eq!(
			cached
				.transaction(|_| Ok(b"cached application policy"))
				.unwrap(),
			b"cached application policy"
		);
		assert_eq!(cached.server.store.loads, loads);
		assert_eq!(cached.server.store.expects, expects);
		assert_eq!(cached.server.store.rows, before);
		assert_eq!(cached.cached_peer_count(), 1);
		assert_eq!(
			cached
				.encrypt_message(b"warm no-load path", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			2
		);
	}

	#[test]
	fn cached_generation_exhaustion_and_invalid_reloads_never_reuse_tentative_keys() {
		let mut server = server();
		let key = install_peer(&mut server, u64::MAX - 1);
		let mut cached = CachedRowServer::from_server(server, 1);
		assert_eq!(
			cached
				.encrypt_message(b"last generation", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			1
		);
		let committed = cached.server.store.rows.clone();
		assert_eq!(
			cached.encrypt_message(b"exhausted", PEER_KID).err(),
			Some(RowError::GenerationExhausted)
		);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(cached.server.store.rows, committed);
		assert_eq!(
			decode_row(&key, &committed[&key]).unwrap().generation,
			u64::MAX
		);
		assert_eq!(
			cached.encrypt_message(b"still exhausted", PEER_KID).err(),
			Some(RowError::GenerationExhausted)
		);
		assert_eq!(cached.server.store.rows, committed);

		let mut cached = deferred_server(1);
		cached.encrypt_message(b"warm", PEER_KID).unwrap().unwrap();
		let committed = cached.server.store.rows[&key].clone();
		cached
			.server
			.store
			.rows
			.insert(key.clone(), b"corrupted".to_vec());
		assert_eq!(
			cached.encrypt_message(b"stale", PEER_KID).err(),
			Some(RowError::Conflict)
		);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(
			cached.encrypt_message(b"invalid reload", PEER_KID).err(),
			Some(RowError::InvalidRow)
		);
		assert_eq!(cached.cached_peer_count(), 0);
		cached.server.store.rows.insert(key, committed);
		assert_eq!(
			cached
				.encrypt_message(b"valid reload", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			2
		);
	}

	#[test]
	fn cached_transaction_gate_discards_pending_output_when_callbacks_are_misused() {
		#[derive(Clone, Copy)]
		enum Behaviour {
			Normal,
			Skip,
			Repeat,
			Swallow,
		}
		struct MisbehavingStore {
			inner: TestStore,
			behaviour: Behaviour,
		}
		impl RowStore for MisbehavingStore {
			fn transaction(
				&mut self,
				operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
			) -> Result<(), RowError> {
				if matches!(self.behaviour, Behaviour::Normal) {
					return self.inner.transaction(operation);
				}
				let mut rows = self.inner.rows.clone();
				let mut transaction = TestTransaction {
					rows: &mut rows,
					fail_load: false,
					fail_store: false,
				};
				match self.behaviour {
					Behaviour::Skip => (),
					Behaviour::Repeat => {
						let _ = operation(&mut transaction);
						let _ = operation(&mut transaction);
					}
					Behaviour::Swallow => {
						let _ = operation(&mut transaction);
					}
					Behaviour::Normal => unreachable!(),
				}
				Ok(())
			}
		}
		struct PendingOutput {
			_message: RowMessage,
			dropped: Arc<AtomicUsize>,
		}
		impl Drop for PendingOutput {
			fn drop(&mut self) {
				self.dropped.fetch_add(1, Ordering::SeqCst);
			}
		}
		for behaviour in [Behaviour::Skip, Behaviour::Repeat, Behaviour::Swallow] {
			let mut server = server();
			install_peer(&mut server, 0);
			let mut cached = CachedRowServer::open(
				MisbehavingStore {
					inner: server.store,
					behaviour: Behaviour::Normal,
				},
				LINEAGE,
				1,
			)
			.unwrap();
			cached.encrypt_message(b"warm", PEER_KID).unwrap().unwrap();
			let committed = cached.server.store.inner.rows.clone();
			cached.server.store.behaviour = behaviour;
			let dropped = Arc::new(AtomicUsize::new(0));
			let mut calls = 0;
			let result = cached.transaction(|session| {
				calls += 1;
				let message = session
					.encrypt_message(b"pending", PEER_KID)?
					.message
					.unwrap();
				let pending = PendingOutput {
					_message: message,
					dropped: Arc::clone(&dropped),
				};
				if matches!(behaviour, Behaviour::Swallow) {
					return Err(RowError::InvalidSession);
				}
				Ok(pending)
			});
			assert!(result.is_err());
			assert_eq!(calls, usize::from(!matches!(behaviour, Behaviour::Skip)));
			assert_eq!(dropped.load(Ordering::SeqCst), calls);
			assert_eq!(cached.cached_peer_count(), 0);
			assert_eq!(cached.server.store.inner.rows, committed);
			cached.server.store.behaviour = Behaviour::Normal;
			assert_eq!(
				cached
					.encrypt_message(b"fresh", PEER_KID)
					.unwrap()
					.unwrap()
					.seq,
				2
			);
		}
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn cached_rejected_receives_validate_deferred_expectations_without_writing() {
		use crate::ProviderBeacon;
		let mut cached = CachedRowServer::create(
			SERVER_KID,
			Some(&[0x62; 32]),
			Some(&[0x63; 32]),
			DeferredStore::default(),
			LINEAGE,
			1,
		)
		.unwrap();
		let mut beacon = crate::Beacon::new(
			SERVER_KID,
			cached.identity_pk().as_bytes(),
			&cached.mldsa_public_key(),
		);
		let request = beacon.get_registration_bundle().unwrap();
		let response = cached.register_beacon(&request, None).unwrap().unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		assert_eq!(cached.cached_peer_count(), 0);
		let first = beacon.encrypt_message(b"first").unwrap();
		let second = beacon.encrypt_message(b"second").unwrap();
		assert_eq!(
			cached
				.decrypt_message(&first.ciphertext)
				.unwrap()
				.unwrap()
				.plaintext,
			b"first"
		);
		let before = cached.server.store.rows.clone();
		let loads = cached.server.store.loads;
		let expects = cached.server.store.expects;
		assert!(cached.decrypt_message(&first.ciphertext).unwrap().is_none());
		assert_eq!(cached.server.store.rows, before);
		assert_eq!(cached.server.store.loads, loads);
		assert_eq!(cached.server.store.expects, expects + 1);
		assert_eq!(cached.cached_peer_count(), 1);

		let mut other = RowServer::open(
			TestStore {
				rows: before,
				..TestStore::default()
			},
			LINEAGE,
		)
		.unwrap();
		assert_eq!(
			other
				.decrypt_message(&second.ciphertext)
				.unwrap()
				.unwrap()
				.plaintext,
			b"second"
		);
		cached.server.store.rows = other.store.rows;
		let current = cached.server.store.rows.clone();
		// The local ratchet rejects this replay without changing anything, but its stale read must
		// still fail the outer transaction. A backend cannot infer freshness from zero writes.
		assert_eq!(
			cached.decrypt_message(&first.ciphertext).err(),
			Some(RowError::Conflict)
		);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(cached.server.store.rows, current);
		assert!(
			cached
				.decrypt_message(&second.ciphertext)
				.unwrap()
				.is_none()
		);
		assert_eq!(cached.cached_peer_count(), 1);
		let third = beacon.encrypt_message(b"third").unwrap();
		assert_eq!(
			cached
				.decrypt_message(&third.ciphertext)
				.unwrap()
				.unwrap()
				.plaintext,
			b"third"
		);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn cached_registration_uses_uncached_phases_and_clears_resident_peers_on_phase_errors() {
		use crate::ProviderBeacon;
		let mut cached = CachedRowServer::from_server(server(), 2);
		let request = registration(&cached.server);
		assert_eq!(
			cached.register_beacon(&request, None).unwrap().unwrap().kid,
			PEER_KID
		);
		assert_eq!(cached.cached_peer_count(), 0);
		cached.encrypt_message(b"warm", PEER_KID).unwrap().unwrap();
		let before = cached.server.store.rows.clone();
		let request = registration(&cached.server);
		let acceptance_error = cached
			.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					Err::<RowRegistrationDecision<(), ()>, _>(RowError::Storage(
						"acceptance callback".into(),
					))
				},
				|_, ()| panic!("failed acceptance must not invoke completion"),
			)
			.unwrap_err();
		assert_eq!(acceptance_error.phase, RowRegistrationPhase::Acceptance);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(cached.server.store.rows, before);
		assert!(cached.register_beacon(&request, None).unwrap().is_some());
		cached
			.encrypt_message(b"warm again", PEER_KID)
			.unwrap()
			.unwrap();
		let before = cached.server.store.rows.clone();
		let request = registration(&cached.server);
		let completion_error = cached
			.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					Ok(RowRegistrationDecision::Continue(()))
				},
				|session, ()| {
					assert!(session.complete_registration(None)?.message.is_some());
					Err::<(), _>(RowError::Storage("completion callback".into()))
				},
			)
			.unwrap_err();
		assert_eq!(completion_error.phase, RowRegistrationPhase::Completion);
		assert_eq!(cached.cached_peer_count(), 0);
		assert_eq!(cached.server.store.rows.len(), before.len() + 1);
		for (key, value) in before {
			assert_eq!(cached.server.store.rows[&key], value);
		}
		assert!(cached.register_beacon(&request, None).unwrap().is_none());

		cached
			.encrypt_message(b"keep resident", PEER_KID)
			.unwrap()
			.unwrap();
		let mut beacon = crate::Beacon::new(
			SERVER_KID,
			cached.identity_pk().as_bytes(),
			&cached.mldsa_public_key(),
		);
		let request = beacon.get_registration_bundle().unwrap();
		let message = cached
			.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					session.store_application(b"registration", b"accepted")?;
					Ok(RowRegistrationDecision::Continue(()))
				},
				|session, ()| {
					let message = session
						.complete_registration(Some(b"registered"))?
						.message
						.unwrap();
					session.store_application(b"registration", message.data())?;
					Ok(message)
				},
			)
			.unwrap();
		assert_eq!(
			beacon.finish_registration(message.data()).unwrap(),
			b"registered"
		);
		assert_eq!(cached.cached_peer_count(), 1);
		cached.server.store.fail_commit = true;
		let request = registration(&cached.server);
		assert!(matches!(
			cached.register_beacon(&request, None),
			Err(RowError::Storage(_))
		));
		assert_eq!(cached.cached_peer_count(), 0);
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
			(
				RowError::InvalidSession,
				"invalid operation in row transaction session",
			),
		] {
			assert_eq!(error.to_string(), expected);
			assert!(error.source().is_none());
		}
	}

	#[cfg(feature = "beacon")]
	fn registration<S: RowStore>(server: &RowServer<S>) -> Vec<u8> {
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

	#[test]
	fn invalid_send_sizes_are_rejected_without_requiring_available_storage() {
		let mut server = server();
		let transactions = server.store.transactions;
		server.store.fail_load = true;
		assert!(server.encrypt_message(&[], PEER_KID).unwrap().is_none());
		let oversized = vec![0; crate::MAX_MESSAGE_SIZE + 1];
		assert!(
			server
				.encrypt_message(&oversized[..crate::MAX_MESSAGE_SIZE], PEER_KID)
				.unwrap()
				.is_none()
		);
		assert!(
			server
				.encrypt_message(&oversized, PEER_KID)
				.unwrap()
				.is_none()
		);
		assert_eq!(server.store.transactions, transactions);
	}

	#[test]
	fn composed_send_commits_application_receipt_and_cached_preflight_skips_native_work() {
		let mut server = server();
		let peer_key = install_peer(&mut server, 0);
		let before = server.store.rows.clone();
		let ciphertext = server
			.transaction(|session| {
				assert!(session.load_application(b"request").unwrap().is_none());
				let transition = session.encrypt_message(b"application request", PEER_KID)?;
				assert!(transition.changed);
				let message = transition.message.unwrap();
				assert_eq!(message.key_id(), PEER_KID);
				assert_eq!(message.sequence(), 1);
				assert!(!message.data().is_empty());
				session.store_application(b"request", message.data())?;
				// Even an application key equal to a private storage key uses a separate namespace.
				session.store_application(&peer_key, b"application metadata")?;
				Ok(message)
			})
			.unwrap();
		assert_eq!(server.store.rows.len(), before.len() + 2);
		assert_ne!(server.store.rows[&peer_key], before[&peer_key]);
		let committed = server.store.rows.clone();
		let cached = server
			.transaction(|session| {
				assert_eq!(
					session.load_application(&peer_key)?.unwrap().as_slice(),
					b"application metadata"
				);
				if let Some(receipt) = session.load_application(b"request")? {
					return Ok(receipt);
				}
				panic!("the receipt must prevent a second native transition")
			})
			.unwrap();
		assert_eq!(cached.as_slice(), ciphertext.data());
		assert_eq!(server.store.rows, committed);
		assert_eq!(
			server
				.encrypt_message(b"next request", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			2
		);
	}

	#[test]
	fn composed_finalizer_and_commit_failures_roll_back_native_and_application_rows() {
		let mut server = server();
		install_peer(&mut server, 0);
		let before = server.store.rows.clone();
		let failure = RowError::Storage("application finalizer failed".into());
		assert_eq!(
			server
				.transaction::<()>(|session| {
					let message = session
						.encrypt_message(b"withheld", PEER_KID)?
						.message
						.unwrap();
					session.store_application(b"receipt", message.data())?;
					Err(failure.clone())
				})
				.err(),
			Some(failure)
		);
		assert_eq!(server.store.rows, before);
		server.store.fail_commit = true;
		assert!(matches!(
			server.transaction(|session| {
				let message = session
					.encrypt_message(b"also withheld", PEER_KID)?
					.message
					.unwrap();
				session.store_application(b"receipt", message.data())?;
				Ok(message)
			}),
			Err(RowError::Storage(_))
		));
		assert_eq!(server.store.rows, before);
		server.store.fail_commit = false;
		assert_eq!(
			server
				.encrypt_message(b"fresh", PEER_KID)
				.unwrap()
				.unwrap()
				.seq,
			1
		);
	}

	#[test]
	fn rejected_native_attempts_still_use_the_single_allowance_and_errors_are_sticky() {
		let mut server = server();
		install_peer(&mut server, 0);
		let before = server.store.rows.clone();
		assert_eq!(
			server.transaction(|session| {
				session.store_application(b"tentative", b"must roll back")?;
				let rejected = session.decrypt_message(b"malformed")?;
				assert!(!rejected.changed);
				assert!(rejected.message.is_none());
				assert_eq!(
					session.encrypt_message(b"second", PEER_KID).err(),
					Some(RowError::InvalidSession)
				);
				assert_eq!(
					session.load_application(b"tentative").err(),
					Some(RowError::InvalidSession)
				);
				assert_eq!(
					session.store_application(b"late", b"blocked").err(),
					Some(RowError::InvalidSession)
				);
				Ok(())
			}),
			Err(RowError::InvalidSession)
		);
		assert_eq!(server.store.rows, before);
		assert_eq!(
			server.transaction(|session| {
				assert_eq!(
					session.accept_registration(b"wrong phase"),
					Err(RowError::InvalidSession)
				);
				Ok(())
			}),
			Err(RowError::InvalidSession)
		);
		assert_eq!(
			server.transaction(|session| {
				assert_eq!(
					session.complete_registration(None).err(),
					Some(RowError::InvalidSession)
				);
				Ok(())
			}),
			Err(RowError::InvalidSession)
		);
		assert_eq!(server.store.rows, before);
	}

	#[test]
	fn caught_storage_failure_blocks_later_io_and_prevents_commit() {
		struct Observed<'a> {
			loads: &'a AtomicUsize,
			stores: &'a AtomicUsize,
		}
		impl RowTransaction for Observed<'_> {
			fn load(&mut self, _: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
				self.loads.fetch_add(1, Ordering::SeqCst);
				Err(RowError::Storage("read failed".into()))
			}
			fn store(&mut self, _: &[u8], _: &[u8]) -> Result<(), RowError> {
				self.stores.fetch_add(1, Ordering::SeqCst);
				Ok(())
			}
		}
		let server = server();
		let loads = AtomicUsize::new(0);
		let stores = AtomicUsize::new(0);
		let mut transaction = Observed {
			loads: &loads,
			stores: &stores,
		};
		let mut session = RowSession::new(
			&server.identity,
			&server.identity_digest,
			LINEAGE,
			&mut transaction,
			SessionPhase::Message,
			None,
		);
		let failure = RowError::Storage("read failed".into());
		assert_eq!(
			session.load_application(b"request").err(),
			Some(failure.clone())
		);
		assert_eq!(
			session.load_application(b"again").err(),
			Some(failure.clone())
		);
		assert_eq!(
			session.store_application(b"write", b"blocked"),
			Err(failure.clone())
		);
		assert_eq!(
			session.encrypt_message(b"native", PEER_KID).err(),
			Some(failure.clone())
		);
		assert_eq!(session.finish(Ok(())), Err(failure));
		assert_eq!(loads.load(Ordering::SeqCst), 1);
		assert_eq!(stores.load(Ordering::SeqCst), 0);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn composed_receive_withholds_failed_output_and_recovers_only_the_committed_application_result()
	{
		use crate::ProviderBeacon;
		let mut server = server();
		let mut beacon = crate::Beacon::new(
			SERVER_KID,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let request = beacon.get_registration_bundle().unwrap();
		let response = server
			.register_beacon(&request, Some(b"registered"))
			.unwrap()
			.unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		let first = beacon.encrypt_message(b"delayed").unwrap();
		let second = beacon.encrypt_message(b"received").unwrap();
		let before = server.store.rows.clone();
		server.store.fail_commit = true;
		let failed = server.transaction(|session| {
			let transition = session.decrypt_message(&second.ciphertext)?;
			assert!(transition.changed);
			let message = transition.message.unwrap();
			assert_eq!(message.data(), b"received");
			session.store_application(b"receive receipt", message.data())?;
			// The pending native message retains its wiping buffer through the outer commit gate.
			Ok(message)
		});
		assert!(matches!(failed, Err(RowError::Storage(_))));
		assert_eq!(server.store.rows, before);
		server.store.fail_commit = false;
		let received = server
			.transaction(|session| {
				assert!(session.load_application(b"receive receipt")?.is_none());
				let transition = session.decrypt_message(&second.ciphertext)?;
				assert!(transition.changed);
				let message = transition.message.unwrap();
				assert_eq!(message.key_id(), PEER_KID);
				assert_eq!(message.sequence(), 2);
				session.store_application(b"receive receipt", message.data())?;
				Ok(message)
			})
			.unwrap();
		assert_eq!(received.data(), b"received");
		let committed = server.store.rows.clone();
		let cached = server
			.transaction(|session| {
				if let Some(receipt) = session.load_application(b"receive receipt")? {
					return Ok(receipt);
				}
				panic!("cached receipt must bypass the now-consumed receive key")
			})
			.unwrap();
		assert_eq!(cached.as_slice(), received.data());
		assert_eq!(server.store.rows, committed);
		let replay = server
			.transaction(|session| session.decrypt_message(&second.ciphertext))
			.unwrap();
		assert!(!replay.changed);
		assert!(replay.message.is_none());
		assert_eq!(server.store.rows, committed);
		let delayed = server
			.transaction(|session| session.decrypt_message(&first.ciphertext))
			.unwrap();
		assert!(delayed.changed);
		let delayed = delayed.message.unwrap();
		assert_eq!(delayed.data(), b"delayed");
		assert_eq!(delayed.sequence(), 1);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn composed_registration_commits_each_phase_and_returns_exact_cached_application_result() {
		use crate::ProviderBeacon;
		let mut server = server();
		let mut beacon = crate::Beacon::new(
			SERVER_KID,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let request = beacon.get_registration_bundle().unwrap();
		let transactions = server.store.transactions;
		let output = server
			.registration_transaction(
				|session| {
					assert!(session.load_application(b"registration")?.is_none());
					assert!(session.accept_registration(&request)?);
					session.store_application(b"registration", b"accepted/incomplete")?;
					Ok(RowRegistrationDecision::<_, RowMessage>::Continue(
						b"chosen session reference".to_vec(),
					))
				},
				|session, context| {
					assert_eq!(
						session
							.load_application(b"registration")?
							.unwrap()
							.as_slice(),
						b"accepted/incomplete"
					);
					let transition = session.complete_registration(Some(b"registered"))?;
					assert!(transition.changed);
					let message = transition.message.unwrap();
					assert_eq!(message.key_id(), PEER_KID);
					assert_eq!(message.sequence(), 1);
					session.store_application(b"session", &context)?;
					session.store_application(b"registration", message.data())?;
					Ok(message)
				},
			)
			.unwrap();
		assert_eq!(server.store.transactions, transactions + 2);
		assert_eq!(
			beacon.finish_registration(output.data()).unwrap(),
			b"registered"
		);
		let before = server.store.rows.clone();
		let cached = server
			.registration_transaction(
				|session| {
					assert_eq!(
						session.load_application(b"session")?.unwrap().as_slice(),
						b"chosen session reference"
					);
					Ok(RowRegistrationDecision::<(), _>::Return(
						session.load_application(b"registration")?.unwrap(),
					))
				},
				|_, ()| panic!("cached application result must not accept or complete again"),
			)
			.unwrap();
		assert_eq!(cached.as_slice(), output.data());
		assert_eq!(server.store.rows, before);
		assert_eq!(server.store.transactions, transactions + 3);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn acceptance_callback_failure_rolls_back_marker_and_does_not_release_a_pending_token() {
		let mut server = server();
		let request = registration(&server);
		let before = server.store.rows.clone();
		let failure = RowError::Storage("acceptance finalizer failed".into());
		let result = server.registration_transaction::<(), ()>(
			|session| {
				assert!(session.accept_registration(&request)?);
				session.store_application(b"request", b"incomplete")?;
				Err(failure.clone())
			},
			|_, _| panic!("uncommitted acceptance must not reach completion"),
		);
		assert_eq!(
			result,
			Err(RowRegistrationError {
				phase: RowRegistrationPhase::Acceptance,
				source: failure
			})
		);
		assert_eq!(server.store.rows, before);
		assert!(
			server
				.register_beacon(&request, Some(b"retry unaccepted request"))
				.unwrap()
				.is_some()
		);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn completion_callback_failure_retains_acceptance_but_rolls_back_peer_and_result() {
		let mut server = server();
		let request = registration(&server);
		let before = server.store.rows.clone();
		let failure = RowError::Storage("completion finalizer failed".into());
		let result = server.registration_transaction::<(), ()>(
			|session| {
				assert!(session.accept_registration(&request)?);
				session.store_application(b"request", b"incomplete")?;
				Ok(RowRegistrationDecision::Continue(()))
			},
			|session, ()| {
				let message = session
					.complete_registration(Some(b"withheld"))?
					.message
					.unwrap();
				session.store_application(b"request", message.data())?;
				session.store_application(b"session", b"must roll back")?;
				Err(failure.clone())
			},
		);
		let error = result.unwrap_err();
		assert_eq!(error.phase, RowRegistrationPhase::Completion);
		assert_eq!(error.source, failure);
		assert!(error.to_string().contains("completion finalizer failed"));
		assert!(Error::source(&error).is_some());
		assert_eq!(server.store.rows.len(), before.len() + 2);
		for (key, value) in before {
			assert_eq!(server.store.rows[&key], value);
		}
		server
			.transaction(|session| {
				assert_eq!(
					session.load_application(b"request")?.unwrap().as_slice(),
					b"incomplete"
				);
				assert!(session.load_application(b"session")?.is_none());
				Ok(())
			})
			.unwrap();
		assert!(server.register_beacon(&request, None).unwrap().is_none());
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn registration_continuation_requires_acceptance_and_completion_can_record_terminal_policy() {
		let mut server = server();
		let before = server.store.rows.clone();
		let result = server.registration_transaction::<(), ()>(
			|session| {
				session.store_application(b"invalid continuation", b"must roll back")?;
				assert!(!session.accept_registration(b"malformed")?);
				Ok(RowRegistrationDecision::Continue(()))
			},
			|_, _| panic!("there is no accepted pending token"),
		);
		assert_eq!(
			result,
			Err(RowRegistrationError {
				phase: RowRegistrationPhase::Acceptance,
				source: RowError::InvalidSession
			})
		);
		assert_eq!(server.store.rows, before);
		let request = registration(&server);
		let result = server
			.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					Ok(RowRegistrationDecision::Continue(()))
				},
				|session, ()| {
					session.store_application(b"request", b"revoked before completion")?;
					Ok("terminal policy result")
				},
			)
			.unwrap();
		assert_eq!(result, "terminal policy result");
		assert_eq!(server.store.rows.len(), before.len() + 2);
		for (key, value) in before {
			assert_eq!(server.store.rows[&key], value);
		}
		assert!(server.register_beacon(&request, None).unwrap().is_none());
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn unknown_registration_commit_is_resolved_from_application_receipts_without_reusing_tokens() {
		use crate::ProviderBeacon;
		struct UncertainStore {
			inner: TestStore,
			calls: usize,
			lose_acknowledgement: usize,
		}
		impl RowStore for UncertainStore {
			fn transaction(
				&mut self,
				operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
			) -> Result<(), RowError> {
				self.calls += 1;
				self.inner.transaction(operation)?;
				if self.calls == self.lose_acknowledgement {
					return Err(RowError::Storage("commit acknowledgement lost".into()));
				}
				Ok(())
			}
		}
		for (lose_acknowledgement, phase) in [
			(2, RowRegistrationPhase::Acceptance),
			(3, RowRegistrationPhase::Completion),
		] {
			let mut server = RowServer::create(
				SERVER_KID,
				Some(&[0x62; 32]),
				Some(&[0x63; 32]),
				UncertainStore {
					inner: TestStore::default(),
					calls: 0,
					lose_acknowledgement,
				},
				LINEAGE,
			)
			.unwrap();
			let mut beacon = crate::Beacon::new(
				SERVER_KID,
				server.identity_pk().as_bytes(),
				&server.mldsa_public_key(),
			);
			let request = beacon.get_registration_bundle().unwrap();
			let mut completed = false;
			let result = server.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					session.store_application(b"request", b"incomplete")?;
					Ok(RowRegistrationDecision::Continue(()))
				},
				|session, ()| {
					completed = true;
					let message = session
						.complete_registration(Some(b"registered"))?
						.message
						.unwrap();
					let mut response = Zeroizing::new(b"application response:".to_vec());
					response.extend_from_slice(message.data());
					session.store_application(b"session", &message.key_id().to_le_bytes())?;
					session.store_application(b"request", &response)?;
					Ok(response)
				},
			);
			assert_eq!(
				result.err(),
				Some(RowRegistrationError {
					phase,
					source: RowError::Storage("commit acknowledgement lost".into()),
				})
			);
			assert_eq!(completed, phase == RowRegistrationPhase::Completion);
			let committed = server.store.inner.rows.clone();
			let cached = server
				.registration_transaction(
					|session| {
						Ok(RowRegistrationDecision::<(), _>::Return(
							session.load_application(b"request")?.unwrap(),
						))
					},
					|_, ()| panic!("receipt lookup must not reconstruct a pending registration"),
				)
				.unwrap();
			if phase == RowRegistrationPhase::Acceptance {
				assert_eq!(cached.as_slice(), b"incomplete");
				assert!(!server.store.inner.rows.contains_key(&storage_key(
					LINEAGE,
					PEER,
					&PEER_KID.to_le_bytes()
				)));
			} else {
				assert_eq!(
					beacon
						.finish_registration(cached.strip_prefix(b"application response:").unwrap())
						.unwrap(),
					b"registered"
				);
			}
			assert_eq!(server.store.inner.rows, committed);
			assert!(server.register_beacon(&request, None).unwrap().is_none());
			assert_eq!(server.store.inner.rows, committed);
		}
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn response_construction_rejection_can_commit_an_application_terminal_result() {
		let mut server = server();
		let request = registration(&server);
		let before = server.store.rows.clone();
		let output = server
			.registration_transaction(
				|session| {
					assert!(session.accept_registration(&request)?);
					Ok(RowRegistrationDecision::Continue(()))
				},
				|session, ()| {
					let transition = session.complete_registration(Some(b""))?;
					assert!(!transition.changed);
					assert!(transition.message.is_none());
					session.store_application(b"request", b"terminal response failure")?;
					Ok("terminal response failure")
				},
			)
			.unwrap();
		assert_eq!(output, "terminal response failure");
		assert_eq!(server.store.rows.len(), before.len() + 2);
		for (key, value) in before {
			assert_eq!(server.store.rows[&key], value);
		}
		assert!(server.register_beacon(&request, None).unwrap().is_none());
	}
}
