// SPDX-License-Identifier: 0BSD

use std::{error::Error, fmt};

use libsodium_rs::{crypto_generichash, ensure_init, random};
use zeroize::Zeroizing;

use crate::server::{
	ProviderServer, ReceiveTransition, RecvState, RegResponse, RegistrationOutput, SendState,
	Server,
};
use crate::{Decrypted, Encrypted};

const SNAPSHOT_MAGIC: &[u8; 16] = b"beaconcrypt-snap";
const SNAPSHOT_VERSION: u16 = 2;
const SNAPSHOT_KIND_SERVER: u8 = 1;
const SNAPSHOT_RESERVED: u8 = 0;
const LINEAGE_SIZE: usize = 32;
const DIGEST_SIZE: usize = 32;
const HEADER_SIZE: usize = SNAPSHOT_MAGIC.len() + 2 + 1 + 1 + LINEAGE_SIZE + 8 + DIGEST_SIZE + 8;

/// Stable, non-secret identifier for one persistence lineage.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SnapshotLineage([u8; LINEAGE_SIZE]);

impl SnapshotLineage {
	fn generate() -> Self {
		let mut bytes = [0; LINEAGE_SIZE];
		random::fill_bytes(&mut bytes);
		Self(bytes)
	}

	pub const fn from_bytes(bytes: [u8; LINEAGE_SIZE]) -> Self {
		Self(bytes)
	}

	pub const fn as_bytes(&self) -> &[u8; LINEAGE_SIZE] {
		&self.0
	}
}

/// The value compared atomically by a [`SnapshotStore`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SnapshotHead {
	lineage: SnapshotLineage,
	generation: u64,
	digest: [u8; DIGEST_SIZE],
}

impl SnapshotHead {
	pub const fn lineage(self) -> SnapshotLineage {
		self.lineage
	}

	pub const fn generation(self) -> u64 {
		self.generation
	}

	pub const fn digest(self) -> [u8; DIGEST_SIZE] {
		self.digest
	}
}

/// Inert server-state bytes supplied by a trusted [`SnapshotStore`].
///
/// This type has no conversion to operational ratchet state. Activation is available only through
/// [`PersistentServer::restore`], which validates the canonical encoding and wins a store CAS first.
/// The envelope digest is an exact-byte identity for CAS and parent links, not an authenticator.
pub struct ServerSnapshot {
	bytes: Zeroizing<Vec<u8>>,
}

impl ServerSnapshot {
	pub fn from_bytes(bytes: Vec<u8>) -> Self {
		Self {
			bytes: Zeroizing::new(bytes),
		}
	}

	pub fn as_bytes(&self) -> &[u8] {
		self.bytes.as_slice()
	}

	pub fn head(&self) -> Result<SnapshotHead, PersistenceError> {
		let parsed = ParsedSnapshot::parse(self.as_bytes())?;
		Ok(SnapshotHead {
			lineage: parsed.lineage,
			generation: parsed.generation,
			digest: snapshot_digest(self.as_bytes())?,
		})
	}

	fn encode(
		server: &Server,
		lineage: SnapshotLineage,
		generation: u64,
		parent_digest: [u8; DIGEST_SIZE],
	) -> Result<Self, PersistenceError> {
		let payload = Zeroizing::new(server.serialize_state().ok_or(PersistenceError::Encoding)?);
		let payload_len = u64::try_from(payload.len()).map_err(|_| PersistenceError::Encoding)?;
		let capacity = HEADER_SIZE
			.checked_add(payload.len())
			.ok_or(PersistenceError::Encoding)?;
		let mut bytes = Zeroizing::new(Vec::with_capacity(capacity));
		bytes.extend_from_slice(SNAPSHOT_MAGIC);
		bytes.extend_from_slice(&SNAPSHOT_VERSION.to_le_bytes());
		bytes.push(SNAPSHOT_KIND_SERVER);
		bytes.push(SNAPSHOT_RESERVED);
		bytes.extend_from_slice(lineage.as_bytes());
		bytes.extend_from_slice(&generation.to_le_bytes());
		bytes.extend_from_slice(&parent_digest);
		bytes.extend_from_slice(&payload_len.to_le_bytes());
		bytes.extend_from_slice(payload.as_bytes());
		Ok(Self { bytes })
	}

	fn decode(&self) -> Result<(Server, SnapshotHead), PersistenceError> {
		let parsed = ParsedSnapshot::parse(self.as_bytes())?;
		let payload =
			std::str::from_utf8(parsed.payload).map_err(|_| PersistenceError::InvalidSnapshot)?;
		let server = Server::deserialize_state(payload).ok_or(PersistenceError::InvalidSnapshot)?;
		let canonical = Zeroizing::new(server.serialize_state().ok_or(PersistenceError::Encoding)?);
		if canonical.as_bytes() != parsed.payload {
			return Err(PersistenceError::NonCanonicalSnapshot);
		}

		Ok((server, self.head()?))
	}
}

struct ParsedSnapshot<'a> {
	lineage: SnapshotLineage,
	generation: u64,
	payload: &'a [u8],
}

impl<'a> ParsedSnapshot<'a> {
	fn parse(bytes: &'a [u8]) -> Result<Self, PersistenceError> {
		if bytes.len() < HEADER_SIZE || &bytes[..SNAPSHOT_MAGIC.len()] != SNAPSHOT_MAGIC {
			return Err(PersistenceError::InvalidSnapshot);
		}
		let mut offset = SNAPSHOT_MAGIC.len();
		let version = read_u16(bytes, &mut offset)?;
		if version != SNAPSHOT_VERSION
			|| take_byte(bytes, &mut offset)? != SNAPSHOT_KIND_SERVER
			|| take_byte(bytes, &mut offset)? != SNAPSHOT_RESERVED
		{
			return Err(PersistenceError::InvalidSnapshot);
		}
		let lineage = SnapshotLineage(take_array(bytes, &mut offset)?);
		let generation = read_u64(bytes, &mut offset)?;
		let parent_digest: [u8; DIGEST_SIZE] = take_array(bytes, &mut offset)?;
		if generation == 0 && parent_digest != [0; DIGEST_SIZE] {
			return Err(PersistenceError::InvalidSnapshot);
		}
		let payload_len = usize::try_from(read_u64(bytes, &mut offset)?)
			.map_err(|_| PersistenceError::InvalidSnapshot)?;
		if offset != HEADER_SIZE {
			return Err(PersistenceError::InvalidSnapshot);
		}
		let payload_end = offset
			.checked_add(payload_len)
			.ok_or(PersistenceError::InvalidSnapshot)?;
		if payload_end != bytes.len() {
			return Err(PersistenceError::InvalidSnapshot);
		}
		Ok(Self {
			lineage,
			generation,
			payload: &bytes[offset..payload_end],
		})
	}
}

fn take_byte(bytes: &[u8], offset: &mut usize) -> Result<u8, PersistenceError> {
	let value = *bytes
		.get(*offset)
		.ok_or(PersistenceError::InvalidSnapshot)?;
	*offset += 1;
	Ok(value)
}

fn take_array<const N: usize>(
	bytes: &[u8],
	offset: &mut usize,
) -> Result<[u8; N], PersistenceError> {
	let end = offset
		.checked_add(N)
		.ok_or(PersistenceError::InvalidSnapshot)?;
	let value = bytes
		.get(*offset..end)
		.ok_or(PersistenceError::InvalidSnapshot)?
		.try_into()
		.map_err(|_| PersistenceError::InvalidSnapshot)?;
	*offset = end;
	Ok(value)
}

fn read_u16(bytes: &[u8], offset: &mut usize) -> Result<u16, PersistenceError> {
	Ok(u16::from_le_bytes(take_array(bytes, offset)?))
}

fn read_u64(bytes: &[u8], offset: &mut usize) -> Result<u64, PersistenceError> {
	Ok(u64::from_le_bytes(take_array(bytes, offset)?))
}

fn snapshot_digest(bytes: &[u8]) -> Result<[u8; DIGEST_SIZE], PersistenceError> {
	let digest = crypto_generichash::generichash(bytes, None, DIGEST_SIZE)
		.map_err(|_| PersistenceError::Digest)?;
	digest.try_into().map_err(|_| PersistenceError::Digest)
}

/// Linearizable durable storage for one server lineage.
///
/// This store is the persistence trust anchor. `load` must return only the exact snapshot bytes
/// accepted for this lineage from a domain that protects their integrity and provenance. Neither
/// [`ServerSnapshot`] nor its unkeyed digest authenticates those bytes.
///
/// `compare_and_swap` must atomically compare the complete current [`SnapshotHead`] and durably
/// store the exact `replacement` bytes and new head before returning `true`. Implementations must
/// keep that trusted head in a rollback-resistant domain; canonical encoding and a digest do not
/// make an old generation fresh.
pub trait SnapshotStore {
	fn load(&self) -> Option<ServerSnapshot>;

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool;
}

/// In-memory checkpoint storage used by language bindings that cannot supply a Rust
/// [`SnapshotStore`] implementation.
///
/// Importing bytes into this store explicitly trusts them as the current authoritative state.
/// It provides in-process CAS fencing, but exporting its bytes is not a durable commit and cannot
/// detect rollback to an older exported checkpoint. Production Rust deployments that need crash
/// durability or multi-owner coordination must provide their own conforming [`SnapshotStore`].
#[derive(Default)]
#[cfg(any(feature = "cbinds", feature = "pybinds"))]
pub(crate) struct BindingSnapshotStore {
	snapshot: Option<Zeroizing<Vec<u8>>>,
	head: Option<SnapshotHead>,
}

#[cfg(any(feature = "cbinds", feature = "pybinds"))]
impl BindingSnapshotStore {
	pub(crate) fn from_bytes(bytes: Vec<u8>) -> Result<Self, PersistenceError> {
		let snapshot = ServerSnapshot::from_bytes(bytes);
		let head = snapshot.head()?;
		Ok(Self {
			snapshot: Some(Zeroizing::new(snapshot.as_bytes().to_vec())),
			head: Some(head),
		})
	}

	pub(crate) fn as_bytes(&self) -> Option<&[u8]> {
		self.snapshot.as_deref().map(Vec::as_slice)
	}
}

#[cfg(any(feature = "cbinds", feature = "pybinds"))]
impl SnapshotStore for BindingSnapshotStore {
	fn load(&self) -> Option<ServerSnapshot> {
		self.snapshot
			.as_ref()
			.map(|bytes| ServerSnapshot::from_bytes(bytes.as_slice().to_vec()))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		if self.head.as_ref() != expected {
			return false;
		}
		let Ok(replacement_head) = replacement.head() else {
			return false;
		};
		match expected {
			Some(previous)
				if replacement_head.lineage() != previous.lineage()
					|| previous.generation().checked_add(1)
						!= Some(replacement_head.generation()) =>
			{
				return false;
			}
			None if replacement_head.generation() != 0 => return false,
			_ => {}
		}
		self.snapshot = Some(Zeroizing::new(replacement.as_bytes().to_vec()));
		self.head = Some(replacement_head);
		true
	}
}

/// A server whose state-changing results are released only after durable CAS.
pub struct PersistentServer<S: SnapshotStore> {
	server: Server,
	store: S,
	head: SnapshotHead,
	poisoned: bool,
}

impl<S: SnapshotStore> PersistentServer<S> {
	pub fn create(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		store: S,
	) -> Result<Self, PersistenceError> {
		ensure_init().map_err(|_| PersistenceError::Initialization)?;
		Self::create_with_lineage(server_kid, id_seed, store, SnapshotLineage::generate())
	}

	/// Create a fresh server under an externally provisioned lineage identifier.
	///
	/// The caller must allocate each lineage to exactly one rollback-resistant store head. Reusing
	/// one identifier with independent stores creates independent trust domains and voids the
	/// single-lineage guarantee.
	pub fn create_with_lineage(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mut store: S,
		lineage: SnapshotLineage,
	) -> Result<Self, PersistenceError> {
		ensure_init().map_err(|_| PersistenceError::Initialization)?;
		let server = Server::new(server_kid, id_seed);
		let snapshot = ServerSnapshot::encode(&server, lineage, 0, [0; DIGEST_SIZE])?;
		if !store.compare_and_swap(None, &snapshot) {
			return Err(PersistenceError::StaleGeneration);
		}
		let head = snapshot.head()?;
		Ok(Self {
			server,
			store,
			head,
			poisoned: false,
		})
	}

	/// Validate and activate the current snapshot supplied by the trusted store.
	///
	/// Activation itself advances the generation by CAS, so two restorers of one head cannot both
	/// become live.
	pub fn restore(mut store: S) -> Result<Self, PersistenceError> {
		ensure_init().map_err(|_| PersistenceError::Initialization)?;
		let snapshot = store.load().ok_or(PersistenceError::MissingSnapshot)?;
		let (server, stored_head) = snapshot.decode()?;
		let generation = stored_head
			.generation
			.checked_add(1)
			.ok_or(PersistenceError::GenerationExhausted)?;
		let activated =
			ServerSnapshot::encode(&server, stored_head.lineage, generation, stored_head.digest)?;
		if !store.compare_and_swap(Some(&stored_head), &activated) {
			return Err(PersistenceError::StaleGeneration);
		}
		let head = activated.head()?;
		Ok(Self {
			server,
			store,
			head,
			poisoned: false,
		})
	}

	pub const fn head(&self) -> SnapshotHead {
		self.head
	}

	pub const fn is_poisoned(&self) -> bool {
		self.poisoned
	}

	pub fn identity_pk(&self) -> &libsodium_rs::crypto_sign::PublicKey {
		self.server.identity_pk()
	}

	pub fn identity_key_kid(&self) -> u64 {
		self.server.identity_key_kid()
	}

	pub fn server_kid(&self) -> u64 {
		self.server.server_kid()
	}

	pub fn pk_by_kid(&self, kid: u64) -> Option<&libsodium_rs::crypto_sign::PublicKey> {
		self.server.pk_by_kid(kid)
	}

	pub fn ratchet_status(&self, kid: u64) -> Option<crate::RatchetStatus> {
		self.server.ratchet_status(kid)
	}

	pub fn get_shared_secret(
		&mut self,
		buffer: &[u8],
	) -> Result<Option<RegistrationOutput>, PersistenceError> {
		self.commit(|server| server.get_shared_secret(buffer))
	}

	pub fn build_registration_response(
		&mut self,
		registration: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Result<Option<RegResponse>, PersistenceError> {
		self.commit(|server| server.build_registration_response(registration, data))
	}

	pub fn encrypt_message(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<Encrypted>, PersistenceError> {
		self.commit(|server| server.encrypt_message(bytes, kid))
	}

	pub fn decrypt_message(&mut self, bytes: &[u8]) -> Result<Option<Decrypted>, PersistenceError> {
		Ok(self
			.commit_receive(|server| server.decrypt_message_transition(bytes))?
			.into_option())
	}

	pub fn encrypt_and_update(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<SendState>, PersistenceError> {
		self.commit(|server| server.encrypt_and_update(bytes, kid))
	}

	pub fn decrypt_and_update(
		&mut self,
		bytes: &[u8],
	) -> Result<Option<RecvState>, PersistenceError> {
		self.receive_and_project(bytes, |server, decrypted| {
			server.try_receive_update(decrypted)
		})
	}

	pub fn encrypt_and_update_json(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<String>, PersistenceError> {
		self.commit(|server| server.encrypt_and_update_json(bytes, kid))
	}

	pub fn decrypt_and_update_json(
		&mut self,
		bytes: &[u8],
	) -> Result<Option<String>, PersistenceError> {
		self.receive_and_project(bytes, |server, decrypted| {
			server
				.try_receive_update(decrypted)
				.and_then(|update| update.try_render_json())
		})
	}

	fn receive_and_project<T, E>(
		&mut self,
		bytes: &[u8],
		project: impl FnOnce(&Server, Decrypted) -> Result<T, E>,
	) -> Result<Option<T>, PersistenceError> {
		// Commit the authoritative receive effect before constructing any caller-visible update.
		let transition = self.commit_receive(|server| server.decrypt_message_transition(bytes))?;
		Self::project_receive_output(transition, |decrypted| project(&self.server, decrypted))
	}

	fn project_receive_output<T, U, E>(
		transition: ReceiveTransition<T>,
		project: impl FnOnce(T) -> Result<U, E>,
	) -> Result<Option<U>, PersistenceError> {
		match transition {
			ReceiveTransition::Rejected => Ok(None),
			ReceiveTransition::Accepted(output) => project(output)
				.map(Some)
				.map_err(|_| PersistenceError::OutputEncoding),
		}
	}

	fn commit_receive<T>(
		&mut self,
		operation: impl FnOnce(&mut Server) -> ReceiveTransition<T>,
	) -> Result<ReceiveTransition<T>, PersistenceError> {
		if self.poisoned {
			return Err(PersistenceError::Poisoned);
		}
		self.poisoned = true;
		let output = match operation(&mut self.server) {
			ReceiveTransition::Rejected => {
				// Rejection is an exact-state transition, so it creates no snapshot generation.
				self.poisoned = false;
				return Ok(ReceiveTransition::Rejected);
			}
			ReceiveTransition::Accepted(output) => output,
		};
		let generation = self
			.head
			.generation
			.checked_add(1)
			.ok_or(PersistenceError::GenerationExhausted)?;
		let snapshot = ServerSnapshot::encode(
			&self.server,
			self.head.lineage,
			generation,
			self.head.digest,
		)?;
		let successor_head = snapshot.head()?;
		if !self.store.compare_and_swap(Some(&self.head), &snapshot) {
			return Err(PersistenceError::StaleGeneration);
		}
		self.head = successor_head;
		self.poisoned = false;
		Ok(ReceiveTransition::Accepted(output))
	}

	fn commit<T>(
		&mut self,
		operation: impl FnOnce(&mut Server) -> T,
	) -> Result<T, PersistenceError> {
		if self.poisoned {
			return Err(PersistenceError::Poisoned);
		}
		self.poisoned = true;
		let output = operation(&mut self.server);
		let generation = self
			.head
			.generation
			.checked_add(1)
			.ok_or(PersistenceError::GenerationExhausted)?;
		let snapshot = ServerSnapshot::encode(
			&self.server,
			self.head.lineage,
			generation,
			self.head.digest,
		)?;
		let successor_head = snapshot.head()?;
		if !self.store.compare_and_swap(Some(&self.head), &snapshot) {
			return Err(PersistenceError::StaleGeneration);
		}
		self.head = successor_head;
		self.poisoned = false;
		Ok(output)
	}
}

#[cfg(any(feature = "cbinds", feature = "pybinds"))]
pub(crate) type BindingServer = PersistentServer<BindingSnapshotStore>;

#[cfg(any(feature = "cbinds", feature = "pybinds"))]
impl PersistentServer<BindingSnapshotStore> {
	pub(crate) fn create_binding(
		server_kid: u64,
		id_seed: Option<&[u8]>,
	) -> Result<Self, PersistenceError> {
		Self::create(server_kid, id_seed, BindingSnapshotStore::default())
	}

	pub(crate) fn restore_binding(bytes: Vec<u8>) -> Result<Self, PersistenceError> {
		Self::restore(BindingSnapshotStore::from_bytes(bytes)?)
	}

	pub(crate) fn export_binding_state(&self) -> Result<Vec<u8>, PersistenceError> {
		self.store
			.as_bytes()
			.map(<[u8]>::to_vec)
			.ok_or(PersistenceError::MissingSnapshot)
	}
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PersistenceError {
	MissingSnapshot,
	InvalidSnapshot,
	NonCanonicalSnapshot,
	StaleGeneration,
	GenerationExhausted,
	Encoding,
	OutputEncoding,
	Initialization,
	Digest,
	Poisoned,
}

impl fmt::Display for PersistenceError {
	fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
		let message = match self {
			Self::MissingSnapshot => "snapshot store is empty",
			Self::InvalidSnapshot => "invalid server snapshot",
			Self::NonCanonicalSnapshot => "non-canonical server snapshot payload",
			Self::StaleGeneration => "snapshot generation compare-and-swap failed",
			Self::GenerationExhausted => "snapshot generation exhausted",
			Self::Encoding => "server snapshot encoding failed",
			Self::OutputEncoding => "receive output encoding failed after commit",
			Self::Initialization => "failed to initialize snapshot dependencies",
			Self::Digest => "failed to compute snapshot identity digest",
			Self::Poisoned => "persistent server is poisoned after a failed commit",
		};
		formatter.write_str(message)
	}
}

impl Error for PersistenceError {}

#[cfg(test)]
mod tests {
	use super::*;
	#[cfg(feature = "beacon")]
	use crate::ratchet::RATCHET_MAX_GAP;
	#[cfg(feature = "beacon")]
	use crate::{Beacon, ProviderBeacon};

	#[derive(Default)]
	struct MemoryStore {
		snapshot: Option<Vec<u8>>,
		head: Option<SnapshotHead>,
	}

	impl SnapshotStore for MemoryStore {
		fn load(&self) -> Option<ServerSnapshot> {
			self.snapshot
				.as_ref()
				.map(|bytes| ServerSnapshot::from_bytes(bytes.clone()))
		}

		fn compare_and_swap(
			&mut self,
			expected: Option<&SnapshotHead>,
			replacement: &ServerSnapshot,
		) -> bool {
			if self.head.as_ref() != expected {
				return false;
			}
			let Ok(replacement_head) = replacement.head() else {
				return false;
			};
			match expected {
				Some(previous)
					if replacement_head.lineage() != previous.lineage()
						|| previous.generation().checked_add(1)
							!= Some(replacement_head.generation()) =>
				{
					return false;
				}
				None if replacement_head.generation() != 0 => return false,
				_ => {}
			}
			self.snapshot = Some(replacement.as_bytes().to_vec());
			self.head = Some(replacement_head);
			true
		}
	}

	fn deterministic_persistent_server() -> PersistentServer<MemoryStore> {
		PersistentServer::create_with_lineage(
			7,
			Some(&[0x71; libsodium_rs::crypto_sign::SEEDBYTES]),
			MemoryStore::default(),
			SnapshotLineage::from_bytes([0x72; LINEAGE_SIZE]),
		)
		.unwrap()
	}

	#[test]
	fn snapshot_head_rejects_short_envelopes_and_accepts_an_empty_payload() {
		for length in 0..HEADER_SIZE {
			assert!(matches!(
				ServerSnapshot::from_bytes(vec![0; length]).head(),
				Err(PersistenceError::InvalidSnapshot)
			));
		}

		let persistent = deterministic_persistent_server();
		let PersistentServer { store, .. } = persistent;
		let mut bytes = store.snapshot.unwrap();
		bytes.truncate(HEADER_SIZE);
		bytes[HEADER_SIZE - 8..HEADER_SIZE].copy_from_slice(&0u64.to_le_bytes());
		assert!(ServerSnapshot::from_bytes(bytes).head().is_ok());
	}

	#[test]
	fn snapshot_head_contains_a_real_content_digest() {
		let persistent = deterministic_persistent_server();
		assert_ne!(persistent.head().digest(), [0; DIGEST_SIZE]);
		assert_ne!(persistent.head().digest(), [1; DIGEST_SIZE]);
	}

	#[test]
	fn fresh_persistent_server_reports_its_configuration() {
		let persistent = deterministic_persistent_server();
		assert!(!persistent.is_poisoned());
		assert_eq!(persistent.server_kid(), 7);
	}

	#[test]
	fn persistence_errors_have_stable_messages() {
		let cases = [
			(PersistenceError::MissingSnapshot, "snapshot store is empty"),
			(PersistenceError::InvalidSnapshot, "invalid server snapshot"),
			(
				PersistenceError::NonCanonicalSnapshot,
				"non-canonical server snapshot payload",
			),
			(
				PersistenceError::StaleGeneration,
				"snapshot generation compare-and-swap failed",
			),
			(
				PersistenceError::GenerationExhausted,
				"snapshot generation exhausted",
			),
			(
				PersistenceError::Encoding,
				"server snapshot encoding failed",
			),
			(
				PersistenceError::OutputEncoding,
				"receive output encoding failed after commit",
			),
			(
				PersistenceError::Initialization,
				"failed to initialize snapshot dependencies",
			),
			(
				PersistenceError::Digest,
				"failed to compute snapshot identity digest",
			),
			(
				PersistenceError::Poisoned,
				"persistent server is poisoned after a failed commit",
			),
		];
		for (error, expected) in cases {
			assert_eq!(error.to_string(), expected);
		}
	}

	#[test]
	fn changed_state_is_committed_even_when_the_operation_returns_none() {
		let mut persistent = PersistentServer::create_with_lineage(
			7,
			Some(&[0x71; libsodium_rs::crypto_sign::SEEDBYTES]),
			MemoryStore::default(),
			SnapshotLineage::from_bytes([0x72; LINEAGE_SIZE]),
		)
		.unwrap();
		let previous = persistent.head();

		let output = persistent
			.commit(|server| {
				server.set_identity_kid(6);
				None::<()>
			})
			.unwrap();
		assert!(output.is_none());
		assert_eq!(persistent.head.generation(), previous.generation() + 1);

		let PersistentServer { store, .. } = persistent;
		let restored = PersistentServer::restore(store).unwrap();
		assert_eq!(restored.identity_key_kid(), 6);
	}

	#[test]
	fn panicking_operation_leaves_the_live_owner_poisoned() {
		let mut persistent = PersistentServer::create_with_lineage(
			7,
			Some(&[0x73; libsodium_rs::crypto_sign::SEEDBYTES]),
			MemoryStore::default(),
			SnapshotLineage::from_bytes([0x74; LINEAGE_SIZE]),
		)
		.unwrap();
		let committed_head = persistent.head();

		let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			persistent.commit::<()>(|server| {
				server.set_identity_kid(6);
				panic!("injected operation panic");
			})
		}));
		assert!(panic.is_err());
		assert!(persistent.is_poisoned());
		assert_eq!(persistent.head(), committed_head);
		assert!(matches!(
			persistent.commit(|_| ()),
			Err(PersistenceError::Poisoned)
		));
	}

	#[test]
	fn rejected_receive_needs_no_successor_generation_and_clears_poison() {
		let mut persistent = deterministic_persistent_server();
		persistent.head.generation = u64::MAX;
		let entry_head = persistent.head();

		let transition = persistent
			.commit_receive(|_| ReceiveTransition::<()>::Rejected)
			.unwrap();
		assert!(matches!(transition, ReceiveTransition::Rejected));
		assert_eq!(persistent.head(), entry_head);
		assert!(!persistent.is_poisoned());
	}

	#[test]
	fn panicking_receive_operation_leaves_the_live_owner_poisoned() {
		let mut persistent = deterministic_persistent_server();
		let committed_head = persistent.head();

		let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
			persistent.commit_receive::<()>(|_| panic!("injected receive panic"))
		}));
		assert!(panic.is_err());
		assert!(persistent.is_poisoned());
		assert_eq!(persistent.head(), committed_head);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn rejected_future_receive_preserves_complete_live_server_and_snapshot() {
		let mut persistent = deterministic_persistent_server();
		let mut beacon = Beacon::new(persistent.server_kid(), persistent.identity_pk().as_bytes());
		let phase_1 = beacon.get_registration_bundle().unwrap();
		let registration = persistent.get_shared_secret(&phase_1).unwrap().unwrap();
		let response = persistent
			.build_registration_response(registration, Some(b"registration"))
			.unwrap()
			.unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		let _first = beacon.encrypt_message(b"first").unwrap();
		let _second = beacon.encrypt_message(b"second").unwrap();
		let third = beacon.encrypt_message(b"third").unwrap();

		let message = capnp::serialize::read_message(
			third.ciphertext.as_slice(),
			capnp::message::ReaderOptions::new(),
		)
		.unwrap();
		let typed =
			capnp::message::TypedReader::<_, crate::cryptoframe_capnp::crypto_frame::Owned>::new(
				message,
			);
		let frame = typed.get().unwrap();
		let mut ciphertext = frame.get_cipher_text().unwrap().to_vec();
		ciphertext[0] ^= 1;
		let mut message = capnp::message::TypedBuilder::<
			crate::cryptoframe_capnp::crypto_frame::Owned,
		>::new_default();
		let mut corrupted = message.init_root();
		corrupted.set_seq(frame.get_seq());
		corrupted.set_key_id(frame.get_key_id());
		corrupted.set_cipher_text(&ciphertext);
		let mut rejected = Vec::new();
		capnp::serialize::write_message(&mut rejected, message.borrow_inner()).unwrap();

		let live = persistent.server.serialize_state().unwrap();
		let head = persistent.head();
		let snapshot = persistent.store.snapshot.clone();
		assert!(persistent.decrypt_message(&rejected).unwrap().is_none());
		assert_eq!(persistent.server.serialize_state().unwrap(), live);
		assert_eq!(persistent.head(), head);
		assert_eq!(persistent.store.snapshot, snapshot);
		assert!(!persistent.is_poisoned());
		assert_eq!(
			persistent
				.decrypt_message(&third)
				.unwrap()
				.unwrap()
				.plaintext,
			b"third"
		);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn full_legacy_v2_receive_cache_restores_and_makes_forward_progress() {
		let mut persistent = deterministic_persistent_server();
		let mut beacon = Beacon::new(persistent.server_kid(), persistent.identity_pk().as_bytes());
		let phase_1 = beacon.get_registration_bundle().unwrap();
		let registration = persistent.get_shared_secret(&phase_1).unwrap().unwrap();
		let response = persistent
			.build_registration_response(registration, Some(b"registration"))
			.unwrap()
			.unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		let frames = (1..=RATCHET_MAX_GAP + 1)
			.map(|sequence| {
				let plaintext = format!("legacy cached message {sequence}").into_bytes();
				let frame = beacon.encrypt_message(&plaintext).unwrap();
				assert_eq!(frame.seq, sequence);
				(plaintext, frame)
			})
			.collect::<Vec<_>>();

		assert_eq!(
			persistent
				.commit(|server| server.ratchet_recv_until(RATCHET_MAX_GAP, response.kid))
				.unwrap(),
			Some(RATCHET_MAX_GAP)
		);
		assert_eq!(
			persistent
				.ratchet_status(response.kid)
				.unwrap()
				.receive_cache_len(),
			RATCHET_MAX_GAP as u8
		);
		let snapshot = persistent.store.snapshot.as_ref().unwrap();
		assert_eq!(
			u16::from_le_bytes(
				snapshot[SNAPSHOT_MAGIC.len()..SNAPSHOT_MAGIC.len() + 2]
					.try_into()
					.unwrap()
			),
			SNAPSHOT_VERSION
		);

		let PersistentServer { store, .. } = persistent;
		let mut restored = PersistentServer::restore(store).unwrap();
		let full_state = restored.head();
		let full_snapshot = restored.store.snapshot.clone();
		let target = &frames[RATCHET_MAX_GAP as usize - 1].1;
		let message = capnp::serialize::read_message(
			target.ciphertext.as_slice(),
			capnp::message::ReaderOptions::new(),
		)
		.unwrap();
		let typed =
			capnp::message::TypedReader::<_, crate::cryptoframe_capnp::crypto_frame::Owned>::new(
				message,
			);
		let frame = typed.get().unwrap();
		let mut ciphertext = frame.get_cipher_text().unwrap().to_vec();
		ciphertext[0] ^= 1;
		let mut message = capnp::message::TypedBuilder::<
			crate::cryptoframe_capnp::crypto_frame::Owned,
		>::new_default();
		let mut corrupted = message.init_root();
		corrupted.set_seq(frame.get_seq());
		corrupted.set_key_id(frame.get_key_id());
		corrupted.set_cipher_text(&ciphertext);
		let mut rejected = Vec::new();
		capnp::serialize::write_message(&mut rejected, message.borrow_inner()).unwrap();

		assert!(restored.decrypt_message(&rejected).unwrap().is_none());
		assert_eq!(restored.head(), full_state);
		assert_eq!(restored.store.snapshot, full_snapshot);
		assert_eq!(
			restored
				.ratchet_status(response.kid)
				.unwrap()
				.receive_cache_len(),
			RATCHET_MAX_GAP as u8
		);
		assert!(
			restored
				.decrypt_message(&frames[RATCHET_MAX_GAP as usize].1)
				.unwrap()
				.is_none()
		);
		assert_eq!(restored.head(), full_state);

		let cached = &frames[RATCHET_MAX_GAP as usize - 1];
		assert_eq!(
			restored
				.decrypt_message(&cached.1)
				.unwrap()
				.unwrap()
				.plaintext,
			cached.0
		);
		let future = &frames[RATCHET_MAX_GAP as usize];
		assert_eq!(
			restored
				.decrypt_message(&future.1)
				.unwrap()
				.unwrap()
				.plaintext,
			future.0
		);
	}

	#[cfg(feature = "beacon")]
	#[test]
	fn post_commit_output_failures_do_not_poison_or_undo_receives() {
		let mut persistent = deterministic_persistent_server();
		let mut beacon = Beacon::new(persistent.server_kid(), persistent.identity_pk().as_bytes());
		let phase_1 = beacon.get_registration_bundle().unwrap();
		let registration = persistent.get_shared_secret(&phase_1).unwrap().unwrap();
		let response = persistent
			.build_registration_response(registration, Some(b"registration"))
			.unwrap()
			.unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		let update_frame = beacon.encrypt_message(b"update durably consumed").unwrap();
		let json_frame = beacon.encrypt_message(b"JSON durably consumed").unwrap();
		let previous = persistent.head();

		let projected: Result<Option<()>, PersistenceError> =
			persistent.receive_and_project(&update_frame, |_, _| {
				Err(<serde_json::Error as serde::ser::Error>::custom(
					"injected update capture failure",
				))
			});
		assert_eq!(projected, Err(PersistenceError::OutputEncoding));
		assert_eq!(persistent.head().generation(), previous.generation() + 1);
		assert!(!persistent.is_poisoned());
		let update_committed = persistent.head();
		assert!(persistent.decrypt_message(&update_frame).unwrap().is_none());
		assert_eq!(persistent.head(), update_committed);

		let projected: Result<Option<()>, PersistenceError> =
			persistent.receive_and_project(&json_frame, |server, decrypted| {
				let _update = server.try_receive_update(decrypted)?;
				Err(<serde_json::Error as serde::ser::Error>::custom(
					"injected JSON rendering failure",
				))
			});
		assert_eq!(projected, Err(PersistenceError::OutputEncoding));
		assert_eq!(
			persistent.head().generation(),
			update_committed.generation() + 1
		);
		assert!(!persistent.is_poisoned());
		let committed = persistent.head();
		assert!(persistent.decrypt_message(&json_frame).unwrap().is_none());
		assert_eq!(persistent.head(), committed);
		assert!(!persistent.is_poisoned());

		let PersistentServer { store, .. } = persistent;
		let mut restored = PersistentServer::restore(store).unwrap();
		let restored_head = restored.head();
		assert!(restored.decrypt_message(&update_frame).unwrap().is_none());
		assert!(restored.decrypt_message(&json_frame).unwrap().is_none());
		assert_eq!(restored.head(), restored_head);
		assert!(!restored.is_poisoned());
	}
}
