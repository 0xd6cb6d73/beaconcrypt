use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::crypto_sign;
use std::sync::{Arc, Barrier, Mutex};
use std::thread;

const SNAPSHOT_HEADER_SIZE: usize = 16 + 2 + 1 + 1 + 32 + 8 + 32 + 8;
const SNAPSHOT_PARENT_DIGEST_OFFSET: usize = 16 + 2 + 1 + 1 + 32 + 8;
const SNAPSHOT_PAYLOAD_LENGTH_OFFSET: usize = SNAPSHOT_HEADER_SIZE - 8;

#[derive(Default)]
struct MemoryStoreState {
	snapshot: Option<Vec<u8>>,
	trusted_head: Option<SnapshotHead>,
	cas_attempts: usize,
	fail_next_cas: bool,
}

#[derive(Clone, Default)]
struct MemoryStore {
	state: Arc<Mutex<MemoryStoreState>>,
	load_override: Option<Arc<Vec<u8>>>,
	load_barrier: Option<Arc<Barrier>>,
}

impl MemoryStore {
	fn from_snapshot(bytes: Vec<u8>) -> Self {
		let head = ServerSnapshot::from_bytes(bytes.clone()).head().unwrap();
		Self {
			state: Arc::new(Mutex::new(MemoryStoreState {
				snapshot: Some(bytes),
				trusted_head: Some(head),
				cas_attempts: 0,
				fail_next_cas: false,
			})),
			load_override: None,
			load_barrier: None,
		}
	}

	fn with_load_override(mut self, bytes: Vec<u8>) -> Self {
		self.load_override = Some(Arc::new(bytes));
		self
	}

	fn with_load_barrier(mut self, barrier: Arc<Barrier>) -> Self {
		self.load_barrier = Some(barrier);
		self
	}

	fn snapshot_bytes(&self) -> Vec<u8> {
		self.state.lock().unwrap().snapshot.clone().unwrap()
	}

	fn trusted_head(&self) -> Option<SnapshotHead> {
		self.state.lock().unwrap().trusted_head
	}

	fn cas_attempts(&self) -> usize {
		self.state.lock().unwrap().cas_attempts
	}

	fn fail_next_cas(&self) {
		self.state.lock().unwrap().fail_next_cas = true;
	}
}

impl SnapshotStore for MemoryStore {
	fn load(&self) -> Option<ServerSnapshot> {
		let bytes = self
			.load_override
			.as_deref()
			.map(|bytes| bytes.as_slice().to_vec())
			.or_else(|| self.state.lock().unwrap().snapshot.clone());
		if let Some(barrier) = &self.load_barrier {
			barrier.wait();
		}
		bytes.map(ServerSnapshot::from_bytes)
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let replacement_head = match replacement.head() {
			Ok(head) => head,
			Err(_) => return false,
		};
		let mut state = self.state.lock().unwrap();
		state.cas_attempts += 1;
		if std::mem::take(&mut state.fail_next_cas) || state.trusted_head.as_ref() != expected {
			return false;
		}
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
		state.snapshot = Some(replacement.as_bytes().to_vec());
		state.trusted_head = Some(replacement_head);
		true
	}
}

fn test_register_pqxdh_beacon(server: &mut Server, beacon: &mut Beacon) -> Vec<u8> {
	let message = [0xFFu8; 32];
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let registration = server.get_shared_secret(&phase_1).unwrap();
	let response = server
		.build_registration_response(registration, Some(&message))
		.unwrap();
	beacon.finish_registration(&response.serialized).unwrap()
}

fn test_register_persistent(
	server: &mut PersistentServer<MemoryStore>,
	beacon: &mut Beacon,
) -> u64 {
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let registration = server.get_shared_secret(&phase_1).unwrap().unwrap();
	let response = server
		.build_registration_response(registration, Some(b"registration"))
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		b"registration"
	);
	response.kid
}

fn snapshot_with_payload(snapshot: &[u8], payload: &[u8]) -> Vec<u8> {
	assert!(snapshot.len() >= SNAPSHOT_HEADER_SIZE);
	let mut bytes = snapshot[..SNAPSHOT_HEADER_SIZE].to_vec();
	bytes[SNAPSHOT_PAYLOAD_LENGTH_OFFSET..SNAPSHOT_HEADER_SIZE]
		.copy_from_slice(&(payload.len() as u64).to_le_bytes());
	bytes.extend_from_slice(payload);
	bytes
}

fn corrupt_crypto_frame_ciphertext(serialized: &[u8]) -> Vec<u8> {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	let frame = typed.get().unwrap();
	let mut ciphertext = frame.get_cipher_text().unwrap().to_vec();
	ciphertext[0] ^= 1;

	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut corrupted = message.init_root();
	corrupted.set_seq(frame.get_seq());
	corrupted.set_key_id(frame.get_key_id());
	corrupted.set_cipher_text(&ciphertext);
	let mut serialized = Vec::new();
	capnp::serialize::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

#[test]
fn server_from_seed() {
	let empty = [0u8; ED25519_SEED_SIZE];
	let seeded = crypto_sign::KeyPair::from_seed(&empty).unwrap();
	let server = Server::new(0, Some(&empty));
	assert_eq!(
		seeded.secret_key.as_bytes(),
		server.identity_sk().as_bytes()
	);
	assert_eq!(
		seeded.public_key.as_bytes(),
		server.identity_pk().as_bytes()
	);
}

#[test]
fn server_can_register_multiple() {
	let mut server = Server::new(0, None);
	let server_id = server.identity_pk().to_owned();
	let mut first = Beacon::new(0, server_id.as_bytes());
	let first_message = test_register_pqxdh_beacon(&mut server, &mut first);
	let mut second = Beacon::new(0, server_id.as_bytes());
	let second_message = test_register_pqxdh_beacon(&mut server, &mut second);
	assert_eq!(first_message, second_message);
}

#[test]
fn snapshots_are_plain_canonical_v2_envelopes_without_a_trailing_tag() {
	let store = MemoryStore::default();
	let server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x31; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x42; 32]),
	)
	.unwrap();
	let original_head = server.head();
	let original_identity = server.identity_pk().clone();
	let bytes = store.snapshot_bytes();
	assert_eq!(u16::from_le_bytes(bytes[16..18].try_into().unwrap()), 2);
	let payload_len = u64::from_le_bytes(
		bytes[SNAPSHOT_PAYLOAD_LENGTH_OFFSET..SNAPSHOT_HEADER_SIZE]
			.try_into()
			.unwrap(),
	) as usize;
	assert_eq!(bytes.len(), SNAPSHOT_HEADER_SIZE + payload_len);
	let payload = std::str::from_utf8(&bytes[SNAPSHOT_HEADER_SIZE..]).unwrap();
	let payload_json: serde_json::Value = serde_json::from_str(payload).unwrap();
	assert!(payload_json.get("identity_key").is_some());
	assert!(payload_json.get("known_ids").is_some());
	assert!(payload_json.get("consumed_registrations").is_some());
	let mut legacy_v1 = bytes.clone();
	legacy_v1[16..18].copy_from_slice(&1u16.to_le_bytes());
	assert!(matches!(
		ServerSnapshot::from_bytes(legacy_v1).head(),
		Err(PersistenceError::InvalidSnapshot)
	));
	assert_eq!(store.cas_attempts(), 1);
	assert_eq!(store.trusted_head(), Some(original_head));

	let restored = PersistentServer::restore(store.clone()).unwrap();
	assert_eq!(restored.identity_pk(), &original_identity);
	assert_eq!(restored.head().lineage(), original_head.lineage());
	assert_eq!(restored.head().generation(), 1);
	let activated = store.snapshot_bytes();
	assert_eq!(
		&activated[SNAPSHOT_PARENT_DIGEST_OFFSET..SNAPSHOT_PARENT_DIGEST_OFFSET + 32],
		original_head.digest().as_slice()
	);
}

#[test]
fn trusted_snapshots_must_use_the_canonical_payload_encoding() {
	let store = MemoryStore::default();
	let _server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x37; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x43; 32]),
	)
	.unwrap();
	let canonical = store.snapshot_bytes();
	let payload_len = u64::from_le_bytes(
		canonical[SNAPSHOT_PAYLOAD_LENGTH_OFFSET..SNAPSHOT_HEADER_SIZE]
			.try_into()
			.unwrap(),
	) as usize;
	let payload = &canonical[SNAPSHOT_HEADER_SIZE..SNAPSHOT_HEADER_SIZE + payload_len];

	let mut noncanonical_payload = payload.to_vec();
	noncanonical_payload.push(b' ');
	let noncanonical = snapshot_with_payload(&canonical, &noncanonical_payload);
	assert!(matches!(
		PersistentServer::restore(MemoryStore::from_snapshot(noncanonical)),
		Err(PersistenceError::NonCanonicalSnapshot)
	));

	let mut malformed_payload = payload.to_vec();
	malformed_payload[0] = b'[';
	let malformed = snapshot_with_payload(&canonical, &malformed_payload);
	assert!(matches!(
		PersistentServer::restore(MemoryStore::from_snapshot(malformed)),
		Err(PersistenceError::InvalidSnapshot)
	));
}

#[test]
fn persistent_restore_preserves_cached_receive_keys_and_continues_the_session() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x3D; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x48; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
	let kid = test_register_persistent(&mut server, &mut beacon);
	let first = beacon.encrypt_message(b"first").unwrap();
	let second = beacon.encrypt_message(b"second").unwrap();
	let third = beacon.encrypt_message(b"third").unwrap();
	assert_eq!(
		server.decrypt_message(&third).unwrap().unwrap().plaintext,
		b"third"
	);
	assert_eq!(server.ratchet_status(kid).unwrap().receive_cache_len(), 2);
	drop(server);

	let mut restored = PersistentServer::restore(store).unwrap();
	assert_eq!(
		restored.decrypt_message(&first).unwrap().unwrap().plaintext,
		b"first"
	);
	assert_eq!(
		restored
			.decrypt_message(&second)
			.unwrap()
			.unwrap()
			.plaintext,
		b"second"
	);
	let reply = restored
		.encrypt_message(b"after restore", kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.decrypt_message(&reply).unwrap().plaintext,
		b"after restore"
	);
}

#[test]
fn failed_future_receive_advancement_is_committed_and_restored() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x3F; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x4A; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
	let kid = test_register_persistent(&mut server, &mut beacon);
	let first = beacon.encrypt_message(b"first").unwrap();
	let second = beacon.encrypt_message(b"second").unwrap();
	let third = beacon.encrypt_message(b"third").unwrap();
	assert_eq!(third.seq, 3);
	let corrupted_third = corrupt_crypto_frame_ciphertext(&third);
	let before_failure = server.head();
	assert_eq!(server.ratchet_status(kid).unwrap().receive_sequence(), 0);

	assert!(server.decrypt_message(&corrupted_third).unwrap().is_none());
	assert_eq!(server.head().generation(), before_failure.generation() + 1);
	let retained = server.ratchet_status(kid).unwrap();
	assert_eq!(retained.receive_sequence(), third.seq);
	assert_eq!(retained.receive_cache_len(), 3);
	drop(server);

	let mut restored = PersistentServer::restore(store).unwrap();
	let restored_status = restored.ratchet_status(kid).unwrap();
	assert_eq!(restored_status.receive_sequence(), third.seq);
	assert_eq!(restored_status.receive_cache_len(), 3);
	assert_eq!(
		restored.decrypt_message(&third).unwrap().unwrap().plaintext,
		b"third"
	);
	assert_eq!(restored.ratchet_status(kid).unwrap().receive_cache_len(), 2);
	assert_eq!(
		restored.decrypt_message(&first).unwrap().unwrap().plaintext,
		b"first"
	);
	assert_eq!(
		restored
			.decrypt_message(&second)
			.unwrap()
			.unwrap()
			.plaintext,
		b"second"
	);
}

#[test]
fn trusted_head_rejects_a_stale_snapshot() {
	let store = MemoryStore::default();
	let original = PersistentServer::create_with_lineage(
		0,
		Some(&[0x41; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x44; 32]),
	)
	.unwrap();
	let stale_bytes = store.snapshot_bytes();
	let stale_head = original.head();

	let activated = PersistentServer::restore(store.clone()).unwrap();
	assert_eq!(activated.head().generation(), stale_head.generation() + 1);
	let trusted_head = activated.head();
	let stale_view = store.clone().with_load_override(stale_bytes);
	assert!(matches!(
		PersistentServer::restore(stale_view),
		Err(PersistenceError::StaleGeneration)
	));
	assert_eq!(store.trusted_head(), Some(trusted_head));
}

#[test]
fn only_one_racing_restorer_can_activate_a_snapshot_head() {
	let store = MemoryStore::default();
	let original = PersistentServer::create_with_lineage(
		0,
		Some(&[0x47; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x45; 32]),
	)
	.unwrap();
	let barrier = Arc::new(Barrier::new(2));
	let first_store = store.clone().with_load_barrier(barrier.clone());
	let second_store = store.clone().with_load_barrier(barrier);
	let first =
		thread::spawn(move || PersistentServer::restore(first_store).map(|server| server.head()));
	let second =
		thread::spawn(move || PersistentServer::restore(second_store).map(|server| server.head()));
	let outcomes = [first.join().unwrap(), second.join().unwrap()];

	assert_eq!(outcomes.iter().filter(|outcome| outcome.is_ok()).count(), 1);
	assert_eq!(
		outcomes
			.iter()
			.filter(|outcome| matches!(outcome, Err(PersistenceError::StaleGeneration)))
			.count(),
		1
	);
	assert_eq!(
		store.trusted_head().unwrap().generation(),
		original.head().generation() + 1
	);
}

#[test]
fn cas_failure_withholds_the_result_and_poisons_the_live_instance() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x51; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x46; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
	let kid = test_register_persistent(&mut server, &mut beacon);
	let committed_head = server.head();
	let expected_sequence = server.ratchet_status(kid).unwrap().send_sequence() + 1;

	store.fail_next_cas();
	assert!(matches!(
		server.encrypt_message(b"must not escape before durability", kid),
		Err(PersistenceError::StaleGeneration)
	));
	assert!(server.is_poisoned());
	assert_eq!(server.head(), committed_head);
	assert_eq!(store.trusted_head(), Some(committed_head));
	assert!(matches!(
		server.encrypt_message(b"poisoned", kid),
		Err(PersistenceError::Poisoned)
	));

	let mut recovered = PersistentServer::restore(store.clone()).unwrap();
	let released = recovered
		.encrypt_message(b"must not escape before durability", kid)
		.unwrap()
		.unwrap();
	assert_eq!(released.seq, expected_sequence);
	assert_eq!(
		beacon.decrypt_message(&released).unwrap().plaintext,
		b"must not escape before durability"
	);
}

#[test]
fn failed_registration_response_keeps_consumption_committed() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x59; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x49; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let registration = server.get_shared_secret(&phase_1).unwrap().unwrap();
	let consumption_head = server.head();
	assert!(
		server
			.build_registration_response(registration, Some(&[]))
			.unwrap()
			.is_none()
	);
	assert_eq!(
		server.head().generation(),
		consumption_head.generation() + 1
	);
	drop(server);

	let mut restored = PersistentServer::restore(store).unwrap();
	assert!(restored.get_shared_secret(&phase_1).unwrap().is_none());
}

#[test]
fn a_peer_becomes_operational_only_after_pqxdh_establishment() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		0,
		Some(&[0x61; ED25519_SEED_SIZE]),
		store,
		SnapshotLineage::from_bytes([0x47; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());

	assert!(server.pk_by_kid(1).is_none());
	assert!(server.ratchet_status(1).is_none());
	assert!(
		server
			.encrypt_message(b"no all-zero ratchet", 1)
			.unwrap()
			.is_none()
	);

	let kid = test_register_persistent(&mut server, &mut beacon);
	assert_eq!(server.pk_by_kid(kid), Some(beacon.identity_pk()));
	assert!(server.ratchet_status(kid).is_some());
	let encrypted = server
		.encrypt_message(b"established", kid)
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.decrypt_message(&encrypted).unwrap().plaintext,
		b"established"
	);
}

#[test]
fn persistent_structured_updates_return_committed_outputs() {
	let store = MemoryStore::default();
	let mut server = PersistentServer::create_with_lineage(
		9,
		Some(&[0x63; ED25519_SEED_SIZE]),
		store.clone(),
		SnapshotLineage::from_bytes([0x4B; 32]),
	)
	.unwrap();
	let mut beacon = Beacon::new(9, server.identity_pk().as_bytes());
	let kid = test_register_persistent(&mut server, &mut beacon);

	let send = server
		.encrypt_and_update(b"binary send", kid)
		.unwrap()
		.unwrap();
	assert_eq!(send.kid, kid);
	assert_eq!(
		beacon.decrypt_message(&send.data).unwrap().plaintext,
		b"binary send"
	);

	let encrypted = beacon.encrypt_message(b"binary receive").unwrap();
	let receive = server.decrypt_and_update(&encrypted).unwrap().unwrap();
	assert_eq!(receive.kid, kid);
	assert_eq!(receive.data, b"binary receive");

	let send_json = server
		.encrypt_and_update_json(b"JSON send", kid)
		.unwrap()
		.unwrap();
	let send: serde_json::Value = serde_json::from_str(&send_json).unwrap();
	let ciphertext: Vec<u8> = serde_json::from_value(send["data"].clone()).unwrap();
	assert_eq!(
		beacon.decrypt_message(&ciphertext).unwrap().plaintext,
		b"JSON send"
	);

	let encrypted = beacon.encrypt_message(b"JSON receive").unwrap();
	let receive_json = server.decrypt_and_update_json(&encrypted).unwrap().unwrap();
	let receive: serde_json::Value = serde_json::from_str(&receive_json).unwrap();
	assert_eq!(receive["kid"], kid);
	let plaintext: Vec<u8> = serde_json::from_value(receive["data"].clone()).unwrap();
	assert_eq!(plaintext, b"JSON receive");

	assert_eq!(store.trusted_head(), Some(server.head()));
}
