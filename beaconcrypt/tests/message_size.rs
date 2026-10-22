// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "beacon", feature = "server", feature = "pqxdh"))]

use beaconcrypt::{
	Beacon, PersistenceError, PersistentServer, ProviderBeacon, ProviderServer, Server,
	ServerSnapshot, SnapshotHead, SnapshotStore,
};
use beaconcrypt_parse::{MAX_MESSAGE_SIZE, decode_frame, encoded_frame_len};
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct StoredState {
	snapshot: Option<ServerSnapshot>,
	attempts: usize,
	fail_next: bool,
}

#[derive(Clone, Default)]
struct Store(Arc<Mutex<StoredState>>);

impl Store {
	fn attempts(&self) -> usize {
		self.0.lock().unwrap().attempts
	}

	fn bytes(&self) -> Vec<u8> {
		self.0
			.lock()
			.unwrap()
			.snapshot
			.as_ref()
			.unwrap()
			.as_bytes()
			.to_vec()
	}
}

impl SnapshotStore for Store {
	fn load(&self) -> Option<ServerSnapshot> {
		self.0
			.lock()
			.unwrap()
			.snapshot
			.as_ref()
			.map(|snapshot| ServerSnapshot::from_bytes(snapshot.as_bytes().to_vec()))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let mut state = self.0.lock().unwrap();
		state.attempts += 1;
		if std::mem::take(&mut state.fail_next) {
			return false;
		}
		let current = state
			.snapshot
			.as_ref()
			.map(|snapshot| snapshot.head().unwrap());
		if current.as_ref() != expected || replacement.validate_successor(expected).is_err() {
			return false;
		}
		state.snapshot = Some(ServerSnapshot::from_bytes(replacement.as_bytes().to_vec()));
		true
	}
}

#[test]
fn complete_frame_limit_is_inclusive_and_rejections_preserve_ratchets() {
	let mut server = Server::new(0, None, None);
	let mut beacon = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap();
	let response = server.build_registration_response(accepted, None).unwrap();
	beacon.finish_registration(&response.serialized).unwrap();

	// At this size, two one-byte integers and the byte-string header take ten CBOR bytes.
	let maximum_plaintext = MAX_MESSAGE_SIZE - 80 - 10;
	assert_eq!(
		encoded_frame_len(1, response.kid, maximum_plaintext + 80),
		Some(MAX_MESSAGE_SIZE)
	);
	let plaintext = vec![0x5a; maximum_plaintext + 1];
	let sender_before = beacon.ratchet_status().unwrap();
	assert!(beacon.encrypt_message(&plaintext).is_none());
	assert_eq!(beacon.ratchet_status().unwrap(), sender_before);

	let mut frame = beacon
		.encrypt_message(&plaintext[..maximum_plaintext])
		.unwrap();
	assert_eq!(frame.ciphertext.len(), MAX_MESSAGE_SIZE);
	assert_eq!(frame.seq, 1);
	assert!(decode_frame(&frame.ciphertext).is_some());
	frame.ciphertext.reserve_exact(1);
	frame.ciphertext.push(0);
	let receiver_before = server.ratchet_status(response.kid).unwrap();
	assert!(server.decrypt_message(&frame).is_none());
	assert_eq!(
		server.ratchet_status(response.kid).unwrap(),
		receiver_before
	);
	frame.ciphertext.pop();
	assert_eq!(
		server.decrypt_message(&frame).unwrap().plaintext,
		plaintext[..maximum_plaintext]
	);
}

#[test]
fn flattened_registration_response_accepts_the_exact_complete_message_limit() {
	let mut server = Server::new(0, None, None);
	let mut beacon = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap();
	// The v2 response adds 4,480 bytes to its raw payload, including the
	// 3,309-byte signature and its three-byte CBOR header. The raw payload adds
	// the eight-byte assigned-ID binding, tag, and commitment.
	let application = vec![0x63; MAX_MESSAGE_SIZE - 4_568];
	let response = server
		.build_registration_response(accepted, Some(&application))
		.unwrap();
	assert_eq!(response.kid, 1);
	assert_eq!(response.serialized.len(), MAX_MESSAGE_SIZE);
	let decoded = decode_response(&response.serialized).unwrap();
	assert_eq!(decoded.app_cipher_text.len(), application.len() + 8 + 80);
	assert_eq!(
		beacon.finish_registration(&response.serialized),
		Some(application)
	);
	assert_eq!(beacon.ratchet_status().unwrap().receive_sequence(), 1);
	assert_eq!(
		server.ratchet_status(response.kid).unwrap().send_sequence(),
		1
	);
}

#[test]
fn persistent_oversize_rejections_skip_cas_and_preserve_poison_fencing() {
	let store = Store::default();
	let mut server = PersistentServer::create(0, None, None, store.clone()).unwrap();
	let mut first = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = first.get_registration_bundle().unwrap();
	let mut oversized = init.clone();
	oversized.resize(MAX_MESSAGE_SIZE + 1, 0);
	// The inclusive boundary still admits an ordinary registration attempt. This
	// malformed request follows the existing persisted-rejection behavior.
	let head = server.head();
	let attempts = store.attempts();
	assert!(
		server
			.get_shared_secret(&oversized[..MAX_MESSAGE_SIZE])
			.unwrap()
			.is_none()
	);
	assert_eq!(server.head().generation(), head.generation() + 1);
	assert_eq!(store.attempts(), attempts + 1);
	let head = server.head();
	let attempts = store.attempts();
	let snapshot = store.bytes();
	assert!(server.get_shared_secret(&oversized).unwrap().is_none());
	assert_eq!(server.head(), head);
	assert_eq!(store.attempts(), attempts);
	assert_eq!(store.bytes(), snapshot);
	// Rejection of the oversized request leaves its registration identifier fresh.
	let accepted = server.get_shared_secret(&init).unwrap().unwrap();
	let head = server.head();
	let attempts = store.attempts();
	let snapshot = store.bytes();
	// The raw ciphertext fits, but its binding and outer response exceed the cap.
	let response_too_large = &oversized[..MAX_MESSAGE_SIZE - 4_567];
	assert!(
		server
			.build_registration_response(accepted, Some(response_too_large))
			.unwrap()
			.is_none()
	);
	assert_eq!(server.head(), head);
	assert_eq!(store.attempts(), attempts);
	assert_eq!(store.bytes(), snapshot);
	assert_eq!(server.server_kid(), 0);
	assert!(server.pk_by_kid(1).is_none());
	assert!(server.ratchet_status(1).is_none());

	let mut beacon = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap().unwrap();
	let response = server
		.build_registration_response(accepted, None)
		.unwrap()
		.unwrap();
	beacon.finish_registration(&response.serialized).unwrap();
	let head = server.head();
	let attempts = store.attempts();
	let snapshot = store.bytes();
	let status = server.ratchet_status(response.kid).unwrap();
	let plaintext_too_large = &oversized[..MAX_MESSAGE_SIZE - 89];
	assert!(
		server
			.encrypt_message(plaintext_too_large, response.kid)
			.unwrap()
			.is_none()
	);
	assert!(
		server
			.encrypt_and_update(plaintext_too_large, response.kid)
			.unwrap()
			.is_none()
	);
	assert!(
		server
			.encrypt_and_update_json(plaintext_too_large, response.kid)
			.unwrap()
			.is_none()
	);
	assert!(server.decrypt_message(&oversized).unwrap().is_none());
	assert!(server.decrypt_and_update(&oversized).unwrap().is_none());
	assert!(
		server
			.decrypt_and_update_json(&oversized)
			.unwrap()
			.is_none()
	);
	assert_eq!(server.ratchet_status(response.kid).unwrap(), status);
	assert_eq!(server.head(), head);
	assert_eq!(store.attempts(), attempts);
	assert_eq!(store.bytes(), snapshot);
	assert!(!server.is_poisoned());
	let encrypted = server
		.encrypt_message(b"retry", response.kid)
		.unwrap()
		.unwrap();
	assert_eq!(encrypted.seq, status.send_sequence() + 1);
	assert_eq!(
		beacon.decrypt_message(&encrypted).unwrap().plaintext,
		b"retry"
	);

	let mut pending_beacon = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = pending_beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&init).unwrap().unwrap();
	store.0.lock().unwrap().fail_next = true;
	assert_eq!(
		server.encrypt_message(b"fence", response.kid).err(),
		Some(PersistenceError::StaleGeneration)
	);
	assert!(server.is_poisoned());
	let attempts = store.attempts();
	assert_eq!(
		server.get_shared_secret(&oversized).err(),
		Some(PersistenceError::Poisoned)
	);
	assert_eq!(
		server
			.build_registration_response(pending, Some(response_too_large))
			.err(),
		Some(PersistenceError::Poisoned)
	);
	assert_eq!(
		server
			.encrypt_message(plaintext_too_large, response.kid)
			.err(),
		Some(PersistenceError::Poisoned)
	);
	assert_eq!(
		server
			.encrypt_and_update(plaintext_too_large, response.kid)
			.err(),
		Some(PersistenceError::Poisoned)
	);
	assert_eq!(
		server
			.encrypt_and_update_json(plaintext_too_large, response.kid)
			.err(),
		Some(PersistenceError::Poisoned)
	);
	assert_eq!(store.attempts(), attempts);
}

mod common;
use common::decode_response;

#[test]
fn signed_response_cbor_overflow_rejects_before_persistence() {
	let store = Store::default();
	let mut server = PersistentServer::create(0, None, None, store.clone()).unwrap();
	let mut beacon = Beacon::new(
		0,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap().unwrap();
	let head = server.head();
	let attempts = store.attempts();
	let snapshot = store.bytes();
	// The complete v2 CBOR response exceeds the inclusive cap by exactly one byte.
	let application = vec![0x63; MAX_MESSAGE_SIZE - 4_567];
	assert!(
		server
			.build_registration_response(accepted, Some(&application))
			.unwrap()
			.is_none()
	);
	assert_eq!(server.head(), head);
	assert_eq!(store.attempts(), attempts);
	assert_eq!(store.bytes(), snapshot);
	assert_eq!(server.server_kid(), 0);
	assert!(server.pk_by_kid(1).is_none());
}
