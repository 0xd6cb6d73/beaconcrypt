#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use beaconcrypt::{
	Beacon, MLDSA_PUBLIC_KEY_LEN, MLDSA_SIGNATURE_LEN, MldsaIdentity, PersistentServer,
	ProviderBeacon, ProviderServer, Server, ServerSnapshot, SnapshotHead, SnapshotStore,
};
use beaconcrypt_parse::{InitKex, KexResponse};
use libsodium_rs::crypto_generichash;

mod common;

const SERVER_KID: u64 = 42;

fn server() -> Server {
	Server::new(SERVER_KID, Some(&[7; 32]), Some(&[8; 32]))
}

fn beacon(server: &Server) -> Beacon {
	Beacon::new(
		SERVER_KID,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	)
}

fn register(server: &mut Server, beacon: &mut Beacon, message: &[u8]) -> (Vec<u8>, Vec<u8>, u64) {
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap();
	let response = server
		.build_registration_response(accepted, Some(message))
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		message
	);
	(init, response.serialized, response.kid)
}

fn fingerprint(key: &[u8]) -> Vec<u8> {
	crypto_generichash::generichash(key, None, 64).unwrap()
}

fn init_with_payload(original: &[u8], payload: &[u8]) -> Vec<u8> {
	let mut rewritten = original[..common::INIT_HEADER].to_vec();
	rewritten.extend_from_slice(payload);
	rewritten
}

#[derive(Default)]
struct MemoryStore(Option<ServerSnapshot>);

impl SnapshotStore for MemoryStore {
	fn load(&self) -> Option<ServerSnapshot> {
		self.0
			.as_ref()
			.map(|snapshot| ServerSnapshot::from_bytes(snapshot.as_bytes().to_vec()))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let current = self.0.as_ref().map(|snapshot| snapshot.head().unwrap());
		if current.as_ref() != expected || replacement.validate_successor(expected).is_err() {
			return false;
		}
		self.0 = Some(ServerSnapshot::from_bytes(replacement.as_bytes().to_vec()));
		true
	}
}

fn persistent_server(mldsa_seed: &[u8]) -> PersistentServer<MemoryStore> {
	PersistentServer::create(
		SERVER_KID,
		Some(&[7; 32]),
		Some(mldsa_seed),
		MemoryStore::default(),
	)
	.unwrap()
}

fn assert_rejected_commit_preserves_protocol_state(
	before: &ServerSnapshot,
	after: &ServerSnapshot,
) {
	// Version 3 has a 100-byte envelope followed by the complete canonical server-state JSON.
	const HEADER_SIZE: usize = 100;
	for snapshot in [before, after] {
		assert_eq!(&snapshot.as_bytes()[16..18], &3u16.to_le_bytes());
	}
	assert!(before.as_bytes()[HEADER_SIZE..] == after.as_bytes()[HEADER_SIZE..]);
	let before_head = before.head().unwrap();
	let after_head = after.validate_successor(Some(&before_head)).unwrap();
	assert_eq!(after_head.generation(), before_head.generation() + 1);
}

#[test]
fn signed_registration_binds_both_public_keys_in_associated_data_and_exchanges_records() {
	let mut server = server();
	let mut beacon = beacon(&server);
	let server_key = server.mldsa_public_key();
	let beacon_key = beacon.mldsa_public_key();
	assert_ne!(server_key, beacon_key);
	let (init, response, kid) = register(&mut server, &mut beacon, b"authenticated welcome");
	assert!(init.starts_with(common::AUTH_MAGIC));
	assert!(response.starts_with(common::AUTH_MAGIC));
	assert_eq!(init[common::AUTH_MAGIC.len()], 0);
	assert_eq!(response[common::AUTH_MAGIC.len()], 1);
	assert_eq!(
		&init[common::AUTH_MAGIC.len() + 1..common::AUTH_MAGIC.len() + 1 + MLDSA_PUBLIC_KEY_LEN],
		&beacon_key
	);
	let ad = beacon.associated_data().unwrap();
	let base = beaconcrypt_core::pqxdh::build_associated_data(
		*server.identity_pk().as_bytes(),
		*beacon.identity_pk().as_bytes(),
	);
	assert_eq!(ad.len(), 281);
	assert_eq!(&ad[..153], &base[..153]);
	assert_eq!(&ad[153..217], fingerprint(&server_key));
	assert_eq!(&ad[217..281], fingerprint(&beacon_key));
	assert_eq!(
		server.mldsa_public_key_hash_by_kid(kid).unwrap().as_slice(),
		fingerprint(&beacon_key)
	);
	let encrypted = server.encrypt_message(b"server to beacon", kid).unwrap();
	assert_eq!(
		beacon
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.plaintext,
		b"server to beacon"
	);
	let encrypted = beacon.encrypt_message(b"beacon to server").unwrap();
	assert_eq!(
		server
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.plaintext,
		b"beacon to server"
	);
	assert!(beacon.finish_registration(&response).is_none());
	assert!(server.get_shared_secret(&init).is_none());
}

#[test]
fn every_init_field_and_envelope_key_is_authenticated_before_server_state_changes() {
	let mut server = persistent_server(&[8; 32]);
	let mut beacon = Beacon::new(
		SERVER_KID,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let decoded = common::decode_init(&init).unwrap();
	let fields = [
		decoded.identity_key.to_vec(),
		decoded.pre_key.to_vec(),
		decoded.one_time_key.to_vec(),
		decoded.pq_key.to_vec(),
	];
	let mut candidates = Vec::new();
	for index in 0..fields.len() {
		let mut altered = fields.clone();
		altered[index][0] ^= 1;
		candidates.push(init_with_payload(
			&init,
			&common::encode_unchecked_init(InitKex {
				identity_key: &altered[0],
				pre_key: &altered[1],
				one_time_key: &altered[2],
				pq_key: &altered[3],
			}),
		));
	}
	let mut substituted = init.clone();
	let key_start = common::AUTH_MAGIC.len() + 1;
	substituted[key_start..key_start + MLDSA_PUBLIC_KEY_LEN]
		.copy_from_slice(&MldsaIdentity::from_seed([9; 32]).public_key());
	candidates.push(substituted);
	let mut bad_signature = init.clone();
	bad_signature[key_start + MLDSA_PUBLIC_KEY_LEN] ^= 1;
	candidates.push(bad_signature);
	for candidate in candidates {
		let before = server.snapshot().unwrap();
		assert!(server.get_shared_secret(&candidate).unwrap().is_none());
		assert_rejected_commit_preserves_protocol_state(&before, &server.snapshot().unwrap());
	}
	let accepted = server.get_shared_secret(&init).unwrap().unwrap();
	let after_accept = server.snapshot().unwrap();
	assert!(server.get_shared_secret(&init).unwrap().is_none());
	assert_rejected_commit_preserves_protocol_state(&after_accept, &server.snapshot().unwrap());
	let response = server
		.build_registration_response(accepted, None)
		.unwrap()
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized),
		Some(vec![0xff])
	);
}

#[test]
fn a_beacon_pinned_to_another_mldsa_server_key_cannot_consume_a_registration() {
	let mut server = persistent_server(&[8; 32]);
	let wrong_key = MldsaIdentity::from_seed([9; 32]).public_key();
	let mut wrong = Beacon::new(SERVER_KID, server.identity_pk().as_bytes(), &wrong_key);
	let init = wrong.get_registration_bundle().unwrap();
	let before = server.snapshot().unwrap();
	assert!(server.get_shared_secret(&init).unwrap().is_none());
	assert_rejected_commit_preserves_protocol_state(&before, &server.snapshot().unwrap());
	let mut correct = Beacon::new(
		SERVER_KID,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = correct.get_registration_bundle().unwrap();
	assert!(server.get_shared_secret(&init).unwrap().is_some());
}

#[test]
fn accepted_tokens_cannot_be_retargeted_to_a_different_mldsa_identity_with_the_same_ed25519_key() {
	let mut first = persistent_server(&[8; 32]);
	let mut other = persistent_server(&[9; 32]);
	assert_eq!(first.identity_pk(), other.identity_pk());
	let mut beacon = Beacon::new(
		SERVER_KID,
		first.identity_pk().as_bytes(),
		&first.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = first.get_shared_secret(&init).unwrap().unwrap();
	let before = other.snapshot().unwrap();
	assert!(
		other
			.build_registration_response(accepted, None)
			.unwrap()
			.is_none()
	);
	assert_rejected_commit_preserves_protocol_state(&before, &other.snapshot().unwrap());
}

#[test]
fn every_response_field_is_authenticated_and_failure_aborts_the_beacon() {
	for index in 0..5 {
		let mut server = server();
		let mut beacon = beacon(&server);
		let init = beacon.get_registration_bundle().unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(accepted, None).unwrap();
		let decoded = common::decode_response(&response.serialized).unwrap();
		let mut fields = [
			decoded.identity_key.to_vec(),
			decoded.ephemeral_key.to_vec(),
			decoded.kem_cipher_text.to_vec(),
			decoded.app_cipher_text.to_vec(),
		];
		let mut key_id = decoded.key_id;
		if index < fields.len() {
			fields[index][0] ^= 1;
		} else {
			key_id ^= 1;
		}
		let modified = common::encode_response(KexResponse {
			identity_key: &fields[0],
			ephemeral_key: &fields[1],
			kem_cipher_text: &fields[2],
			app_cipher_text: &fields[3],
			key_id,
		});
		let candidate = common::replace_response_payload(&response.serialized, &modified);
		assert!(
			beacon.finish_registration(&candidate).is_none(),
			"field {index}"
		);
		assert!(beacon.ratchet_status().is_none());
		assert!(beacon.pq_sk().is_none());
		assert!(beacon.get_prekey_sk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.finish_registration(&response.serialized).is_none());
	}
}

#[test]
fn signatures_cannot_be_replayed_between_registration_transcripts() {
	let mut server = server();
	let mut first = beacon(&server);
	let mut second = beacon(&server);
	let first_init = first.get_registration_bundle().unwrap();
	let second_init = second.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&first_init).unwrap();
	let first_response = server.build_registration_response(accepted, None).unwrap();
	let accepted = server.get_shared_secret(&second_init).unwrap();
	let second_response = server.build_registration_response(accepted, None).unwrap();
	assert!(
		first
			.finish_registration(&second_response.serialized)
			.is_none()
	);
	assert!(first.ratchet_status().is_none());
	assert!(
		first
			.finish_registration(&first_response.serialized)
			.is_none()
	);
	assert_eq!(
		second.finish_registration(&second_response.serialized),
		Some(vec![0xff])
	);
	let encrypted = server
		.encrypt_message(b"correct session", second_response.kid)
		.unwrap();
	assert_eq!(
		second
			.decrypt_message(&encrypted.ciphertext)
			.unwrap()
			.plaintext,
		b"correct session"
	);
}

#[test]
fn unsigned_and_malformed_init_envelopes_are_rejected_without_consuming_the_original() {
	let mut server = persistent_server(&[8; 32]);
	let mut beacon = Beacon::new(
		SERVER_KID,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let mut candidates = vec![
		common::init_payload(&init).to_vec(),
		Vec::new(),
		init[..common::INIT_HEADER].to_vec(),
		init[..common::INIT_HEADER - 1].to_vec(),
	];
	let mut wrong_kind = init.clone();
	wrong_kind[common::AUTH_MAGIC.len()] = 1;
	candidates.push(wrong_kind);
	let mut wrong_magic = init.clone();
	wrong_magic[0] ^= 1;
	candidates.push(wrong_magic);
	let mut shortened_signature = init.clone();
	shortened_signature.remove(common::AUTH_MAGIC.len() + 1 + MLDSA_PUBLIC_KEY_LEN);
	candidates.push(shortened_signature);
	let mut trailing = init.clone();
	trailing.push(0);
	candidates.push(trailing);
	for candidate in candidates {
		let before = server.snapshot().unwrap();
		assert!(server.get_shared_secret(&candidate).unwrap().is_none());
		assert_rejected_commit_preserves_protocol_state(&before, &server.snapshot().unwrap());
	}
	assert!(server.get_shared_secret(&init).unwrap().is_some());
}

#[test]
fn unsigned_or_malformed_response_envelopes_terminally_abort_registration() {
	for case in 0..7 {
		let mut server = server();
		let mut beacon = beacon(&server);
		let init = beacon.get_registration_bundle().unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(accepted, None).unwrap();
		let mut candidate = response.serialized.clone();
		match case {
			0 => candidate = common::response_payload(&candidate).to_vec(),
			1 => candidate.truncate(common::RESPONSE_HEADER),
			2 => candidate.truncate(common::RESPONSE_HEADER - 1),
			3 => candidate[common::AUTH_MAGIC.len()] = 0,
			4 => candidate[common::AUTH_MAGIC.len() + 1] ^= 1,
			5 => {
				candidate.remove(common::AUTH_MAGIC.len() + MLDSA_SIGNATURE_LEN);
			}
			6 => candidate.push(0),
			_ => unreachable!(),
		}
		assert!(
			beacon.finish_registration(&candidate).is_none(),
			"case {case}"
		);
		assert!(beacon.ratchet_status().is_none());
		assert!(beacon.finish_registration(&response.serialized).is_none());
	}
}

#[test]
fn constructors_require_exact_identity_seed_and_mldsa_pin_lengths() {
	let server = server();
	for length in [0, 1, 31, 33, 64] {
		let invalid = vec![0; length];
		assert!(Server::try_new(SERVER_KID, Some(&invalid), None).is_err());
		assert!(Server::try_new(SERVER_KID, None, Some(&invalid)).is_err());
	}
	for length in [0, 1, 32, MLDSA_PUBLIC_KEY_LEN - 1, MLDSA_PUBLIC_KEY_LEN + 1] {
		assert!(
			Beacon::try_new(
				SERVER_KID,
				server.identity_pk().as_bytes(),
				&vec![0; length]
			)
			.is_err()
		);
	}
	for length in [0, 1, 31, 33] {
		assert!(Beacon::try_new(SERVER_KID, &vec![0; length], &server.mldsa_public_key()).is_err());
	}
}
