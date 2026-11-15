#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use beaconcrypt::{
	Beacon, MLDSA_PUBLIC_KEY_LEN, MLDSA_SIGNATURE_LEN, MldsaIdentity, PersistentServer,
	ProviderBeacon, ProviderServer, Server, ServerSnapshot, SnapshotHead, SnapshotStore,
};
use beaconcrypt_crypto::crypto_generichash;
use beaconcrypt_parse::{InitKex, KexResponse};

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

fn legacy_init(init: InitKex<'_>) -> Vec<u8> {
	let mut encoded = common::encode_unchecked_init(init);
	encoded[1] = 2;
	encoded
}

fn legacy_response(response: KexResponse<'_>) -> Vec<u8> {
	let mut encoded = common::encode_unchecked_response(KexResponse {
		signature: &[],
		..response
	});
	encoded.pop();
	encoded[..3].copy_from_slice(&[0x87, 1, 1]);
	encoded
}

#[derive(Default)]
struct MemoryStore(Option<ServerSnapshot>);

impl SnapshotStore for MemoryStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, beaconcrypt::PersistenceError> {
		Ok(self
			.0
			.as_ref()
			.map(|snapshot| ServerSnapshot::from_bytes(snapshot.as_bytes().to_vec())))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, beaconcrypt::PersistenceError> {
		let current = self.0.as_ref().map(|snapshot| snapshot.head().unwrap());
		if current.as_ref() != expected || replacement.validate_successor(expected).is_err() {
			return Ok(false);
		}
		self.0 = Some(ServerSnapshot::from_bytes(replacement.as_bytes().to_vec()));
		Ok(true)
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
	// Rejected authentication is an exact-state transition and does not create a generation.
	assert_eq!(before.as_bytes(), after.as_bytes());
	assert_eq!(before.head().unwrap(), after.head().unwrap());
}

#[test]
fn registration_uses_exact_transcript_context_and_exchanges_records() {
	let mut server = server();
	let mut beacon = beacon(&server);
	let (init, response, kid) = register(&mut server, &mut beacon, b"authenticated welcome");
	assert_eq!(init.len(), 1490);
	assert!(init.starts_with(&[0x86, 3, 0]));
	assert!(response.starts_with(&[0x88, 3, 1]));
	let request = common::decode_init(&init).unwrap();
	let reply = common::decode_response(&response).unwrap();
	assert_eq!(reply.signature.len(), MLDSA_SIGNATURE_LEN);
	assert_eq!(common::encode_unchecked_init(request), init);
	assert_eq!(common::encode_response(reply), response);
	let mut preimage = Vec::new();
	for field in [
		request.identity_key,
		request.pre_key,
		request.one_time_key,
		request.pq_key,
		reply.identity_key,
		reply.ephemeral_key,
		reply.kem_cipher_text,
	] {
		preimage.extend_from_slice(field);
	}
	preimage.extend_from_slice(&kid.to_le_bytes());
	assert_eq!(preimage.len(), 2638);
	let hash = crypto_generichash::generichash(&preimage, None, 64).unwrap();
	let ad = beacon.associated_data().unwrap();
	assert_eq!(ad.len(), 151);
	assert_eq!(
		&ad[..87],
		b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"
	);
	assert_eq!(&ad[87..], hash);
	let encrypted = server.encrypt_message(b"server to beacon", kid).unwrap();
	assert_eq!(
		beacon.decrypt_message(&encrypted).unwrap().plaintext,
		b"server to beacon"
	);
	let encrypted = beacon.encrypt_message(b"beacon to server").unwrap();
	assert_eq!(
		server.decrypt_message(&encrypted).unwrap().plaintext,
		b"beacon to server"
	);
	assert!(beacon.finish_registration(&response).is_none());
	assert!(server.get_shared_secret(&init).is_none());
}

#[test]
fn every_init_field_is_classically_authenticated_before_server_state_changes() {
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
		candidates.push(common::encode_unchecked_init(InitKex {
			identity_key: &altered[0],
			pre_key: &altered[1],
			one_time_key: &altered[2],
			pq_key: &altered[3],
		}));
	}

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
fn wrong_server_pin_allows_server_registration_but_aborts_beacon_finish() {
	let mut server = server();
	let wrong_key = MldsaIdentity::from_seed([9; 32]).public_key();
	let mut wrong = Beacon::new(SERVER_KID, server.identity_pk().as_bytes(), &wrong_key);
	let init = wrong.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap();
	let response = server.build_registration_response(accepted, None).unwrap();
	assert!(wrong.finish_registration(&response.serialized).is_none());
	assert!(wrong.ratchet_status().is_none());
	assert!(wrong.finish_registration(&response.serialized).is_none());
	assert!(server.get_shared_secret(&init).is_none());
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
		let candidate = common::encode_response(KexResponse {
			identity_key: &fields[0],
			ephemeral_key: &fields[1],
			kem_cipher_text: &fields[2],
			app_cipher_text: &fields[3],
			key_id,
			signature: decoded.signature,
		});
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
fn legacy_and_malformed_init_cbor_is_rejected_without_consuming_the_original() {
	let mut server = persistent_server(&[8; 32]);
	let mut beacon = Beacon::new(
		SERVER_KID,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let decoded = common::decode_init(&init).unwrap();
	let old_cbor = legacy_init(decoded);
	let mut old_envelope = b"beaconcrypt/ml-dsa-65/v1\0".to_vec();
	old_envelope.push(0);
	old_envelope.extend_from_slice(&old_cbor);
	let mut candidates = vec![old_cbor, old_envelope, Vec::new(), init[..1].to_vec()];
	candidates.push(init[..init.len() - 1].to_vec());
	for length in [0, 32, 34] {
		let identity = vec![1; length];
		candidates.push(common::encode_unchecked_init(InitKex {
			identity_key: &identity,
			..decoded
		}));
	}

	let mut wrong_kind = init.clone();
	wrong_kind[2] = 1;
	candidates.push(wrong_kind);
	let mut wrong_version = init.clone();
	wrong_version[1] = 1;
	candidates.push(wrong_version);
	let mut wrong_array = init.clone();
	wrong_array[0] = 0x88;
	candidates.push(wrong_array);
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
fn unsigned_or_malformed_response_cbor_terminally_aborts_registration() {
	for case in 0..11 {
		let mut server = server();
		let mut beacon = beacon(&server);
		let init = beacon.get_registration_bundle().unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(accepted, None).unwrap();
		let decoded = common::decode_response(&response.serialized).unwrap();
		let mut candidate = response.serialized.clone();
		match case {
			0 => candidate = legacy_response(decoded),
			1 => {
				candidate = b"beaconcrypt/ml-dsa-65/v1\0".to_vec();
				candidate.push(1);
				candidate.extend_from_slice(decoded.signature);
				candidate.extend_from_slice(&legacy_response(decoded));
			}
			2..=4 => {
				let length = [0, MLDSA_SIGNATURE_LEN - 1, MLDSA_SIGNATURE_LEN + 1][case - 2];
				let mut signature = decoded.signature.to_vec();
				signature.resize(length, 0);
				candidate = common::encode_unchecked_response(KexResponse {
					signature: &signature,
					..decoded
				});
			}
			5 => {
				let mut signature = decoded.signature.to_vec();
				signature[0] ^= 1;
				candidate = common::encode_response(KexResponse {
					signature: &signature,
					..decoded
				});
			}
			6 => candidate[2] = 0,
			7 => candidate[1] = 1,
			8 => candidate.truncate(1),
			9 => candidate.truncate(candidate.len() - 1),
			10 => candidate.push(0),
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
