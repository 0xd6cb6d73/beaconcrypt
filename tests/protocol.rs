use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use std::panic::{AssertUnwindSafe, catch_unwind};

const SERVER_KID: u64 = 0;
const TAG_SIZE: usize = 16;
const COMMITMENT_SIZE: usize = 64;

fn new_pair() -> (BeaconCryptPqxdh, BeaconCryptPqxdh) {
	let server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let beacon = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	(server, beacon)
}

fn register_beacon(
	server: &mut BeaconCryptPqxdh,
	beacon: &mut BeaconCryptPqxdh,
	initial_message: Option<&[u8]>,
) -> RegResponse {
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let reg_out = server.get_shared_secret(&phase_1).unwrap();
	let phase_2 = server
		.build_registration_response(reg_out, initial_message)
		.unwrap();
	let plaintext = beacon.finish_registration(&phase_2.serialized).unwrap();
	// `build_registration_response` insert a single 0xFF byte if no initial message is provided to satisfy the upstream specification's requirement
	// this allows the beacon to check that keychain derivation is correct
	assert_eq!(plaintext, initial_message.unwrap_or(&[0xFFu8; 1]));
	phase_2
}

fn corrupt_aead_ciphertext(serialized: &[u8]) -> Vec<u8> {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed_reader = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	let frame = typed_reader.get().unwrap();
	let mut ciphertext = frame.get_cipher_text().unwrap().to_vec();
	ciphertext[0] ^= 0x01;

	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut corrupted = message.init_root();
	corrupted.set_seq(frame.get_seq());
	corrupted.set_cipher_text(&ciphertext);

	let mut serialized = vec![];
	capnp::serialize::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

fn serialize_crypto_frame(seq: u64, ciphertext: &[u8]) -> Vec<u8> {
	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut frame = message.init_root();
	frame.set_seq(seq);
	frame.set_cipher_text(ciphertext);

	let mut serialized = vec![];
	capnp::serialize::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

fn crypto_frame_seq(serialized: &[u8]) -> u64 {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	typed.get().unwrap().get_seq()
}

fn crypto_frame_ciphertext(serialized: &[u8]) -> Vec<u8> {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	typed.get().unwrap().get_cipher_text().unwrap().to_vec()
}

fn assert_server_frame_tampering_is_rejected(mut tamper: impl FnMut(&mut Vec<u8>, &[u8])) {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let plaintext = b"message whose authenticated fields will be tampered with";
	let valid = server.encrypt_message(plaintext, response.kid).unwrap();
	let donor = server
		.encrypt_message(
			b"a second message supplies independently generated fields",
			response.kid,
		)
		.unwrap();
	let seq = crypto_frame_seq(&valid);
	let mut ciphertext = crypto_frame_ciphertext(&valid);
	let donor_ciphertext = crypto_frame_ciphertext(&donor);

	tamper(&mut ciphertext, &donor_ciphertext);
	let tampered = serialize_crypto_frame(seq, &ciphertext);

	assert!(beacon.decrypt_message(&tampered, SERVER_KID).is_none());
	assert_eq!(
		beacon.decrypt_message(&valid, SERVER_KID).unwrap(),
		plaintext,
		"rejecting a tampered frame must not consume its receive key"
	);
}

struct KexResponseParts {
	identity_key: Vec<u8>,
	ephemeral_key: Vec<u8>,
	kem_ciphertext: Vec<u8>,
	app_ciphertext: Vec<u8>,
	key_id: u64,
}

fn parse_kex_response(serialized: &[u8]) -> KexResponseParts {
	let message = capnp::serialize_packed::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(message);
	let response = typed.get().unwrap();
	KexResponseParts {
		identity_key: response.get_identity_key().unwrap().to_vec(),
		ephemeral_key: response.get_ephemeral_key().unwrap().to_vec(),
		kem_ciphertext: response.get_kem_cipher_text().unwrap().to_vec(),
		app_ciphertext: response.get_app_cipher_text().unwrap().to_vec(),
		key_id: response.get_key_id(),
	}
}

fn serialize_kex_response(parts: &KexResponseParts) -> Vec<u8> {
	let mut message = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
	let mut response = message.init_root();
	response.set_identity_key(&parts.identity_key);
	response.set_ephemeral_key(&parts.ephemeral_key);
	response.set_kem_cipher_text(&parts.kem_ciphertext);
	response.set_app_cipher_text(&parts.app_ciphertext);
	response.set_key_id(parts.key_id);

	let mut serialized = vec![];
	capnp::serialize_packed::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

fn pending_registration(initial_message: &[u8]) -> (BeaconCryptPqxdh, Vec<u8>) {
	let (mut server, mut beacon) = new_pair();
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let reg_out = server.get_shared_secret(&phase_1).unwrap();
	let response = server
		.build_registration_response(reg_out, Some(initial_message))
		.unwrap();
	(beacon, response.serialized)
}

fn rewrite_protogram_key_id(serialized: &[u8], key_id: u64) -> Vec<u8> {
	let message = capnp::serialize_packed::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, protogram_capnp::proto_gram::Owned>::new(message);
	let original = typed.get().unwrap();

	let mut message = TypedBuilder::<protogram_capnp::proto_gram::Owned>::new_default();
	let mut rewritten = message.init_root();
	rewritten.set_key_id(key_id);
	rewritten.set_data(original.get_data().unwrap());

	let mut serialized = vec![];
	capnp::serialize_packed::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

#[test]
fn server_uses_per_beacon_associated_data() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let b1_response = register_beacon(&mut server, &mut b1, Some(b"initial message for b1"));
	let b2_response = register_beacon(&mut server, &mut b2, Some(b"initial message for b2"));

	let to_b1 = server
		.encrypt_message(b"server to b1", b1_response.kid)
		.unwrap();
	let to_b2 = server
		.encrypt_message(b"server to b2", b2_response.kid)
		.unwrap();
	assert_eq!(
		b1.decrypt_message(&to_b1, SERVER_KID).unwrap(),
		b"server to b1"
	);
	assert_eq!(
		b2.decrypt_message(&to_b2, SERVER_KID).unwrap(),
		b"server to b2"
	);

	let from_b1 = b1.encrypt_message(b"b1 to server", SERVER_KID).unwrap();
	let from_b2 = b2.encrypt_message(b"b2 to server", SERVER_KID).unwrap();
	assert_eq!(
		server.decrypt_message(&from_b1, b1_response.kid).unwrap(),
		b"b1 to server"
	);
	assert_eq!(
		server.decrypt_message(&from_b2, b2_response.kid).unwrap(),
		b"b2 to server"
	);
}

#[test]
fn server_can_encrypt_to_beacon_a_after_registering_beacon_b() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut beacon_a = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut beacon_b = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let beacon_a_response = register_beacon(&mut server, &mut beacon_a, None);
	register_beacon(&mut server, &mut beacon_b, None);

	let message = b"server to beacon A after registering beacon B";
	let ciphertext = server
		.encrypt_message(message, beacon_a_response.kid)
		.unwrap();

	assert_eq!(
		beacon_a.decrypt_message(&ciphertext, SERVER_KID).unwrap(),
		message
	);
}

#[test]
fn server_can_decrypt_from_beacon_a_after_registering_beacon_b() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut beacon_a = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut beacon_b = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let beacon_a_response = register_beacon(&mut server, &mut beacon_a, None);
	register_beacon(&mut server, &mut beacon_b, None);

	let message = b"beacon A to server after registering beacon B";
	let ciphertext = beacon_a.encrypt_message(message, SERVER_KID).unwrap();

	assert_eq!(
		server
			.decrypt_message(&ciphertext, beacon_a_response.kid)
			.unwrap(),
		message
	);
}

#[test]
fn server_can_decrypt_from_beacon_a_after_encrypting_to_beacon_b() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut beacon_a = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut beacon_b = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let beacon_a_response = register_beacon(&mut server, &mut beacon_a, None);
	let beacon_b_response = register_beacon(&mut server, &mut beacon_b, None);

	let to_beacon_b = server
		.encrypt_message(b"server to beacon B", beacon_b_response.kid)
		.unwrap();
	assert_eq!(
		beacon_b.decrypt_message(&to_beacon_b, SERVER_KID).unwrap(),
		b"server to beacon B"
	);

	let from_beacon_a = beacon_a
		.encrypt_message(b"beacon A to server", SERVER_KID)
		.unwrap();
	assert_eq!(
		server
			.decrypt_message(&from_beacon_a, beacon_a_response.kid)
			.unwrap(),
		b"beacon A to server"
	);
}

#[test]
fn interleaved_registrations_use_the_correct_associated_data() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let b1_phase_1 = b1.get_registration_bundle().unwrap();
	let b2_phase_1 = b2.get_registration_bundle().unwrap();
	let b1_registration = server.get_shared_secret(&b1_phase_1).unwrap();
	let b2_registration = server.get_shared_secret(&b2_phase_1).unwrap();

	let b1_phase_2 = server
		.build_registration_response(b1_registration, Some(b"initial message for b1"))
		.unwrap();
	let b2_phase_2 = server
		.build_registration_response(b2_registration, Some(b"initial message for b2"))
		.unwrap();

	assert_eq!(
		b1.finish_registration(&b1_phase_2.serialized).unwrap(),
		b"initial message for b1"
	);
	assert_eq!(
		b2.finish_registration(&b2_phase_2.serialized).unwrap(),
		b"initial message for b2"
	);
}

#[test]
fn malformed_registration_is_rejected() {
	let (mut server, _) = new_pair();

	assert!(server.get_shared_secret(b"not a registration").is_none());
}

#[test]
fn registration_can_omit_initial_message() {
	let (mut server, mut beacon) = new_pair();

	let response = register_beacon(&mut server, &mut beacon, None);

	assert_eq!(response.kid, 1);
}

#[test]
fn beacon_rejects_registration_response_from_wrong_server() {
	let (mut expected_server, mut beacon) = new_pair();
	let mut wrong_server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);

	let phase_1 = beacon.get_registration_bundle().unwrap();
	assert!(expected_server.get_shared_secret(&phase_1).is_some());
	let reg_out = wrong_server.get_shared_secret(&phase_1).unwrap();
	let phase_2 = wrong_server
		.build_registration_response(reg_out, Some(b"wrong server"))
		.unwrap();

	assert!(beacon.finish_registration(&phase_2.serialized).is_none());
}

#[test]
fn beacon_can_encrypt_to_server() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"beacon to server";

	let ciphertext = beacon
		.encrypt_message(message.as_slice(), SERVER_KID)
		.unwrap();
	let plaintext = server.decrypt_message(&ciphertext, response.kid).unwrap();

	assert_eq!(plaintext, message);
}

#[test]
fn beacon_can_encrypt_to_server_signed() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"signed beacon to server";

	let ciphertext = beacon
		.encrypt_message(message.as_slice(), SERVER_KID)
		.unwrap();
	let signed = beacon.sign_message(&ciphertext).unwrap();
	let verified = server.verify_signature(&signed).unwrap();
	let plaintext = server
		.decrypt_message(&verified.data, verified.key_id)
		.unwrap();

	assert_eq!(verified.key_id, response.kid);
	assert_eq!(plaintext, message);
}

#[test]
fn encrypt_and_sign_encrypts_before_signing() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"signed server to beacon";

	let signed = server.encrypt_and_sign(message, response.kid).unwrap();
	let verified = beacon.verify_signature(&signed).unwrap();

	assert_eq!(verified.key_id, SERVER_KID);
	assert_eq!(
		beacon.decrypt_message(&verified.data, SERVER_KID).unwrap(),
		message
	);
}

#[test]
fn decrypt_signed_verifies_the_sender_and_uses_its_key_id() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"signed beacon to server";
	let ciphertext = beacon.encrypt_message(message, SERVER_KID).unwrap();
	let signed = beacon.sign_message(&ciphertext).unwrap();
	let verified = server.decrypt_signed(&signed).unwrap();

	assert_eq!(verified.key_id, response.kid);
	assert_eq!(verified.data, message);
}

#[test]
fn signed_beacon_message_rejects_tampering() {
	let (mut server, mut beacon) = new_pair();
	register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let ciphertext = beacon
		.encrypt_message(b"beacon to server", SERVER_KID)
		.unwrap();
	let mut signed = beacon.sign_message(&ciphertext).unwrap();
	let last = signed.len() - 1;
	signed[last] ^= 0x01;

	assert!(server.verify_signature(&signed).is_none());
}

#[test]
fn signed_server_message_rejects_tampering() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let ciphertext = server
		.encrypt_message(b"server to beacon", response.kid)
		.unwrap();
	let mut signed = server.sign_message(&ciphertext).unwrap();
	let last = signed.len() - 1;
	signed[last] ^= 0x01;

	assert!(beacon.verify_signature(&signed).is_none());
}

#[test]
fn decrypt_rejects_wrong_direction() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let server_to_beacon = server
		.encrypt_message(b"server to beacon", response.kid)
		.unwrap();
	assert!(
		server
			.decrypt_message(&server_to_beacon, response.kid)
			.is_none()
	);

	let beacon_to_server = beacon
		.encrypt_message(b"beacon to server", SERVER_KID)
		.unwrap();
	assert!(
		beacon
			.decrypt_message(&beacon_to_server, SERVER_KID)
			.is_none()
	);
}

#[test]
fn beacon_cannot_decrypt_message_for_different_beacon() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let b1_response = register_beacon(&mut server, &mut b1, Some(&[0xFF; 32]));
	let _ = register_beacon(&mut server, &mut b2, Some(&[0xFF; 32]));

	let ciphertext = server
		.encrypt_message(b"for b1 only", b1_response.kid)
		.unwrap();

	assert!(b2.decrypt_message(&ciphertext, SERVER_KID).is_none());
}

#[test]
fn ciphertext_cannot_be_replayed() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"one shot";

	let ciphertext = server.encrypt_message(message, response.kid).unwrap();
	let first = beacon.decrypt_message(&ciphertext, SERVER_KID).unwrap();

	assert_eq!(first, message);
	assert!(beacon.decrypt_message(&ciphertext, SERVER_KID).is_none());
}

#[test]
fn beacon_can_retry_decryption_after_corrupted_aead_message() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"server to beacon";

	let ciphertext = server.encrypt_message(message, response.kid).unwrap();
	let corrupted = corrupt_aead_ciphertext(&ciphertext);

	assert!(beacon.decrypt_message(&corrupted, SERVER_KID).is_none());
	assert_eq!(
		beacon.decrypt_message(&ciphertext, SERVER_KID).unwrap(),
		message
	);
}

#[test]
fn server_can_retry_decryption_after_corrupted_aead_message() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"beacon to server";

	let ciphertext = beacon.encrypt_message(message, SERVER_KID).unwrap();
	let corrupted = corrupt_aead_ciphertext(&ciphertext);

	assert!(server.decrypt_message(&corrupted, response.kid).is_none());
	assert_eq!(
		server.decrypt_message(&ciphertext, response.kid).unwrap(),
		message
	);
}

#[test]
fn encrypt_and_update_returns_the_advanced_send_state() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"server to beacon with updated state";
	let (send_state_before, recv_state_before) = {
		let ratchet = server.ratchet_manager(response.kid).unwrap();
		(
			ratchet.send_state().as_slice().to_vec(),
			ratchet.recv_state().as_slice().to_vec(),
		)
	};

	let update = server.encrypt_and_update(message, response.kid).unwrap();
	let ratchet = server.ratchet_manager(response.kid).unwrap();

	assert_eq!(update.kid, response.kid);
	assert_eq!(update.key.as_slice(), ratchet.send_state().as_slice());
	assert_ne!(update.key.as_slice(), send_state_before);
	assert_eq!(ratchet.recv_state().as_slice(), recv_state_before);
	let verified = beacon.decrypt_signed(&update.data).unwrap();
	assert_eq!(verified.key_id, SERVER_KID);
	assert_eq!(verified.data, message);
}

#[test]
fn decrypt_and_update_returns_the_advanced_receive_state() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"beacon to server with updated state";
	let ciphertext = beacon.encrypt_and_sign(message, SERVER_KID).unwrap();
	let (send_state_before, recv_state_before) = {
		let ratchet = server.ratchet_manager(response.kid).unwrap();
		(
			ratchet.send_state().as_slice().to_vec(),
			ratchet.recv_state().as_slice().to_vec(),
		)
	};

	let update = server.decrypt_and_update(&ciphertext).unwrap();
	let ratchet = server.ratchet_manager(response.kid).unwrap();

	assert_eq!(update.kid, response.kid);
	assert_eq!(update.data, message);
	assert_eq!(update.key.as_slice(), ratchet.recv_state().as_slice());
	assert_ne!(update.key.as_slice(), recv_state_before);
	assert_eq!(ratchet.send_state().as_slice(), send_state_before);
}

#[test]
fn malformed_crypto_frame_ciphertext_lengths_are_rejected_without_panicking() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let valid = server
		.encrypt_message(b"valid after malformed frames", response.kid)
		.unwrap();
	let seq = crypto_frame_seq(&valid);

	for len in [0, 1, 15, 16, 63, 64, 79, 80] {
		let malformed = serialize_crypto_frame(seq, &vec![0xA5; len]);
		let result = catch_unwind(AssertUnwindSafe(|| {
			beacon.decrypt_message(&malformed, SERVER_KID)
		}));
		assert!(
			matches!(result, Ok(None)),
			"ciphertext length {len} was not rejected cleanly"
		);
	}

	assert_eq!(
		beacon.decrypt_message(&valid, SERVER_KID).unwrap(),
		b"valid after malformed frames"
	);
}

#[test]
fn empty_plaintext_is_rejected_without_advancing_send_ratchets() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let server_state = server
		.ratchet_manager(response.kid)
		.unwrap()
		.send_state()
		.as_slice()
		.to_vec();
	let beacon_state = beacon
		.ratchet_manager(SERVER_KID)
		.unwrap()
		.send_state()
		.as_slice()
		.to_vec();

	assert!(server.encrypt_message(b"", response.kid).is_none());
	assert!(beacon.encrypt_message(b"", SERVER_KID).is_none());
	assert_eq!(
		server
			.ratchet_manager(response.kid)
			.unwrap()
			.send_state()
			.as_slice(),
		server_state
	);
	assert_eq!(
		beacon
			.ratchet_manager(SERVER_KID)
			.unwrap()
			.send_state()
			.as_slice(),
		beacon_state
	);

	let to_beacon = server.encrypt_message(b"non-empty", response.kid).unwrap();
	let to_server = beacon.encrypt_message(b"non-empty", SERVER_KID).unwrap();
	assert_eq!(
		beacon.decrypt_message(&to_beacon, SERVER_KID).unwrap(),
		b"non-empty"
	);
	assert_eq!(
		server.decrypt_message(&to_server, response.kid).unwrap(),
		b"non-empty"
	);
}

#[test]
fn commitment_corruption_is_rejected() {
	assert_server_frame_tampering_is_rejected(|ciphertext, _| {
		let commitment_start = ciphertext.len() - COMMITMENT_SIZE;
		ciphertext[commitment_start] ^= 0x01;
	});
}

#[test]
fn missing_tag_is_rejected() {
	assert_server_frame_tampering_is_rejected(|ciphertext, _| {
		let tag_start = ciphertext.len() - COMMITMENT_SIZE - TAG_SIZE;
		ciphertext.drain(tag_start..tag_start + TAG_SIZE);
	});
}

#[test]
fn missing_commitment_is_rejected() {
	assert_server_frame_tampering_is_rejected(|ciphertext, _| {
		ciphertext.truncate(ciphertext.len() - COMMITMENT_SIZE);
	});
}

#[test]
fn tag_corruption_is_rejected() {
	assert_server_frame_tampering_is_rejected(|ciphertext, _| {
		let tag_start = ciphertext.len() - COMMITMENT_SIZE - TAG_SIZE;
		ciphertext[tag_start] ^= 0x01;
	});
}

#[test]
fn swapped_tag_and_commitment_are_rejected() {
	assert_server_frame_tampering_is_rejected(|ciphertext, _| {
		let tag_start = ciphertext.len() - COMMITMENT_SIZE - TAG_SIZE;
		let commitment_start = ciphertext.len() - COMMITMENT_SIZE;
		let mut swapped = ciphertext[..tag_start].to_vec();
		swapped.extend_from_slice(&ciphertext[commitment_start..]);
		swapped.extend_from_slice(&ciphertext[tag_start..commitment_start]);
		*ciphertext = swapped;
	});
}

#[test]
fn beacon_rejects_tampered_registration_ephemeral_key() {
	let (mut beacon, response) = pending_registration(b"initial message");
	let mut parts = parse_kex_response(&response);
	parts.ephemeral_key[0] ^= 0x01;

	assert!(
		beacon
			.finish_registration(&serialize_kex_response(&parts))
			.is_none()
	);
}

#[test]
fn beacon_rejects_tampered_registration_kem_ciphertext() {
	let (mut beacon, response) = pending_registration(b"initial message");
	let mut parts = parse_kex_response(&response);
	parts.kem_ciphertext[0] ^= 0x01;

	assert!(
		beacon
			.finish_registration(&serialize_kex_response(&parts))
			.is_none()
	);
}

#[test]
fn failed_initial_ciphertext_clears_registration_state() {
	let (mut beacon, response) = pending_registration(b"initial message");
	let mut parts = parse_kex_response(&response);
	parts.app_ciphertext = corrupt_aead_ciphertext(&parts.app_ciphertext);

	assert!(
		beacon
			.finish_registration(&serialize_kex_response(&parts))
			.is_none()
	);
	assert!(beacon.get_onetime_pk().is_none());
	assert!(beacon.get_onetime_sk().is_none());
	assert!(beacon.pq_pk().is_none());
	assert!(beacon.pq_sk().is_none());
	assert!(beacon.associated_data(SERVER_KID).is_none());

	let ratchet = beacon.ratchet_manager(SERVER_KID).unwrap();
	assert_eq!(ratchet.send_state().as_slice(), &[0; KDF_STATE_SIZE]);
	assert_eq!(ratchet.recv_state().as_slice(), &[0; KDF_STATE_SIZE]);
}

#[test]
fn malformed_initial_ciphertext_is_rejected_without_panicking() {
	for malformed_app_ciphertext in [Vec::new(), serialize_crypto_frame(1, &[0xA5; 79])] {
		let (mut beacon, response) = pending_registration(b"initial message");
		let mut parts = parse_kex_response(&response);
		parts.app_ciphertext = malformed_app_ciphertext;

		let result = catch_unwind(AssertUnwindSafe(|| {
			beacon.finish_registration(&serialize_kex_response(&parts))
		}));
		assert!(matches!(result, Ok(None)));
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_sk().is_none());
		assert!(beacon.associated_data(SERVER_KID).is_none());
	}
}

#[test]
#[ignore = "known specification bug: KexResponse.keyId is not authenticated"]
fn beacon_rejects_tampered_registration_key_id() {
	let (mut beacon, response) = pending_registration(b"initial message");
	let mut parts = parse_kex_response(&response);
	parts.key_id = parts.key_id.wrapping_add(1);

	assert!(
		beacon
			.finish_registration(&serialize_kex_response(&parts))
			.is_none()
	);
}

#[test]
#[ignore = "known conformance bug: InitKex generation is not single-use"]
fn beacon_generates_only_one_registration_bundle() {
	let (_, mut beacon) = new_pair();
	assert!(beacon.get_registration_bundle().is_some());
	assert!(beacon.get_registration_bundle().is_none());
}

#[test]
#[ignore = "known protocol gap: replayed InitKex messages are accepted"]
fn server_rejects_replayed_registration_bundle() {
	let (mut server, mut beacon) = new_pair();
	let phase_1 = beacon.get_registration_bundle().unwrap();

	assert!(server.get_shared_secret(&phase_1).is_some());
	assert!(server.get_shared_secret(&phase_1).is_none());
}

#[test]
#[ignore = "known key-ID binding gap when one identity has multiple IDs"]
fn signed_message_cannot_be_relabelled_to_an_alias_key_id() {
	let (mut server, mut beacon) = new_pair();
	let phase_1 = beacon.get_registration_bundle().unwrap();
	let registration = server.get_shared_secret(&phase_1).unwrap();
	let duplicate_registration = RegistrationOutput {
		kem_ciphertext: registration.kem_ciphertext.clone(),
		derived_secret: registration.derived_secret.clone(),
		ephemeral: registration.ephemeral.clone(),
		public_key: registration.public_key.clone(),
	};
	let first = server
		.build_registration_response(duplicate_registration, None)
		.unwrap();
	let alias = server
		.build_registration_response(registration, None)
		.unwrap();
	beacon.finish_registration(&first.serialized).unwrap();

	let signed = beacon
		.encrypt_and_sign(b"authenticated beacon message", SERVER_KID)
		.unwrap();
	let relabelled = rewrite_protogram_key_id(&signed, alias.kid);

	assert!(server.decrypt_signed(&relabelled).is_none());
}
