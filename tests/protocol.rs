use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};

const SERVER_KID: u64 = 0;

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
	corrupted.set_s_to_b(frame.get_s_to_b());
	corrupted.set_cipher_text(&ciphertext);

	let mut serialized = vec![];
	capnp::serialize::write_message(&mut serialized, message.borrow_inner()).unwrap();
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
	register_beacon(&mut server, &mut beacon, None);
	let message = b"signed beacon to server";
	let ciphertext = beacon.encrypt_message(message, SERVER_KID).unwrap();
	let signed = beacon.sign_message(&ciphertext).unwrap();

	assert_eq!(server.decrypt_signed(&signed).unwrap(), message);
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
	assert_eq!(
		beacon.decrypt_message(&update.data, SERVER_KID).unwrap(),
		message
	);
}

#[test]
fn decrypt_and_update_returns_the_advanced_receive_state() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"beacon to server with updated state";
	let ciphertext = beacon.encrypt_message(message, SERVER_KID).unwrap();
	let (send_state_before, recv_state_before) = {
		let ratchet = server.ratchet_manager(response.kid).unwrap();
		(
			ratchet.send_state().as_slice().to_vec(),
			ratchet.recv_state().as_slice().to_vec(),
		)
	};

	let update = server
		.decrypt_and_update(&ciphertext, response.kid)
		.unwrap();
	let ratchet = server.ratchet_manager(response.kid).unwrap();

	assert_eq!(update.kid, response.kid);
	assert_eq!(update.data, message);
	assert_eq!(update.key.as_slice(), ratchet.recv_state().as_slice());
	assert_ne!(update.key.as_slice(), recv_state_before);
	assert_eq!(ratchet.send_state().as_slice(), send_state_before);
}
