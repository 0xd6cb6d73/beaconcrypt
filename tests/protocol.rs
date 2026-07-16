use beaconcrypt::*;

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
	assert_eq!(plaintext, initial_message.unwrap_or(&[]));
	phase_2
}

#[test]
fn registration_can_omit_initial_message() {
	let (mut server, mut beacon) = new_pair();

	let response = register_beacon(&mut server, &mut beacon, None);

	assert_eq!(response.kid, 1);
}

#[test]
fn beacon_can_encrypt_to_server() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"beacon to server";

	let ciphertext = beacon
		.encrypt_message(message.as_slice(), false, SERVER_KID)
		.unwrap();
	let plaintext = server
		.decrypt_message(&ciphertext, response.kid, false)
		.unwrap();

	assert_eq!(plaintext, message);
}

#[test]
fn beacon_can_encrypt_to_server_signed() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"signed beacon to server";

	let ciphertext = beacon
		.encrypt_message(message.as_slice(), false, SERVER_KID)
		.unwrap();
	let signed = beacon.sign_message(&ciphertext).unwrap();
	let verified = server.verify_signature(&signed).unwrap();
	let plaintext = server
		.decrypt_message(&verified.data, verified.key_id, false)
		.unwrap();

	assert_eq!(verified.key_id, response.kid);
	assert_eq!(plaintext, message);
}

#[test]
fn signed_server_message_rejects_tampering() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let ciphertext = server
		.encrypt_message(b"server to beacon", true, response.kid)
		.unwrap();
	let mut signed = server.sign_message(&ciphertext).unwrap();
	let last = signed.len() - 1;
	signed[last] ^= 0x01;

	assert!(beacon.verify_signature(&signed).is_none());
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
		.encrypt_message(b"for b1 only", true, b1_response.kid)
		.unwrap();

	assert!(b2.decrypt_message(&ciphertext, SERVER_KID, true).is_none());
}

#[test]
fn ciphertext_cannot_be_replayed() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"one shot";

	let ciphertext = server.encrypt_message(message, true, response.kid).unwrap();
	let first = beacon
		.decrypt_message(&ciphertext, SERVER_KID, true)
		.unwrap();

	assert_eq!(first, message);
	assert!(
		beacon
			.decrypt_message(&ciphertext, SERVER_KID, true)
			.is_none()
	);
}
