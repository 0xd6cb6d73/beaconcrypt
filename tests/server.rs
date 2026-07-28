use beaconcrypt::*;
use libsodium_rs::crypto_sign;
use serde_json::{Value, json};

fn test_register_pqxdh_beacon(
	server: &mut BeaconCryptPqxdh,
	beacon: &mut BeaconCryptPqxdh,
) -> Vec<u8> {
	let message = [0xFFu8; 32];

	let phase_1 = beacon.get_registration_bundle().unwrap();
	let reg_out = server.get_shared_secret(&phase_1).unwrap();
	let phase2 = server
		.build_registration_response(reg_out, Some(&message))
		.unwrap();
	beacon.finish_registration(&phase2.serialized).unwrap()
}

fn assert_exchange(
	server: &mut BeaconCryptPqxdh,
	beacon: &mut BeaconCryptPqxdh,
	kid: u64,
	server_message: &[u8],
	beacon_message: &[u8],
) {
	let encrypted = server.encrypt_message(server_message, kid).unwrap();
	assert_eq!(
		beacon.decrypt_message(&encrypted).unwrap().plaintext,
		server_message
	);

	let encrypted = beacon
		.encrypt_message(beacon_message, beacon.server_kid())
		.unwrap();
	assert_eq!(
		server.decrypt_message(&encrypted).unwrap().plaintext,
		beacon_message
	);
}

#[test]
fn server_from_seed() {
	let empty = [0u8; ED25519_SEED_SIZE];
	let seeded = crypto_sign::KeyPair::from_seed(&empty).unwrap();
	let server = BeaconCryptPqxdh::new(false, 0, None, Some(&empty));
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
	let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
	let server_id = server.identity_pk().to_owned();

	let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let b1_reg = test_register_pqxdh_beacon(&mut server, &mut b1);
	let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let b2_reg = test_register_pqxdh_beacon(&mut server, &mut b2);

	assert_eq!(b1_reg, b2_reg);
}

#[test]
fn recreated_server_decrypts_beacon_response() {
	let seed = [0x41; ED25519_SEED_SIZE];
	let mut server = BeaconCryptPqxdh::new(false, 0, None, Some(&seed));
	let server_id = server.identity_pk().to_owned();
	let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);

	test_register_pqxdh_beacon(&mut server, &mut beacon);
	let request = server.encrypt_message(b"request", 1).unwrap();
	assert_eq!(
		beacon.decrypt_message(&request).unwrap().plaintext,
		b"request"
	);

	let state = server.export_state().unwrap();
	drop(server);

	let response = beacon
		.encrypt_message(b"response", beacon.server_kid())
		.unwrap();
	let mut server: BeaconCryptPqxdh = ProviderServer::from_state(0, Some(&seed), state);
	assert_eq!(
		server.decrypt_message(&response).unwrap().plaintext,
		b"response"
	);
}

#[test]
fn known_ids_round_trip_and_continue_each_session() {
	let seed = [0x51; ED25519_SEED_SIZE];
	let mut server = BeaconCryptPqxdh::new(false, 0, None, Some(&seed));
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);

	test_register_pqxdh_beacon(&mut server, &mut b1);
	test_register_pqxdh_beacon(&mut server, &mut b2);
	assert_exchange(&mut server, &mut b1, 1, b"server one", b"beacon one");
	assert_exchange(&mut server, &mut b2, 2, b"server two", b"beacon two");

	let state = server.export_state().unwrap();
	let json: Value = serde_json::from_str(&state).unwrap();
	for kid in ["1", "2"] {
		let encoded_pk = json[kid]["pk"].as_array().unwrap();
		assert_eq!(encoded_pk.len(), crypto_sign::PUBLICKEYBYTES + 1);
		assert_eq!(encoded_pk[0], json!(u8::from(SignType::Ed25519)));
		assert!(json[kid]["ratchet"].is_object());
	}

	let mut restored: BeaconCryptPqxdh = ProviderServer::from_state(0, Some(&seed), state);
	assert_eq!(restored.identity_pk(), &server_id);
	assert_eq!(restored.server_kid(), 2);
	assert_eq!(restored.pk_by_kid(1), server.pk_by_kid(1));
	assert_eq!(restored.pk_by_kid(2), server.pk_by_kid(2));

	assert_exchange(
		&mut restored,
		&mut b1,
		1,
		b"server one restored",
		b"beacon one restored",
	);
	assert_exchange(
		&mut restored,
		&mut b2,
		2,
		b"server two restored",
		b"beacon two restored",
	);

	let mut b3 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	test_register_pqxdh_beacon(&mut restored, &mut b3);
	assert_eq!(restored.server_kid(), 3);
	assert!(restored.pk_by_kid(3).is_some());
}

#[test]
fn known_ids_round_trip_preserves_cached_out_of_order_receive_keys() {
	let seed = [0x71; ED25519_SEED_SIZE];
	let mut server = BeaconCryptPqxdh::new(false, 0, None, Some(&seed));
	let server_id = server.identity_pk().to_owned();
	let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	test_register_pqxdh_beacon(&mut server, &mut beacon);

	let first = beacon.encrypt_message(b"first", 0).unwrap();
	let second = beacon.encrypt_message(b"second", 0).unwrap();
	let third = beacon.encrypt_message(b"third", 0).unwrap();
	assert_eq!(server.decrypt_message(&third).unwrap().plaintext, b"third");

	let state = server.export_state().unwrap();
	let encoded: Value = serde_json::from_str(&state).unwrap();
	let cached = encoded["1"]["ratchet"]["recv_past"].as_object().unwrap();
	assert_eq!(cached.len(), 2);
	assert!(cached.contains_key("1"));
	assert!(cached.contains_key("2"));

	let mut restored: BeaconCryptPqxdh = ProviderServer::from_state(0, Some(&seed), state);
	assert_eq!(
		restored.decrypt_message(&first).unwrap().plaintext,
		b"first"
	);
	assert_eq!(
		restored.decrypt_message(&second).unwrap().plaintext,
		b"second"
	);
}

#[test]
fn invalid_known_ids_state_is_rejected() {
	let seed = [0x61; ED25519_SEED_SIZE];
	let mut server = BeaconCryptPqxdh::new(false, 0, None, Some(&seed));
	let server_id = server.identity_pk().to_owned();
	let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	test_register_pqxdh_beacon(&mut server, &mut beacon);

	let state = server.export_state().unwrap();
	let parsed: Value = serde_json::from_str(&state).unwrap();

	let mut wrong_key_type = parsed.clone();
	wrong_key_type["1"]["pk"][0] = json!(u8::from(SignType::MlDsa87));
	let mut short_key = parsed.clone();
	short_key["1"]["pk"].as_array_mut().unwrap().pop();
	let mut malformed_ratchet = parsed;
	malformed_ratchet["1"]["ratchet"]["send_key"][0] = json!(0);

	for malformed in [wrong_key_type, short_key, malformed_ratchet] {
		let malformed = serde_json::to_string(&malformed).unwrap();
		assert!(
			std::panic::catch_unwind(|| {
				let _: BeaconCryptPqxdh = ProviderServer::from_state(0, Some(&seed), malformed);
			})
			.is_err()
		);
	}

	let entry = &state[1..state.len() - 1];
	let duplicate_kid = format!("{{{entry},{entry}}}");
	assert!(
		std::panic::catch_unwind(|| {
			let _: BeaconCryptPqxdh = ProviderServer::from_state(0, Some(&seed), duplicate_kid);
		})
		.is_err()
	);

	assert_exchange(
		&mut server,
		&mut beacon,
		1,
		b"server remains live",
		b"beacon remains live",
	);
}

#[test]
fn empty_known_ids_state_round_trips_without_lowering_the_kid_counter() {
	let server = BeaconCryptPqxdh::new(false, 7, None, None);
	let state = server.export_state().unwrap();
	assert_eq!(state, "{}");

	let restored: BeaconCryptPqxdh = ProviderServer::from_state(7, None, state);
	assert_eq!(restored.server_kid(), 7);
	assert!(restored.pk_by_kid(1).is_none());
}

#[test]
fn fallible_state_restore_rejects_invalid_seed_and_state() {
	let short_seed = [0u8; ED25519_SEED_SIZE - 1];
	assert!(
		<BeaconCryptPqxdh as ProviderServer>::try_from_state(0, Some(&short_seed), "{}").is_none()
	);
	assert!(<BeaconCryptPqxdh as ProviderServer>::try_from_state(0, None, "not JSON").is_none());
}
