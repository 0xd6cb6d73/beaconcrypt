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
	let mut server: BeaconCryptPqxdh = ProviderServer::from_state(state);
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
	assert_eq!(json["identity_key"][0], json!(u8::from(SignType::Ed25519)));
	assert_eq!(json["identity_key"][1], json!(14));
	assert_eq!(
		json["identity_key"][2].as_array().unwrap().len(),
		crypto_sign::SEEDBYTES
	);
	assert_eq!(json["identity_key_kid"], json!(0));
	assert_eq!(json["server_kid"], json!(2));
	let consumed = json["consumed_registrations"].as_array().unwrap();
	assert_eq!(consumed.len(), 2);
	assert!(
		consumed
			.iter()
			.all(|entry| entry.as_array().unwrap().len() == 64)
	);
	let consumed_bytes = consumed
		.iter()
		.map(|entry| {
			entry
				.as_array()
				.unwrap()
				.iter()
				.map(|byte| byte.as_u64().unwrap() as u8)
				.collect::<Vec<_>>()
		})
		.collect::<Vec<_>>();
	assert!(
		consumed_bytes
			.windows(2)
			.all(|pair| pair[0].as_slice() < pair[1].as_slice())
	);
	for kid in ["1", "2"] {
		let encoded_pk = json["known_ids"][kid]["pk"].as_array().unwrap();
		assert_eq!(encoded_pk.len(), crypto_sign::PUBLICKEYBYTES + 1);
		assert_eq!(encoded_pk[0], json!(u8::from(SignType::Ed25519)));
		assert!(json["known_ids"][kid]["ratchet"].is_object());
	}

	let mut restored: BeaconCryptPqxdh = ProviderServer::from_state(state);
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
	let cached = encoded["known_ids"]["1"]["ratchet"]["recv_past"]
		.as_object()
		.unwrap();
	assert_eq!(cached.len(), 2);
	assert!(cached.contains_key("1"));
	assert!(cached.contains_key("2"));

	let mut restored: BeaconCryptPqxdh = ProviderServer::from_state(state);
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
	wrong_key_type["known_ids"]["1"]["pk"][0] = json!(u8::from(SignType::MlDsa87));
	let mut short_key = parsed.clone();
	short_key["known_ids"]["1"]["pk"]
		.as_array_mut()
		.unwrap()
		.pop();
	let mut malformed_ratchet = parsed.clone();
	malformed_ratchet["known_ids"]["1"]["ratchet"]["send_key"][0] = json!(0);
	let mut legacy_send_past = parsed.clone();
	legacy_send_past["known_ids"]["1"]["ratchet"]["send_past"] = json!({});
	let mut malformed_identity = parsed.clone();
	malformed_identity["identity_key"]
		.as_array_mut()
		.unwrap()
		.pop();
	let mut wrong_identity_system = parsed.clone();
	wrong_identity_system["identity_key"][0] = json!(0);
	let mut wrong_identity_role = parsed.clone();
	wrong_identity_role["identity_key"][1] = json!(8);
	let mut invalid_identity_kid = parsed.clone();
	invalid_identity_kid["identity_key_kid"] = json!(2);
	let mut regressed_server_kid = parsed.clone();
	regressed_server_kid["server_kid"] = json!(0);
	let mut short_registration_id = parsed.clone();
	short_registration_id["consumed_registrations"][0]
		.as_array_mut()
		.unwrap()
		.pop();
	let mut duplicate_registration_id = parsed.clone();
	let registration_id = duplicate_registration_id["consumed_registrations"][0].clone();
	duplicate_registration_id["consumed_registrations"]
		.as_array_mut()
		.unwrap()
		.push(registration_id);
	let mut missing_registration_history = parsed.clone();
	missing_registration_history
		.as_object_mut()
		.unwrap()
		.remove("consumed_registrations");
	let mut incomplete_registration_history = parsed.clone();
	incomplete_registration_history["consumed_registrations"] = json!([]);

	for malformed in [
		wrong_key_type,
		short_key,
		malformed_ratchet,
		legacy_send_past,
		malformed_identity,
		wrong_identity_system,
		wrong_identity_role,
		invalid_identity_kid,
		regressed_server_kid,
		short_registration_id,
		duplicate_registration_id,
		missing_registration_history,
		incomplete_registration_history,
	] {
		let malformed = serde_json::to_string(&malformed).unwrap();
		assert!(
			std::panic::catch_unwind(|| {
				let _: BeaconCryptPqxdh = ProviderServer::from_state(malformed);
			})
			.is_err()
		);
	}

	let identity_key = serde_json::to_string(&parsed["identity_key"]).unwrap();
	let principal = serde_json::to_string(&parsed["known_ids"]["1"]).unwrap();
	let consumed_registrations = serde_json::to_string(&parsed["consumed_registrations"]).unwrap();
	let duplicate_kid = format!(
		"{{\"identity_key\":{identity_key},\"identity_key_kid\":0,\
		 \"server_kid\":1,\"known_ids\":\
		 {{\"1\":{principal},\"1\":{principal}}},\
		 \"consumed_registrations\":{consumed_registrations}}}"
	);
	assert!(
		std::panic::catch_unwind(|| {
			let _: BeaconCryptPqxdh = ProviderServer::from_state(duplicate_kid);
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
	let identity = server.identity_pk().to_owned();
	let state = server.export_state().unwrap();
	let encoded: Value = serde_json::from_str(&state).unwrap();
	assert_eq!(encoded["identity_key_kid"], json!(7));
	assert_eq!(encoded["server_kid"], json!(7));
	assert_eq!(encoded["known_ids"], json!({}));
	assert_eq!(encoded["consumed_registrations"], json!([]));

	let restored: BeaconCryptPqxdh = ProviderServer::from_state(state);
	assert_eq!(restored.identity_pk(), &identity);
	assert_eq!(restored.identity_key_kid(), 7);
	assert_eq!(restored.server_kid(), 7);
	assert!(restored.pk_by_kid(1).is_none());
}

#[test]
fn state_counter_survives_deleting_the_highest_known_id() {
	let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	test_register_pqxdh_beacon(&mut server, &mut b1);
	test_register_pqxdh_beacon(&mut server, &mut b2);
	server.delete_known_kid(2);

	let state = server.export_state().unwrap();
	let mut restored: BeaconCryptPqxdh = ProviderServer::from_state(state);
	assert_eq!(restored.server_kid(), 2);

	let mut b3 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
	test_register_pqxdh_beacon(&mut restored, &mut b3);
	assert_eq!(restored.server_kid(), 3);
	assert!(restored.pk_by_kid(3).is_some());
}

#[test]
fn fallible_state_restore_rejects_invalid_state() {
	let server = BeaconCryptPqxdh::new(false, 0, None, None);
	let mut state: Value = serde_json::from_str(&server.export_state().unwrap()).unwrap();
	state.as_object_mut().unwrap().remove("identity_key_kid");

	assert!(<BeaconCryptPqxdh as ProviderServer>::try_from_state(&state.to_string()).is_none());
	assert!(<BeaconCryptPqxdh as ProviderServer>::try_from_state("not JSON").is_none());
	assert!(<BeaconCryptPqxdh as ProviderServer>::try_from_state("{}").is_none());
}
