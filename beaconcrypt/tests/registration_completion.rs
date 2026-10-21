use beaconcrypt::*;
use beaconcrypt_parse::{KexResponse, decode_frame, decode_response};

mod common;

const SERVER_KID: u64 = 0;

fn pending() -> (Server, Beacon, RegResponse) {
	let mut server = Server::new(SERVER_KID, None);
	let mut beacon = Beacon::new(SERVER_KID, server.identity_pk().as_bytes());
	let init = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&init).unwrap();
	let response = server
		.build_registration_response(accepted, Some(b"original response"))
		.unwrap();
	(server, beacon, response)
}

fn response_with_ciphertext(response: &RegResponse, ciphertext: &[u8], assigned: u64) -> Vec<u8> {
	let original = decode_response(&response.serialized).unwrap();
	common::encode_response(KexResponse {
		identity_key: original.identity_key,
		ephemeral_key: original.ephemeral_key,
		kem_cipher_text: original.kem_cipher_text,
		key_id: assigned,
		app_cipher_text: ciphertext,
	})
}

fn response_with_frame(response: &RegResponse, frame: &[u8], assigned: u64) -> Vec<u8> {
	let ciphertext = decode_frame(frame).unwrap().cipher_text;
	response_with_ciphertext(response, ciphertext, assigned)
}

fn bound_payload(assigned: u64, plaintext: &[u8]) -> Vec<u8> {
	let mut payload = assigned.to_le_bytes().to_vec();
	payload.extend_from_slice(plaintext);
	payload
}

fn send_until(
	server: &mut Server,
	kid: u64,
	sequence: u64,
	payload: &[u8],
) -> (Vec<Encrypted>, Encrypted) {
	let mut skipped = vec![];
	for _ in 2..sequence {
		skipped.push(
			server
				.encrypt_message(b"delayed application record", kid)
				.unwrap(),
		);
	}
	let target = server.encrypt_message(payload, kid).unwrap();
	(skipped, target)
}

#[test]
fn registration_rejects_every_otherwise_admissible_later_record_and_aborts() {
	for sequence in 2..=51 {
		let (mut server, mut beacon, original) = pending();
		let application: Vec<u8> = (0..=255).map(|byte| byte ^ sequence as u8).collect();
		let payload = bound_payload(original.kid, &application);
		let (_, target) = send_until(&mut server, original.kid, sequence, &payload);
		let candidate = response_with_frame(&original, &target, original.kid);
		let server_status = server.ratchet_status(original.kid);
		assert_ne!(candidate, original.serialized);
		assert!(
			beacon.finish_registration(&candidate).is_none(),
			"sequence {sequence}"
		);
		assert!(beacon.ratchet_status().is_none());
		assert!(beacon.associated_data().is_none());
		assert_eq!(beacon.identity_key_kid(), SERVER_KID);
		assert!(beacon.get_prekey_sk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_sk().is_none());
		assert!(beacon.decrypt_message(&target).is_none());
		assert!(beacon.finish_registration(&original.serialized).is_none());
		assert!(
			beacon
				.encrypt_message(b"must remain unestablished")
				.is_none()
		);
		assert!(beacon.get_registration_bundle().is_none());
		assert_eq!(server.ratchet_status(original.kid), server_status);
	}
}

#[test]
fn registration_rejects_later_invalid_completions_and_aborts() {
	for invalid in 0..5 {
		let (mut server, mut beacon, original) = pending();
		let (sequence, assigned, payload) = match invalid {
			0 => (
				3,
				original.kid,
				bound_payload(original.kid + 1, b"wrong authenticated binding"),
			),
			1 => (3, original.kid, b"short".to_vec()),
			2 => (
				3,
				original.kid + 1,
				bound_payload(original.kid, b"wrong outer binding"),
			),
			3 => (
				52,
				original.kid,
				bound_payload(original.kid, b"cache bound exceeded"),
			),
			_ => (
				3,
				original.kid,
				bound_payload(original.kid, b"ciphertext corrupted"),
			),
		};
		let (_, target) = send_until(&mut server, original.kid, sequence, &payload);
		let mut ciphertext = decode_frame(&target).unwrap().cipher_text.to_vec();
		if invalid == 4 {
			ciphertext[0] ^= 1;
		}
		let candidate = response_with_ciphertext(&original, &ciphertext, assigned);
		assert!(
			beacon.finish_registration(&candidate).is_none(),
			"invalid case {invalid}"
		);
		assert!(beacon.ratchet_status().is_none());
		assert!(beacon.finish_registration(&original.serialized).is_none());
		assert!(
			beacon
				.encrypt_message(b"must remain unestablished")
				.is_none()
		);
		assert!(beacon.get_registration_bundle().is_none());
	}
}

#[test]
fn registration_rejects_a_genuine_later_record_from_another_session() {
	let (mut server, mut beacon, original) = pending();
	let mut other = Beacon::new(SERVER_KID, server.identity_pk().as_bytes());
	let other_init = other.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&other_init).unwrap();
	let other_response = server.build_registration_response(accepted, None).unwrap();
	let (_, cross_session_frame) = send_until(
		&mut server,
		other_response.kid,
		3,
		&bound_payload(original.kid, b"same claimed binding, wrong session"),
	);
	let candidate = response_with_frame(&original, &cross_session_frame, original.kid);
	assert!(beacon.finish_registration(&candidate).is_none());
	assert!(beacon.ratchet_status().is_none());
	assert!(beacon.finish_registration(&original.serialized).is_none());
}

#[test]
fn registration_rejects_later_record_substitution_even_with_a_matching_relabelled_prefix() {
	let (mut server, mut beacon, original) = pending();
	let relabelled = original.kid + 1;
	let (_, target) = send_until(
		&mut server,
		original.kid,
		3,
		&bound_payload(relabelled, b"authentic application payload"),
	);
	let candidate = response_with_frame(&original, &target, relabelled);
	assert!(beacon.finish_registration(&candidate).is_none());
	assert!(beacon.ratchet_status().is_none());
	assert_eq!(beacon.identity_key_kid(), SERVER_KID);
	assert!(beacon.finish_registration(&original.serialized).is_none());
}

#[test]
fn registration_accepts_the_original_first_record_and_only_consumes_its_target() {
	let (mut server, mut beacon, original) = pending();
	assert_eq!(
		beacon.finish_registration(&original.serialized).unwrap(),
		b"original response"
	);
	let status = beacon.ratchet_status().unwrap();
	assert_eq!(status.send_sequence(), 0);
	assert_eq!(status.receive_sequence(), 1);
	assert_eq!(status.receive_cache_len(), 0);
	let future = server
		.encrypt_message(b"first subsequent record", original.kid)
		.unwrap();
	assert_eq!(
		beacon.decrypt_message(&future).unwrap().plaintext,
		b"first subsequent record"
	);
	assert!(beacon.decrypt_message(&future).is_none());
}

#[test]
fn established_beacon_still_accepts_out_of_order_records_and_rejects_replays() {
	let (mut server, mut beacon, original) = pending();
	assert!(beacon.finish_registration(&original.serialized).is_some());
	let second = server.encrypt_message(b"second", original.kid).unwrap();
	let third = server.encrypt_message(b"third", original.kid).unwrap();
	let opened = beacon.decrypt_message(&third).unwrap();
	assert_eq!(opened.seq, 3);
	assert_eq!(opened.plaintext, b"third");
	assert_eq!(beacon.ratchet_status().unwrap().receive_cache_len(), 1);
	assert_eq!(
		beacon.decrypt_message(&second).unwrap().plaintext,
		b"second"
	);
	assert_eq!(beacon.ratchet_status().unwrap().receive_cache_len(), 0);
	let status = beacon.ratchet_status();
	assert!(beacon.decrypt_message(&second).is_none());
	assert!(beacon.decrypt_message(&third).is_none());
	assert_eq!(beacon.ratchet_status(), status);
}

#[test]
fn registration_rejects_frame_wrappers_malformed_bytes_and_plaintext() {
	for kind in 0..3 {
		let (_server, mut beacon, original) = pending();
		let ciphertext = match kind {
			0 => common::encode_frame(beaconcrypt_parse::CryptoFrame {
				seq: 1,
				key_id: SERVER_KID,
				cipher_text: decode_response(&original.serialized)
					.unwrap()
					.app_cipher_text,
			}),
			1 => vec![255; 3],
			_ => bound_payload(original.kid, b"unframed plaintext"),
		};
		let candidate = response_with_ciphertext(&original, &ciphertext, original.kid);
		assert!(
			beacon.finish_registration(&candidate).is_none(),
			"kind {kind}"
		);
		assert!(beacon.ratchet_status().is_none());
		assert!(beacon.finish_registration(&original.serialized).is_none());
	}
}

#[test]
fn registration_rejects_trailing_bytes_in_outer_response_and_ciphertext_and_aborts() {
	for in_ciphertext in [false, true] {
		for suffix_kind in 0..3 {
			let (server, mut beacon, original) = pending();
			let response = decode_response(&original.serialized).unwrap();
			let input = if in_ciphertext {
				response.app_cipher_text
			} else {
				&original.serialized
			};
			let suffix = match suffix_kind {
				0 => &[0u8][..],
				1 => &[0u8; 8][..],
				_ => input,
			};
			let mut malformed = input.to_vec();
			malformed.extend_from_slice(suffix);
			let candidate = if in_ciphertext {
				response_with_ciphertext(&original, &malformed, original.kid)
			} else {
				malformed
			};
			let server_status = server.ratchet_status(original.kid);
			assert!(beacon.finish_registration(&candidate).is_none());
			assert!(beacon.ratchet_status().is_none());
			assert!(beacon.associated_data().is_none());
			assert_eq!(beacon.identity_key_kid(), SERVER_KID);
			assert!(beacon.get_prekey_sk().is_none());
			assert!(beacon.get_onetime_sk().is_none());
			assert!(beacon.pq_sk().is_none());
			assert!(beacon.finish_registration(&original.serialized).is_none());
			assert!(
				beacon
					.encrypt_message(b"must remain unestablished")
					.is_none()
			);
			assert!(beacon.get_registration_bundle().is_none());
			assert_eq!(server.ratchet_status(original.kid), server_status);
		}
	}
}
