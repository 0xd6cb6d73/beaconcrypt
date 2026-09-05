use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};

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

fn response_with_frame(response: &RegResponse, frame: &[u8], assigned: u64) -> Vec<u8> {
	let reader =
		capnp::serialize_packed::read_message(response.serialized.as_slice(), ReaderOptions::new())
			.unwrap();
	let typed = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
	let original = typed.get().unwrap();
	let mut builder = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
	let mut rewritten = builder.init_root();
	rewritten.set_identity_key(original.get_identity_key().unwrap());
	rewritten.set_ephemeral_key(original.get_ephemeral_key().unwrap());
	rewritten.set_kem_cipher_text(original.get_kem_cipher_text().unwrap());
	rewritten.set_key_id(assigned);
	rewritten.set_app_cipher_text(frame);
	let mut serialized = vec![];
	capnp::serialize_packed::write_message(&mut serialized, builder.borrow_inner()).unwrap();
	serialized
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
fn registration_accepts_later_bound_records_and_preserves_skipped_keys() {
	for sequence in [2, 3, 51] {
		let (mut server, mut beacon, original) = pending();
		let payload = bound_payload(original.kid, b"later completion");
		let (skipped, target) = send_until(&mut server, original.kid, sequence, &payload);
		let candidate = response_with_frame(&original, &target, original.kid);
		assert_ne!(candidate, original.serialized);
		assert_eq!(
			beacon.finish_registration(&candidate).unwrap(),
			b"later completion"
		);
		let status = beacon.ratchet_status().unwrap();
		assert_eq!(status.send_sequence(), 0);
		assert_eq!(status.receive_sequence(), sequence);
		assert_eq!(u64::from(status.receive_cache_len()), sequence - 1);
		assert!(beacon.decrypt_message(&target).is_none());
		assert_eq!(beacon.ratchet_status(), Some(status));
		assert!(beacon.finish_registration(&original.serialized).is_none());
		for frame in skipped.iter().rev() {
			assert_eq!(
				beacon.decrypt_message(frame).unwrap().plaintext,
				b"delayed application record"
			);
			let after = beacon.ratchet_status();
			assert!(beacon.decrypt_message(frame).is_none());
			assert_eq!(beacon.ratchet_status(), after);
		}
		// Sequence one is also retained. A normal receive returns the complete authenticated prefix and payload.
		let original_reader = capnp::serialize_packed::read_message(
			original.serialized.as_slice(),
			ReaderOptions::new(),
		)
		.unwrap();
		let original_typed =
			TypedReader::<_, phase2_capnp::kex_response::Owned>::new(original_reader);
		let first_frame = original_typed.get().unwrap().get_app_cipher_text().unwrap();
		assert_eq!(
			beacon.decrypt_message(first_frame).unwrap().plaintext,
			bound_payload(original.kid, b"original response")
		);
		assert_eq!(beacon.ratchet_status().unwrap().receive_cache_len(), 0);
		let reply = beacon
			.encrypt_message(b"established after later completion")
			.unwrap();
		assert_eq!(
			server.decrypt_message(&reply).unwrap().plaintext,
			b"established after later completion"
		);
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
		let mut frame = target.to_vec();
		if invalid == 4 {
			let reader =
				capnp::serialize::read_message(frame.as_slice(), ReaderOptions::new()).unwrap();
			let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
			let original_frame = typed.get().unwrap();
			let mut ciphertext = original_frame.get_cipher_text().unwrap().to_vec();
			ciphertext[0] ^= 1;
			let mut builder = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
			let mut changed = builder.init_root();
			changed.set_seq(original_frame.get_seq());
			changed.set_key_id(original_frame.get_key_id());
			changed.set_cipher_text(&ciphertext);
			frame.clear();
			capnp::serialize::write_message(&mut frame, builder.borrow_inner()).unwrap();
		}
		let candidate = response_with_frame(&original, &frame, assigned);
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
fn later_completion_authenticates_the_payload_prefix_not_the_original_routing_id() {
	let (mut server, mut beacon, original) = pending();
	let relabelled = original.kid + 1;
	let (_, target) = send_until(
		&mut server,
		original.kid,
		3,
		&bound_payload(relabelled, b"authentic application payload"),
	);
	let candidate = response_with_frame(&original, &target, relabelled);
	assert_eq!(
		beacon.finish_registration(&candidate).unwrap(),
		b"authentic application payload"
	);
	// This genuine same-session record establishes the payload's claimed routing ID, so it does not prove agreement on the server's originally allocated ID.
	assert_eq!(beacon.ratchet_status().unwrap().receive_sequence(), 3);
	let outgoing = beacon
		.encrypt_message(b"different numeric sender ID")
		.unwrap();
	assert!(server.decrypt_message(&outgoing).is_none());
}
