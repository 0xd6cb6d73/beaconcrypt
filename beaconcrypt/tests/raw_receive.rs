use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};

const SERVER_ID: u64 = 7;

fn register(server: &mut Server) -> (Beacon, u64) {
	let mut beacon = Beacon::new(SERVER_ID, server.identity_pk().as_bytes());
	let request = beacon.get_registration_bundle().unwrap();
	let pending = server.get_shared_secret(&request).unwrap();
	let response = server.build_registration_response(pending, None).unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized),
		Some(vec![0xff])
	);
	(beacon, response.kid)
}

fn fields(raw: &[u8]) -> (u64, u64, Vec<u8>) {
	let reader = capnp::serialize::read_message(raw, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
	let frame = typed.get().unwrap();
	(
		frame.get_seq(),
		frame.get_key_id(),
		frame.get_cipher_text().unwrap().to_vec(),
	)
}

fn frame(sequence: u64, sender: u64, payload: &[u8]) -> Vec<u8> {
	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut frame = message.init_root();
	frame.set_seq(sequence);
	frame.set_key_id(sender);
	frame.set_cipher_text(payload);
	let mut result = Vec::new();
	capnp::serialize::write_message(&mut result, message.borrow_inner()).unwrap();
	result
}

fn invalid_variants(raw: &[u8]) -> Vec<Vec<u8>> {
	let (sequence, sender, payload) = fields(raw);
	let mut attempts: Vec<_> = (0..raw.len())
		.map(|length| raw[..length].to_vec())
		.collect();
	for suffix in [&[0u8][..], &[0u8; 8][..], raw] {
		let mut appended = raw.to_vec();
		appended.extend_from_slice(suffix);
		attempts.push(appended);
	}
	attempts.push(frame(0, sender, &payload));
	attempts.push(frame(u64::MAX, sender, &payload));
	attempts.push(frame(sequence, sender + 1, &payload));
	for length in 0..=80 {
		attempts.push(frame(sequence, sender, &payload[..length]));
	}
	for index in [0, payload.len() - 80, payload.len() - 64, payload.len() - 1] {
		let mut corrupted = payload.clone();
		corrupted[index] ^= 1;
		attempts.push(frame(sequence, sender, &corrupted));
	}
	attempts
}

#[test]
fn raw_rejections_preserve_future_and_cached_keys() {
	let mut server = Server::new(SERVER_ID, None);
	let (mut beacon, kid) = register(&mut server);
	let second = server.encrypt_message(b"second", kid).unwrap();
	let third = server.encrypt_message(b"third", kid).unwrap();
	let fourth = server.encrypt_message(b"fourth", kid).unwrap();

	// Every raw rejection preserves the receive status and the future authentic message.
	let before = beacon.ratchet_status().unwrap();
	for attempt in invalid_variants(&third.ciphertext) {
		assert!(beacon.decrypt_message(&attempt).is_none());
		assert_eq!(beacon.ratchet_status().unwrap(), before);
	}
	let accepted = beacon.decrypt_message(&third.ciphertext).unwrap();
	assert_eq!(
		(accepted.plaintext.as_slice(), accepted.key_id, accepted.seq),
		(b"third".as_slice(), SERVER_ID, third.seq)
	);
	assert_eq!(beacon.ratchet_status().unwrap().receive_cache_len(), 1);

	// The same rejections also preserve a skipped key after a successful future receive.
	let before = beacon.ratchet_status().unwrap();
	for attempt in invalid_variants(&second.ciphertext) {
		assert!(beacon.decrypt_message(&attempt).is_none());
		assert_eq!(beacon.ratchet_status().unwrap(), before);
	}
	assert_eq!(
		beacon
			.decrypt_message(&second.ciphertext)
			.unwrap()
			.plaintext,
		b"second"
	);
	assert_eq!(
		beacon
			.decrypt_message(&fourth.ciphertext)
			.unwrap()
			.plaintext,
		b"fourth"
	);
	let before = beacon.ratchet_status().unwrap();
	for replay in [&second, &third, &fourth] {
		assert!(beacon.decrypt_message(&replay.ciphertext).is_none());
		assert_eq!(beacon.ratchet_status().unwrap(), before);
	}
}

#[test]
fn server_routing_rejects_trailing_bytes_before_key_consumption() {
	let mut server = Server::new(SERVER_ID, None);
	let (mut beacon, kid) = register(&mut server);
	let message = beacon.encrypt_message(b"beacon output").unwrap();
	let before = server.ratchet_status(kid).unwrap();
	for attempt in invalid_variants(&message.ciphertext) {
		assert!(server.decrypt_message(&attempt).is_none());
		assert_eq!(server.ratchet_status(kid).unwrap(), before);
	}
	let result = server.decrypt_message(&message.ciphertext).unwrap();
	assert_eq!(
		(result.plaintext.as_slice(), result.key_id, result.seq),
		(b"beacon output".as_slice(), kid, message.seq)
	);
	assert!(server.decrypt_message(&message.ciphertext).is_none());
}

#[test]
fn same_sender_and_sequence_do_not_bypass_session_associated_data() {
	let mut server = Server::new(SERVER_ID, None);
	let (mut first, first_id) = register(&mut server);
	let (mut second, second_id) = register(&mut server);
	let first_message = server.encrypt_message(b"first session", first_id).unwrap();
	let second_message = server
		.encrypt_message(b"second session", second_id)
		.unwrap();
	assert_eq!(
		fields(&first_message.ciphertext).0,
		fields(&second_message.ciphertext).0
	);
	assert_eq!(
		fields(&first_message.ciphertext).1,
		fields(&second_message.ciphertext).1
	);
	let before = first.ratchet_status().unwrap();
	assert!(first.decrypt_message(&second_message.ciphertext).is_none());
	assert_eq!(first.ratchet_status().unwrap(), before);
	assert_eq!(
		first
			.decrypt_message(&first_message.ciphertext)
			.unwrap()
			.plaintext,
		b"first session"
	);
	assert_eq!(
		second
			.decrypt_message(&second_message.ciphertext)
			.unwrap()
			.plaintext,
		b"second session"
	);
}
