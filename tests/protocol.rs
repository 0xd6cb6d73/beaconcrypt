use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use std::panic::{AssertUnwindSafe, catch_unwind};

const SERVER_KID: u64 = 0;
const TAG_SIZE: usize = 16;
const COMMITMENT_SIZE: usize = 64;
const CRYPTO_PAYLOAD_OVERHEAD: usize = TAG_SIZE + COMMITMENT_SIZE;
const RECEIVE_GAP_LIMIT: u64 = 50;

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
	corrupted.set_key_id(frame.get_key_id());
	corrupted.set_cipher_text(&ciphertext);

	let mut serialized = vec![];
	capnp::serialize::write_message(&mut serialized, message.borrow_inner()).unwrap();
	serialized
}

fn serialize_crypto_frame(seq: u64, key_id: u64, ciphertext: &[u8]) -> Vec<u8> {
	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut frame = message.init_root();
	frame.set_seq(seq);
	frame.set_key_id(key_id);
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

fn crypto_frame_key_id(serialized: &[u8]) -> u64 {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	typed.get().unwrap().get_key_id()
}

fn crypto_frame_ciphertext(serialized: &[u8]) -> Vec<u8> {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	typed.get().unwrap().get_cipher_text().unwrap().to_vec()
}

fn rewrite_crypto_frame_seq(serialized: &[u8], seq: u64) -> Vec<u8> {
	serialize_crypto_frame(
		seq,
		crypto_frame_key_id(serialized),
		&crypto_frame_ciphertext(serialized),
	)
}

fn corrupt_crypto_frame_commitment(serialized: &[u8]) -> Vec<u8> {
	let seq = crypto_frame_seq(serialized);
	let key_id = crypto_frame_key_id(serialized);
	let mut ciphertext = crypto_frame_ciphertext(serialized);
	let commitment_start = ciphertext.len() - COMMITMENT_SIZE;
	ciphertext[commitment_start] ^= 0x01;
	serialize_crypto_frame(seq, key_id, &ciphertext)
}

fn receive_state(crypto: &BeaconCryptPqxdh, kid: u64) -> Vec<u8> {
	crypto
		.ratchet_manager(kid)
		.unwrap()
		.recv_state()
		.as_slice()
		.to_vec()
}

fn cached_receive_key_count(crypto: &BeaconCryptPqxdh, kid: u64, start: u64, end: u64) -> usize {
	let ratchet = crypto.ratchet_manager(kid).unwrap();
	(start..=end)
		.filter(|seq| ratchet.recv_key(*seq).is_some())
		.count()
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
	let key_id = crypto_frame_key_id(&valid);
	let mut ciphertext = crypto_frame_ciphertext(&valid);
	let donor_ciphertext = crypto_frame_ciphertext(&donor);

	tamper(&mut ciphertext, &donor_ciphertext);
	let tampered = serialize_crypto_frame(seq, key_id, &ciphertext);

	assert!(beacon.decrypt_message(&tampered).is_none());
	assert_eq!(
		beacon.decrypt_message(&valid).unwrap().plaintext,
		plaintext,
		"rejecting a tampered frame must not consume its receive key"
	);
}

fn assert_sequence_relabelling_is_rejected(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
) {
	let first_plaintext = b"first sequence-bound message";
	let second_plaintext = b"second sequence-bound message";
	let first = sender
		.encrypt_message(first_plaintext, sender_target_kid)
		.unwrap();
	let second = sender
		.encrypt_message(second_plaintext, sender_target_kid)
		.unwrap();
	let first_seq = crypto_frame_seq(&first);
	let second_seq = crypto_frame_seq(&second);
	assert_eq!(second_seq, first_seq + 1);

	let relabelled = rewrite_crypto_frame_seq(&first, second_seq);
	assert!(receiver.decrypt_message(&relabelled).is_none());
	assert_eq!(
		receiver.decrypt_message(&first).unwrap().plaintext,
		first_plaintext
	);
	assert_eq!(
		receiver.decrypt_message(&second).unwrap().plaintext,
		second_plaintext
	);
}

fn assert_invalid_future_frames_cannot_grow_receive_cache(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
	receiver_remote_kid: u64,
) {
	let first_plaintext = b"first message remains usable after forged future frames";
	let second_plaintext = b"second message remains usable after forged future frames";
	let first = sender
		.encrypt_message(first_plaintext, sender_target_kid)
		.unwrap();
	let second = sender
		.encrypt_message(second_plaintext, sender_target_kid)
		.unwrap();
	let first_seq = crypto_frame_seq(&first);
	assert_eq!(crypto_frame_seq(&second), first_seq + 1);
	let current_seq = first_seq - 1;
	let initial_state = receive_state(receiver, receiver_remote_kid);
	let corrupted = corrupt_crypto_frame_commitment(&first);

	for rejected_seq in [0, current_seq + RECEIVE_GAP_LIMIT + 1, u64::MAX] {
		let forged = rewrite_crypto_frame_seq(&corrupted, rejected_seq);
		assert!(
			receiver.decrypt_message(&forged).is_none(),
			"forged sequence {rejected_seq} was accepted"
		);
		assert_eq!(
			receive_state(receiver, receiver_remote_kid),
			initial_state,
			"out-of-range sequence {rejected_seq} advanced the receive state"
		);
		assert!(
			receiver
				.ratchet_manager(receiver_remote_kid)
				.unwrap()
				.recv_key(first_seq)
				.is_none()
		);
	}

	let last_cached_seq = current_seq + RECEIVE_GAP_LIMIT;
	for forged_seq in first_seq..=last_cached_seq {
		let forged = rewrite_crypto_frame_seq(&corrupted, forged_seq);
		assert!(
			receiver.decrypt_message(&forged).is_none(),
			"invalid frame at sequence {forged_seq} was accepted"
		);
		assert_eq!(
			cached_receive_key_count(receiver, receiver_remote_kid, first_seq, last_cached_seq),
			(forged_seq - current_seq) as usize,
			"unexpected cache size after forged sequence {forged_seq}"
		);
	}

	let saturated_state = receive_state(receiver, receiver_remote_kid);
	assert_eq!(
		cached_receive_key_count(receiver, receiver_remote_kid, first_seq, last_cached_seq),
		RECEIVE_GAP_LIMIT as usize
	);

	for rejected_seq in [
		last_cached_seq + 1,
		last_cached_seq + 2,
		last_cached_seq + RECEIVE_GAP_LIMIT,
		u64::MAX,
	] {
		let forged = rewrite_crypto_frame_seq(&corrupted, rejected_seq);
		assert!(
			receiver.decrypt_message(&forged).is_none(),
			"forged sequence {rejected_seq} was accepted after cache saturation"
		);
		assert_eq!(
			receive_state(receiver, receiver_remote_kid),
			saturated_state,
			"forged sequence {rejected_seq} advanced a saturated receive state"
		);
		assert_eq!(
			cached_receive_key_count(receiver, receiver_remote_kid, first_seq, last_cached_seq),
			RECEIVE_GAP_LIMIT as usize
		);
		assert!(
			receiver
				.ratchet_manager(receiver_remote_kid)
				.unwrap()
				.recv_key(rejected_seq)
				.is_none()
		);
	}

	assert_eq!(
		receiver.decrypt_message(&first).unwrap().plaintext,
		first_plaintext
	);
	assert_eq!(
		receiver.decrypt_message(&second).unwrap().plaintext,
		second_plaintext
	);
	assert_eq!(
		receive_state(receiver, receiver_remote_kid),
		saturated_state
	);
	assert_eq!(
		cached_receive_key_count(receiver, receiver_remote_kid, first_seq, last_cached_seq),
		RECEIVE_GAP_LIMIT as usize - 2
	);

	let recovered_boundary_seq = last_cached_seq + 2;
	let recovered_boundary = rewrite_crypto_frame_seq(&corrupted, recovered_boundary_seq);
	assert!(
		receiver.decrypt_message(&recovered_boundary).is_none(),
		"invalid frame at the recovered cache boundary was accepted"
	);
	let recovered_state = receive_state(receiver, receiver_remote_kid);
	assert_ne!(
		recovered_state, saturated_state,
		"freeing two cached keys did not permit two more ratchet steps"
	);
	assert_eq!(
		cached_receive_key_count(
			receiver,
			receiver_remote_kid,
			first_seq + 2,
			recovered_boundary_seq,
		),
		RECEIVE_GAP_LIMIT as usize,
		"receive cache did not refill to its exact boundary"
	);

	let over_recovered_boundary_seq = recovered_boundary_seq + 1;
	let over_recovered_boundary = rewrite_crypto_frame_seq(&corrupted, over_recovered_boundary_seq);
	assert!(
		receiver.decrypt_message(&over_recovered_boundary).is_none(),
		"invalid frame beyond the recovered cache boundary was accepted"
	);
	assert_eq!(
		receive_state(receiver, receiver_remote_kid),
		recovered_state,
		"frame beyond the recovered boundary advanced the receive state"
	);
	assert_eq!(
		cached_receive_key_count(
			receiver,
			receiver_remote_kid,
			first_seq + 2,
			recovered_boundary_seq,
		),
		RECEIVE_GAP_LIMIT as usize,
		"frame beyond the recovered boundary grew the receive cache"
	);
	assert!(
		receiver
			.ratchet_manager(receiver_remote_kid)
			.unwrap()
			.recv_key(over_recovered_boundary_seq)
			.is_none()
	);
}

fn assert_every_inner_payload_bit_is_authenticated(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
) {
	let plaintext = b"every ciphertext, tag, and commitment bit is authenticated";
	let valid = sender
		.encrypt_message(plaintext, sender_target_kid)
		.unwrap();
	let seq = crypto_frame_seq(&valid);
	let key_id = crypto_frame_key_id(&valid);
	let payload = crypto_frame_ciphertext(&valid);
	assert!(payload.len() > CRYPTO_PAYLOAD_OVERHEAD);

	for byte in 0..payload.len() {
		for bit in 0..u8::BITS {
			let mut mutated_payload = payload.clone();
			mutated_payload[byte] ^= 1 << bit;
			let mutated = serialize_crypto_frame(seq, key_id, &mutated_payload);
			assert!(
				receiver.decrypt_message(&mutated).is_none(),
				"accepted mutation at payload byte {byte}, bit {bit}"
			);
		}
	}

	assert_eq!(
		receiver.decrypt_message(&valid).unwrap().plaintext,
		plaintext,
		"failed mutations must not consume the authentic frame's receive key"
	);
}

fn assert_valid_frame_components_cannot_be_spliced(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
) {
	let plaintext_one = [0x11; 32];
	let plaintext_two = [0x22; 32];
	let first = sender
		.encrypt_message(&plaintext_one, sender_target_kid)
		.unwrap();
	let second = sender
		.encrypt_message(&plaintext_two, sender_target_kid)
		.unwrap();
	let first_seq = crypto_frame_seq(&first);
	let second_seq = crypto_frame_seq(&second);
	let key_id = crypto_frame_key_id(&first);
	let first_payload = crypto_frame_ciphertext(&first);
	let second_payload = crypto_frame_ciphertext(&second);
	assert_eq!(second_seq, first_seq + 1);
	assert_eq!(crypto_frame_key_id(&second), key_id);
	assert_eq!(first_payload.len(), second_payload.len());

	let body_end = first_payload.len() - CRYPTO_PAYLOAD_OVERHEAD;
	let tag_end = first_payload.len() - COMMITMENT_SIZE;
	let mut body_splice = first_payload.clone();
	body_splice[..body_end].copy_from_slice(&second_payload[..body_end]);
	let mut tag_splice = first_payload.clone();
	tag_splice[body_end..tag_end].copy_from_slice(&second_payload[body_end..tag_end]);
	let mut commitment_splice = first_payload.clone();
	commitment_splice[tag_end..].copy_from_slice(&second_payload[tag_end..]);
	let mut authenticated_suffix_splice = first_payload.clone();
	authenticated_suffix_splice[body_end..].copy_from_slice(&second_payload[body_end..]);

	for (name, payload) in [
		("ciphertext body", body_splice),
		("AEAD tag", tag_splice),
		("commitment", commitment_splice),
		("tag and commitment", authenticated_suffix_splice),
		("complete payload under the wrong sequence", second_payload),
	] {
		let spliced = serialize_crypto_frame(first_seq, key_id, &payload);
		assert!(
			receiver.decrypt_message(&spliced).is_none(),
			"accepted a frame with a spliced {name}"
		);
	}

	assert_eq!(
		receiver.decrypt_message(&first).unwrap().plaintext,
		plaintext_one
	);
	assert_eq!(
		receiver.decrypt_message(&second).unwrap().plaintext,
		plaintext_two
	);
}

fn assert_receive_window_boundary_survives_rejection_retry_and_replay(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
	receiver_remote_kid: u64,
) {
	let frames = (0..RECEIVE_GAP_LIMIT)
		.map(|index| {
			let plaintext = format!("receive-window-message-{index}").into_bytes();
			let frame = sender
				.encrypt_message(&plaintext, sender_target_kid)
				.unwrap();
			(plaintext, frame)
		})
		.collect::<Vec<_>>();
	let first_seq = crypto_frame_seq(&frames[0].1);
	let boundary_seq = crypto_frame_seq(&frames.last().unwrap().1);
	let sender_kid = crypto_frame_key_id(&frames[0].1);
	assert_eq!(boundary_seq - first_seq + 1, RECEIVE_GAP_LIMIT);

	let initial_state = receive_state(receiver, receiver_remote_kid);
	for len in 0..=CRYPTO_PAYLOAD_OVERHEAD {
		let malformed = serialize_crypto_frame(boundary_seq, sender_kid, &vec![0xA5; len]);
		let result = catch_unwind(AssertUnwindSafe(|| receiver.decrypt_message(&malformed)));
		assert!(
			matches!(result, Ok(None)),
			"future frame with {len} payload bytes was not rejected cleanly"
		);
		assert_eq!(
			receive_state(receiver, receiver_remote_kid),
			initial_state,
			"short future frame with {len} payload bytes advanced the receive ratchet"
		);
		assert_eq!(
			cached_receive_key_count(receiver, receiver_remote_kid, first_seq, boundary_seq,),
			0,
			"short future frame with {len} payload bytes cached receive keys"
		);
	}

	let boundary = &frames.last().unwrap().1;
	let corrupted_commitment = corrupt_crypto_frame_commitment(boundary);
	assert!(receiver.decrypt_message(&corrupted_commitment).is_none());
	let boundary_state = receive_state(receiver, receiver_remote_kid);
	assert_ne!(boundary_state, initial_state);
	assert_eq!(
		cached_receive_key_count(receiver, receiver_remote_kid, first_seq, boundary_seq),
		RECEIVE_GAP_LIMIT as usize
	);

	for attempt in 0..3 {
		assert!(
			receiver.decrypt_message(&corrupted_commitment).is_none(),
			"repeated invalid boundary frame was accepted on attempt {attempt}"
		);
		assert_eq!(
			receive_state(receiver, receiver_remote_kid),
			boundary_state,
			"repeated invalid boundary frame advanced the ratchet"
		);
		assert_eq!(
			cached_receive_key_count(receiver, receiver_remote_kid, first_seq, boundary_seq,),
			RECEIVE_GAP_LIMIT as usize
		);
	}

	let corrupted_ciphertext = corrupt_aead_ciphertext(boundary);
	assert!(receiver.decrypt_message(&corrupted_ciphertext).is_none());
	assert_eq!(receive_state(receiver, receiver_remote_kid), boundary_state);
	assert_eq!(
		cached_receive_key_count(receiver, receiver_remote_kid, first_seq, boundary_seq),
		RECEIVE_GAP_LIMIT as usize
	);

	let boundary_plaintext = &frames.last().unwrap().0;
	assert_eq!(
		receiver.decrypt_message(boundary).unwrap().plaintext,
		boundary_plaintext.as_slice()
	);
	assert!(
		receiver
			.ratchet_manager(receiver_remote_kid)
			.unwrap()
			.recv_key(boundary_seq)
			.is_none()
	);
	assert!(receiver.decrypt_message(boundary).is_none());
	assert_eq!(receive_state(receiver, receiver_remote_kid), boundary_state);

	for index in (0..frames.len() - 1).rev() {
		let (plaintext, frame) = &frames[index];
		assert_eq!(
			receiver.decrypt_message(frame).unwrap().plaintext,
			plaintext.as_slice(),
			"failed to decrypt cached frame at index {index}"
		);
		assert!(
			receiver.decrypt_message(frame).is_none(),
			"replayed cached frame at index {index} was accepted"
		);
		assert_eq!(receive_state(receiver, receiver_remote_kid), boundary_state);
		assert_eq!(
			cached_receive_key_count(receiver, receiver_remote_kid, first_seq, boundary_seq,),
			index,
			"unexpected receive-cache size after index {index}"
		);
	}
}

fn assert_truncated_frames_reject_cleanly(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
	receiver_remote_kid: u64,
) {
	let plaintext = b"authentic frame remains usable after every truncated prefix";
	let valid = sender
		.encrypt_message(plaintext, sender_target_kid)
		.unwrap();
	let corrupted = corrupt_crypto_frame_commitment(&valid);
	let initial_state = receive_state(receiver, receiver_remote_kid);

	for cut in 0..corrupted.len() {
		let result = catch_unwind(AssertUnwindSafe(|| {
			receiver.decrypt_message(&corrupted[..cut])
		}));
		assert!(
			matches!(result, Ok(None)),
			"serialized frame prefix of {cut} bytes was not rejected cleanly"
		);
	}

	assert_eq!(
		receive_state(receiver, receiver_remote_kid),
		initial_state,
		"a strict serialized prefix advanced the receive ratchet"
	);
	assert_eq!(
		receiver.decrypt_message(&valid).unwrap().plaintext,
		plaintext
	);
}

fn assert_message_size_boundaries_round_trip(
	sender: &mut BeaconCryptPqxdh,
	receiver: &mut BeaconCryptPqxdh,
	sender_target_kid: u64,
) {
	for len in [1, 15, 16, 17, 63, 64, 65, 255, 256, 4096] {
		let plaintext = (0..len)
			.map(|index| (index % (u8::MAX as usize + 1)) as u8)
			.collect::<Vec<_>>();
		let frame = sender
			.encrypt_message(&plaintext, sender_target_kid)
			.unwrap();
		assert_eq!(
			crypto_frame_ciphertext(&frame).len(),
			plaintext.len() + CRYPTO_PAYLOAD_OVERHEAD
		);
		assert_eq!(
			receiver.decrypt_message(&frame).unwrap().plaintext,
			plaintext,
			"failed round trip for a {len}-byte plaintext"
		);
	}
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

fn rewrite_crypto_frame_key_id(serialized: &[u8], key_id: u64) -> Vec<u8> {
	let message = capnp::serialize::read_message(serialized, ReaderOptions::new()).unwrap();
	let typed = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(message);
	let original = typed.get().unwrap();

	let mut message = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut rewritten = message.init_root();
	rewritten.set_seq(original.get_seq());
	rewritten.set_key_id(key_id);
	rewritten.set_cipher_text(original.get_cipher_text().unwrap());

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
		b1.decrypt_message(&to_b1).unwrap().plaintext,
		b"server to b1"
	);
	assert_eq!(
		b2.decrypt_message(&to_b2).unwrap().plaintext,
		b"server to b2"
	);

	let from_b1 = b1.encrypt_message(b"b1 to server", SERVER_KID).unwrap();
	let from_b2 = b2.encrypt_message(b"b2 to server", SERVER_KID).unwrap();
	assert_eq!(
		server.decrypt_message(&from_b1).unwrap().plaintext,
		b"b1 to server"
	);
	assert_eq!(
		server.decrypt_message(&from_b2).unwrap().plaintext,
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
		beacon_a.decrypt_message(&ciphertext).unwrap().plaintext,
		message
	);
}

#[test]
fn server_can_decrypt_from_beacon_a_after_registering_beacon_b() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut beacon_a = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut beacon_b = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let _beacon_a_response = register_beacon(&mut server, &mut beacon_a, None);
	register_beacon(&mut server, &mut beacon_b, None);

	let message = b"beacon A to server after registering beacon B";
	let ciphertext = beacon_a.encrypt_message(message, SERVER_KID).unwrap();

	assert_eq!(
		server.decrypt_message(&ciphertext).unwrap().plaintext,
		message
	);
}

#[test]
fn server_can_decrypt_from_beacon_a_after_encrypting_to_beacon_b() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut beacon_a = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut beacon_b = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);

	let _beacon_a_response = register_beacon(&mut server, &mut beacon_a, None);
	let beacon_b_response = register_beacon(&mut server, &mut beacon_b, None);

	let to_beacon_b = server
		.encrypt_message(b"server to beacon B", beacon_b_response.kid)
		.unwrap();
	assert_eq!(
		beacon_b.decrypt_message(&to_beacon_b).unwrap().plaintext,
		b"server to beacon B"
	);

	let from_beacon_a = beacon_a
		.encrypt_message(b"beacon A to server", SERVER_KID)
		.unwrap();
	assert_eq!(
		server.decrypt_message(&from_beacon_a).unwrap().plaintext,
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
	let decrypted = server.decrypt_message(&ciphertext).unwrap();

	assert_eq!(decrypted.key_id, response.kid);
	assert_eq!(decrypted.plaintext, message);
}

#[test]
fn beacon_frame_identifies_its_sender() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"authenticated beacon to server";

	let ciphertext = beacon
		.encrypt_message(message.as_slice(), SERVER_KID)
		.unwrap();
	let decrypted = server.decrypt_message(&ciphertext).unwrap();

	assert_eq!(decrypted.key_id, response.kid);
	assert_eq!(decrypted.plaintext, message);
}

#[test]
fn server_frame_identifies_its_sender() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	let message = b"authenticated server to beacon";

	let ciphertext = server.encrypt_message(message, response.kid).unwrap();
	let decrypted = beacon.decrypt_message(&ciphertext).unwrap();

	assert_eq!(decrypted.key_id, SERVER_KID);
	assert_eq!(decrypted.plaintext, message);
}

#[test]
fn authenticated_beacon_frame_rejects_tampering() {
	let (mut server, mut beacon) = new_pair();
	register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let mut ciphertext = beacon
		.encrypt_message(b"beacon to server", SERVER_KID)
		.unwrap();
	let last = ciphertext.len() - 1;
	ciphertext[last] ^= 0x01;

	assert!(server.decrypt_message(&ciphertext).is_none());
}

#[test]
fn authenticated_server_frame_rejects_tampering() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let mut ciphertext = server
		.encrypt_message(b"server to beacon", response.kid)
		.unwrap();
	let last = ciphertext.len() - 1;
	ciphertext[last] ^= 0x01;

	assert!(beacon.decrypt_message(&ciphertext).is_none());
}

#[test]
fn decrypt_rejects_wrong_direction() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));

	let server_to_beacon = server
		.encrypt_message(b"server to beacon", response.kid)
		.unwrap();
	assert!(server.decrypt_message(&server_to_beacon).is_none());

	let beacon_to_server = beacon
		.encrypt_message(b"beacon to server", SERVER_KID)
		.unwrap();
	assert!(beacon.decrypt_message(&beacon_to_server).is_none());
}

#[test]
fn beacon_cannot_decrypt_message_for_different_beacon() {
	let mut server = BeaconCryptPqxdh::new(false, SERVER_KID, None, None);
	let server_id = server.identity_pk().to_owned();
	let mut b1 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let mut b2 = BeaconCryptPqxdh::new(true, SERVER_KID, Some(server_id.as_bytes()), None);
	let b1_response = register_beacon(&mut server, &mut b1, Some(&[0xFF; 32]));
	let b2_response = register_beacon(&mut server, &mut b2, Some(&[0xFF; 32]));

	let for_b1 = server
		.encrypt_message(b"for b1 only", b1_response.kid)
		.unwrap();
	let for_b2 = server
		.encrypt_message(b"for b2 only", b2_response.kid)
		.unwrap();

	assert!(b2.decrypt_message(&for_b1).is_none());
	assert_eq!(
		b2.decrypt_message(&for_b2).unwrap().plaintext,
		b"for b2 only"
	);
	assert_eq!(
		b1.decrypt_message(&for_b1).unwrap().plaintext,
		b"for b1 only"
	);
}

#[test]
fn ciphertext_cannot_be_replayed() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"one shot";

	let ciphertext = server.encrypt_message(message, response.kid).unwrap();
	let first = beacon.decrypt_message(&ciphertext).unwrap();

	assert_eq!(first.plaintext, message);
	assert!(beacon.decrypt_message(&ciphertext).is_none());
}

#[test]
fn beacon_can_retry_decryption_after_corrupted_aead_message() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"server to beacon";

	let ciphertext = server.encrypt_message(message, response.kid).unwrap();
	let corrupted = corrupt_aead_ciphertext(&ciphertext);

	assert!(beacon.decrypt_message(&corrupted).is_none());
	assert_eq!(
		beacon.decrypt_message(&ciphertext).unwrap().plaintext,
		message
	);
}

#[test]
fn server_can_retry_decryption_after_corrupted_aead_message() {
	let (mut server, mut beacon) = new_pair();
	let _response = register_beacon(&mut server, &mut beacon, Some(&[0xFF; 32]));
	let message = b"beacon to server";

	let ciphertext = beacon.encrypt_message(message, SERVER_KID).unwrap();
	let corrupted = corrupt_aead_ciphertext(&ciphertext);

	assert!(server.decrypt_message(&corrupted).is_none());
	assert_eq!(
		server.decrypt_message(&ciphertext).unwrap().plaintext,
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
	let decrypted = beacon.decrypt_message(&update.data).unwrap();
	assert_eq!(decrypted.key_id, SERVER_KID);
	assert_eq!(decrypted.plaintext, message);
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
		let malformed = serialize_crypto_frame(seq, SERVER_KID, &vec![0xA5; len]);
		let result = catch_unwind(AssertUnwindSafe(|| beacon.decrypt_message(&malformed)));
		assert!(
			matches!(result, Ok(None)),
			"ciphertext length {len} was not rejected cleanly"
		);
	}

	assert_eq!(
		beacon.decrypt_message(&valid).unwrap().plaintext,
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
		beacon.decrypt_message(&to_beacon).unwrap().plaintext,
		b"non-empty"
	);
	assert_eq!(
		server.decrypt_message(&to_server).unwrap().plaintext,
		b"non-empty"
	);
}

#[test]
fn crypto_frame_sequence_is_bound_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_sequence_relabelling_is_rejected(&mut server, &mut beacon, response.kid);

	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_sequence_relabelling_is_rejected(&mut beacon, &mut server, SERVER_KID);
	assert!(
		server
			.ratchet_manager(response.kid)
			.unwrap()
			.recv_key(1)
			.is_none()
	);
}

#[test]
fn invalid_future_frames_cannot_grow_receive_cache_beyond_gap() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_invalid_future_frames_cannot_grow_receive_cache(
		&mut server,
		&mut beacon,
		response.kid,
		SERVER_KID,
	);

	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_invalid_future_frames_cannot_grow_receive_cache(
		&mut beacon,
		&mut server,
		SERVER_KID,
		response.kid,
	);
}

#[test]
fn every_inner_payload_bit_is_authenticated_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_every_inner_payload_bit_is_authenticated(&mut server, &mut beacon, response.kid);

	let (mut server, mut beacon) = new_pair();
	register_beacon(&mut server, &mut beacon, None);
	assert_every_inner_payload_bit_is_authenticated(&mut beacon, &mut server, SERVER_KID);
}

#[test]
fn valid_frame_components_cannot_be_spliced_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_valid_frame_components_cannot_be_spliced(&mut server, &mut beacon, response.kid);

	let (mut server, mut beacon) = new_pair();
	register_beacon(&mut server, &mut beacon, None);
	assert_valid_frame_components_cannot_be_spliced(&mut beacon, &mut server, SERVER_KID);
}

#[test]
fn receive_window_boundary_survives_rejection_retry_and_replay_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_receive_window_boundary_survives_rejection_retry_and_replay(
		&mut server,
		&mut beacon,
		response.kid,
		SERVER_KID,
	);

	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_receive_window_boundary_survives_rejection_retry_and_replay(
		&mut beacon,
		&mut server,
		SERVER_KID,
		response.kid,
	);
}

#[test]
fn every_truncated_frame_prefix_rejects_cleanly_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_truncated_frames_reject_cleanly(&mut server, &mut beacon, response.kid, SERVER_KID);

	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_truncated_frames_reject_cleanly(&mut beacon, &mut server, SERVER_KID, response.kid);
}

#[test]
fn message_size_boundaries_round_trip_in_both_directions() {
	let (mut server, mut beacon) = new_pair();
	let response = register_beacon(&mut server, &mut beacon, None);
	assert_message_size_boundaries_round_trip(&mut server, &mut beacon, response.kid);

	let (mut server, mut beacon) = new_pair();
	register_beacon(&mut server, &mut beacon, None);
	assert_message_size_boundaries_round_trip(&mut beacon, &mut server, SERVER_KID);
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
	for malformed_app_ciphertext in [
		Vec::new(),
		serialize_crypto_frame(1, SERVER_KID, &[0xA5; 79]),
	] {
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
fn encrypted_message_cannot_be_relabelled_to_an_alias_key_id() {
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

	let ciphertext = beacon
		.encrypt_message(b"authenticated beacon message", SERVER_KID)
		.unwrap();
	let relabelled = rewrite_crypto_frame_key_id(&ciphertext, alias.kid);

	assert!(server.decrypt_message(&relabelled).is_none());
	assert_eq!(
		server.decrypt_message(&ciphertext).unwrap().plaintext,
		b"authenticated beacon message"
	);
}
