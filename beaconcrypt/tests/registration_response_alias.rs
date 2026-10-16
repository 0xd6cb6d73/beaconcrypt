//! Counterexample to exact decoded Phase-2 response origin.
//! X25519's ignored input bit is not separately authenticated by production.

use beaconcrypt::*;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};

#[test]
fn registration_accepts_a_distinct_x25519_ephemeral_encoding() {
	for _ in 0..16 {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		let init = beacon.get_registration_bundle().unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server
			.build_registration_response(accepted, Some(b"sequence-one response"))
			.unwrap();
		let reader = capnp::serialize_packed::read_message(
			response.serialized.as_slice(),
			ReaderOptions::new(),
		)
		.unwrap();
		let typed = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let original = typed.get().unwrap();
		let original_ephemeral = original.get_ephemeral_key().unwrap();
		assert_eq!(original_ephemeral.len(), 32);
		assert_eq!(original_ephemeral[31] & 0x80, 0);
		let mut alias = original_ephemeral.to_vec();
		alias[31] ^= 0x80;
		assert_ne!(alias, original_ephemeral);

		let mut builder = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
		let mut rewritten = builder.init_root();
		rewritten.set_identity_key(original.get_identity_key().unwrap());
		rewritten.set_ephemeral_key(&alias);
		rewritten.set_kem_cipher_text(original.get_kem_cipher_text().unwrap());
		rewritten.set_app_cipher_text(original.get_app_cipher_text().unwrap());
		rewritten.set_key_id(original.get_key_id());
		let mut candidate = vec![];
		capnp::serialize_packed::write_message(&mut candidate, builder.borrow_inner()).unwrap();
		assert_ne!(candidate, response.serialized);

		let changed_reader =
			capnp::serialize_packed::read_message(candidate.as_slice(), ReaderOptions::new())
				.unwrap();
		let changed_typed =
			TypedReader::<_, phase2_capnp::kex_response::Owned>::new(changed_reader);
		let changed = changed_typed.get().unwrap();
		assert_eq!(changed.get_ephemeral_key().unwrap(), alias);
		assert_ne!(changed.get_ephemeral_key().unwrap(), original_ephemeral);
		assert_eq!(
			changed.get_identity_key().unwrap(),
			original.get_identity_key().unwrap()
		);
		assert_eq!(
			changed.get_kem_cipher_text().unwrap(),
			original.get_kem_cipher_text().unwrap()
		);
		assert_eq!(
			changed.get_app_cipher_text().unwrap(),
			original.get_app_cipher_text().unwrap()
		);
		assert_eq!(changed.get_key_id(), original.get_key_id());

		let frame_reader = capnp::serialize::read_message(
			changed.get_app_cipher_text().unwrap(),
			ReaderOptions::new(),
		)
		.unwrap();
		let frame_typed =
			TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(frame_reader);
		assert_eq!(frame_typed.get().unwrap().get_seq(), 1);
		assert_eq!(
			beacon.finish_registration(&candidate).unwrap(),
			b"sequence-one response"
		);
		assert_eq!(beacon.ratchet_status().unwrap().receive_sequence(), 1);

		let outbound = beacon.encrypt_message(b"beacon after alias").unwrap();
		assert_eq!(
			server.decrypt_message(&outbound).unwrap().plaintext,
			b"beacon after alias"
		);
		let inbound = server
			.encrypt_message(b"server after alias", original.get_key_id())
			.unwrap();
		assert_eq!(
			beacon.decrypt_message(&inbound).unwrap().plaintext,
			b"server after alias"
		);
	}
}
