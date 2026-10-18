//! Counterexample to exact decoded Phase-2 response origin.
//! X25519's ignored input bit is not separately authenticated by production.

use beaconcrypt::*;
use beaconcrypt_parse::{KexResponse, decode_response};

mod common;

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
		let original = decode_response(&response.serialized).unwrap();
		let original_ephemeral = original.ephemeral_key;
		assert_eq!(original_ephemeral.len(), 32);
		assert_eq!(original_ephemeral[31] & 0x80, 0);
		let mut alias = original_ephemeral.to_vec();
		alias[31] ^= 0x80;
		assert_ne!(alias, original_ephemeral);

		let candidate = common::encode_response(KexResponse {
			identity_key: original.identity_key,
			ephemeral_key: &alias,
			kem_cipher_text: original.kem_cipher_text,
			app_cipher_text: original.app_cipher_text,
			key_id: original.key_id,
		});
		assert_ne!(candidate, response.serialized);

		let changed = decode_response(&candidate).unwrap();
		assert_eq!(changed.ephemeral_key, alias);
		assert_ne!(changed.ephemeral_key, original_ephemeral);
		assert_eq!(changed.identity_key, original.identity_key);
		assert_eq!(changed.kem_cipher_text, original.kem_cipher_text);
		assert_eq!(changed.app_cipher_text, original.app_cipher_text);
		assert_eq!(changed.key_id, original.key_id);
		assert_eq!(
			changed.app_cipher_text.len(),
			8 + b"sequence-one response".len() + 16 + 64
		);
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
			.encrypt_message(b"server after alias", original.key_id)
			.unwrap();
		assert_eq!(
			beacon.decrypt_message(&inbound).unwrap().plaintext,
			b"server after alias"
		);
	}
}
