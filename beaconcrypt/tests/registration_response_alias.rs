//! Transcript signatures authenticate even the input bit ignored by X25519.

use beaconcrypt::*;
use beaconcrypt_parse::KexResponse;

mod common;
use common::decode_response;

#[test]
fn registration_rejects_a_distinct_x25519_ephemeral_encoding() {
	for _ in 0..16 {
		let mut server = Server::new(0, None, None);
		let mut beacon = Beacon::new(
			0,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
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
		let candidate = common::replace_response_payload(&response.serialized, &candidate);
		assert!(beacon.finish_registration(&candidate).is_none());
		assert!(beacon.ratchet_status().is_none());
	}
}
