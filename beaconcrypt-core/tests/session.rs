// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::authentication::{InitFields, OwnedInitFields};
use beaconcrypt_core::pqxdh::ServerBinding;
use beaconcrypt_core::session::{RegistrationBinding, ServerAuthenticationPin, SessionBinding};

fn server_binding() -> ServerBinding {
	ServerBinding {
		identity_public_key: [11; 32],
		identity_key_id: 42,
	}
}

fn pin() -> ServerAuthenticationPin {
	ServerAuthenticationPin::new(server_binding(), [17; 1952])
}

fn pending() -> RegistrationBinding {
	RegistrationBinding::new(
		pin(),
		[37; 64],
		OwnedInitFields::new(InitFields {
			identity_key: &[29; 33],
			pre_key: &[3; 98],
			one_time_key: &[4; 98],
			pq_key: &[5; 1249],
		}),
	)
}

#[test]
fn pending_registration_retains_pin_and_request_digest_without_a_final_ad() {
	let registration = pending();
	assert_eq!(registration.server_pin().binding(), server_binding());
	assert_eq!(registration.server_pin().public_key(), &[17; 1952]);
	assert_eq!(registration.init_hash(), &[37; 64]);
	assert!(registration.matches_server(&pin()));
}

#[test]
fn every_pin_component_rejects_a_pending_request_on_a_different_server() {
	let registration = pending();
	for key_id in [0, 41, 43, u64::MAX] {
		let mut changed = server_binding();
		changed.identity_key_id = key_id;
		assert!(!registration.matches_server(&ServerAuthenticationPin::new(changed, [17; 1952])));
	}
	for index in 0..32 {
		let mut changed = server_binding();
		changed.identity_public_key[index] ^= 1;
		assert!(!registration.matches_server(&ServerAuthenticationPin::new(changed, [17; 1952])));
	}
	for index in 0..1952 {
		let mut changed = [17; 1952];
		changed[index] ^= 1;
		assert!(
			!registration.matches_server(&ServerAuthenticationPin::new(server_binding(), changed))
		);
	}
}

#[test]
fn trusted_metadata_uses_exact_digest_and_authoritative_context() {
	let hash: [u8; 64] = core::array::from_fn(|i| i as u8);
	let session = SessionBinding::from_trusted_metadata(server_binding(), 43, [29; 32], hash);
	assert_eq!(session.server_binding(), server_binding());
	assert_eq!(session.assigned_key_id(), 43);
	assert_eq!(session.beacon_identity_public_key(), &[29; 32]);
	assert_eq!(session.session_transcript_hash(), &hash);
	assert_eq!(
		&session.associated_data()[..87],
		b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305"
	);
	assert_eq!(&session.associated_data()[87..], &hash);
	for index in 0..64 {
		let mut changed = hash;
		changed[index] ^= 1;
		let restored =
			SessionBinding::from_trusted_metadata(server_binding(), 43, [29; 32], changed);
		assert_ne!(restored.associated_data(), session.associated_data());
	}
}
