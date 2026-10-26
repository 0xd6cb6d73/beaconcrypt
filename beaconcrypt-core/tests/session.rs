// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::pqxdh::{PQXDH_INFO, SYM_RATCHET_INFO, ServerBinding};
use beaconcrypt_core::session::{RegistrationBinding, ServerAuthenticationPin, SessionBinding};

fn server_binding() -> ServerBinding {
	ServerBinding {
		identity_public_key: [11; 32],
		identity_key_id: 42,
	}
}

fn pin() -> ServerAuthenticationPin {
	ServerAuthenticationPin::new(server_binding(), [17; 1952], [23; 64])
}

fn expected_ad() -> Vec<u8> {
	let mut expected = vec![1];
	expected.extend_from_slice(&[11; 32]);
	expected.push(1);
	expected.extend_from_slice(&[29; 32]);
	expected.extend_from_slice(PQXDH_INFO);
	expected.extend_from_slice(SYM_RATCHET_INFO);
	expected.extend_from_slice(&[23; 64]);
	expected.extend_from_slice(&[31; 64]);
	expected
}

#[test]
fn registration_retains_the_exact_pin_digest_and_final_record_binding() {
	let registration = RegistrationBinding::new(pin(), [37; 64], [29; 32], [31; 64]);
	assert_eq!(registration.server_pin().binding(), server_binding());
	assert_eq!(registration.server_pin().public_key(), &[17; 1952]);
	assert_eq!(registration.server_pin().fingerprint(), &[23; 64]);
	assert_eq!(registration.init_hash(), &[37; 64]);
	assert!(registration.matches_server(&pin()));
	assert_eq!(registration.associated_data().as_slice(), expected_ad());
	let session = registration.finish(u64::MAX);
	assert_eq!(session.server_binding(), server_binding());
	assert_eq!(session.assigned_key_id(), u64::MAX);
	assert_eq!(session.beacon_identity_public_key(), &[29; 32]);
	assert_eq!(session.server_fingerprint(), &[23; 64]);
	assert_eq!(session.beacon_fingerprint(), &[31; 64]);
	assert_eq!(session.associated_data().as_slice(), expected_ad());
}

#[test]
fn every_pin_component_rejects_a_pending_request_on_a_different_server() {
	let registration = RegistrationBinding::new(pin(), [37; 64], [29; 32], [31; 64]);
	for key_id in [0, 41, 43, u64::MAX] {
		let mut changed = server_binding();
		changed.identity_key_id = key_id;
		assert!(
			!registration
				.matches_server(&ServerAuthenticationPin::new(changed, [17; 1952], [23; 64],))
		);
	}
	for index in 0..32 {
		let mut changed = server_binding();
		changed.identity_public_key[index] ^= 1;
		assert!(
			!registration
				.matches_server(&ServerAuthenticationPin::new(changed, [17; 1952], [23; 64],))
		);
	}
	for index in 0..1952 {
		let mut changed = [17; 1952];
		changed[index] ^= 1;
		assert!(!registration.matches_server(&ServerAuthenticationPin::new(
			server_binding(),
			changed,
			[23; 64],
		)));
	}
	for index in 0..64 {
		let mut changed = [23; 64];
		changed[index] ^= 1;
		assert!(!registration.matches_server(&ServerAuthenticationPin::new(
			server_binding(),
			[17; 1952],
			changed,
		)));
	}
}

#[test]
fn restored_metadata_reconstructs_the_same_session_without_a_request_digest() {
	let session = RegistrationBinding::new(pin(), [37; 64], [29; 32], [31; 64]).finish(43);
	let restored = SessionBinding::from_trusted_metadata(
		session.server_binding(),
		session.assigned_key_id(),
		*session.beacon_identity_public_key(),
		*session.server_fingerprint(),
		*session.beacon_fingerprint(),
	);
	assert_eq!(restored.server_binding(), session.server_binding());
	assert_eq!(restored.assigned_key_id(), session.assigned_key_id());
	assert_eq!(
		restored.beacon_identity_public_key(),
		session.beacon_identity_public_key()
	);
	assert_eq!(restored.server_fingerprint(), session.server_fingerprint());
	assert_eq!(restored.beacon_fingerprint(), session.beacon_fingerprint());
	assert_eq!(restored.associated_data(), session.associated_data());
}

#[test]
fn request_digest_and_assignment_do_not_change_the_record_ad() {
	let first = RegistrationBinding::new(pin(), [37; 64], [29; 32], [31; 64]);
	let second = RegistrationBinding::new(pin(), [41; 64], [29; 32], [31; 64]);
	assert_ne!(first.init_hash(), second.init_hash());
	assert_eq!(
		first.finish(0).associated_data(),
		second.finish(u64::MAX).associated_data()
	);
}
