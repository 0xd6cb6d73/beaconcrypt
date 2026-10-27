// SPDX-License-Identifier: 0BSD

use beaconcrypt_core::agreement::{self, AgreementEffect, DhSecretRole, EphemeralRole};
use beaconcrypt_core::pqxdh::{
	BeaconCoins, BeaconFresh, BeaconStartInputs, PQXDH_INFO, RegistrationStatus, ServerBinding,
	ServerState,
};
use beaconcrypt_core::registration::{
	self, BeaconInitEffect, BeaconPending, InitAuthentication, InitPacket, ResponsePacket,
};
use beaconcrypt_core::session::ServerAuthenticationPin;

struct InitBytes {
	identity: Vec<u8>,
	prekey: Vec<u8>,
	one_time: Vec<u8>,
	pq: Vec<u8>,
	mldsa: Vec<u8>,
	signature: Vec<u8>,
}

fn pin() -> ServerAuthenticationPin {
	ServerAuthenticationPin::new(
		ServerBinding {
			identity_public_key: [11; 32],
			identity_key_id: 42,
		},
		[17; 1952],
		[23; 64],
	)
}

fn initiation() -> (BeaconPending, InitBytes) {
	let mut effect = registration::begin_beacon_init(
		BeaconFresh::new(pin().binding()),
		BeaconStartInputs {
			identity_public_key: [29; 32],
			prekey_public_key: [3; 32],
			pq_public_key: [5; 1184],
		},
		BeaconCoins {
			one_time_public_key: [4; 32],
		},
		pin(),
		[19; 1952],
	);
	loop {
		effect = match effect {
			BeaconInitEffect::Rejected(_) => panic!("fixture initiation rejected"),
			BeaconInitEffect::Ready(ready) => {
				let view = ready.message();
				let bytes = InitBytes {
					identity: view.fields.identity_key.to_vec(),
					prekey: view.fields.pre_key.to_vec(),
					one_time: view.fields.one_time_key.to_vec(),
					pq: view.fields.pq_key.to_vec(),
					mldsa: view.fields.mldsa_public_key.to_vec(),
					signature: view.signature.to_vec(),
				};
				return (ready.publish(Some(())).ok().unwrap().into_parts().0, bytes);
			}
			BeaconInitEffect::Ed25519SigningRequested(pending) => {
				let mut signed = vec![0; 64];
				signed.extend_from_slice(pending.request().message);
				pending.resume(Some(&signed))
			}
			BeaconInitEffect::FingerprintRequested(pending) => pending.resume(Some([31; 64])),
			BeaconInitEffect::HashRequested(pending) => pending.resume(Some([37; 64])),
			BeaconInitEffect::MldsaSigningRequested(pending) => pending.resume(Some(&[41; 3309])),
		};
	}
}

fn server_start(status: RegistrationStatus) -> AgreementEffect<'static> {
	let (_, bytes) = initiation();
	let packet = InitPacket::from_slices(
		&bytes.identity,
		&bytes.prekey,
		&bytes.one_time,
		&bytes.pq,
		&bytes.mldsa,
		&bytes.signature,
	)
	.unwrap();
	let mut effect = registration::begin_init_authentication(pin(), packet);
	loop {
		effect = match effect {
			InitAuthentication::Rejected => panic!("fixture authentication rejected"),
			InitAuthentication::Accepted(authenticated) => {
				return agreement::begin_server_agreement(
					ServerState::new(42),
					status,
					authenticated,
				);
			}
			InitAuthentication::HashRequested(pending) => pending.resume(Some([37; 64])),
			InitAuthentication::MldsaVerificationRequested(pending) => pending.resume(true),
			InitAuthentication::Ed25519VerificationRequested(pending) => {
				let opened = pending.request().signed[64..].to_vec();
				pending.resume(Some(&opened))
			}
			InitAuthentication::ServerFingerprintRequested(pending) => {
				pending.resume(Some([23; 64]))
			}
			InitAuthentication::BeaconFingerprintRequested(pending) => {
				pending.resume(Some([31; 64]))
			}
		};
	}
}

fn beacon_start<'a>(identity: &'a [u8; 32], ciphertext: &'a [u8]) -> AgreementEffect<'a> {
	let (pending, _) = initiation();
	let packet = ResponsePacket::from_slices(
		identity,
		&[25; 32],
		&[33; 1088],
		43,
		ciphertext,
		&[47; 3309],
	)
	.unwrap();
	let hash = registration::begin_response_authentication(pending, Some(packet))
		.ok()
		.unwrap();
	let verify = hash.resume(Some([53; 64])).ok().unwrap();
	agreement::begin_beacon_agreement(verify.resume(true).ok().unwrap())
}

fn root_input() -> Vec<u8> {
	let mut expected = vec![0xff; 32];
	for byte in 11..=14 {
		expected.extend_from_slice(&[byte; 32]);
	}
	expected.extend_from_slice(&[77; 32]);
	expected
}

fn drive(
	mut effect: AgreementEffect<'_>,
	beacon: bool,
	fail_at: Option<usize>,
	zero_dh: Option<usize>,
) -> AgreementEffect<'_> {
	let mut position = 0;
	let mut dh = 0;
	loop {
		let succeed = fail_at != Some(position);
		effect = match effect {
			AgreementEffect::Rejected(_)
			| AgreementEffect::ServerComplete(_)
			| AgreementEffect::BeaconComplete(_) => return effect,
			AgreementEffect::GenerateEphemeral(pending) => {
				assert!(!beacon);
				assert_eq!(position, 0);
				assert!(matches!(pending.role(), EphemeralRole::ServerEphemeral));
				pending.resume(succeed.then_some([25; 32]))
			}
			AgreementEffect::Encapsulate(pending) => {
				assert!(!beacon);
				assert_eq!(position, 1);
				assert_eq!(pending.public_key(), Some(&[5; 1184]));
				pending.resume(succeed.then_some(([33; 1088], [77; 32])))
			}
			AgreementEffect::ConvertPublic(pending) => {
				assert_eq!(position, if beacon { 0 } else { 2 });
				assert_eq!(
					pending.public_key(),
					if beacon { &[11; 32] } else { &[29; 32] }
				);
				pending.resume(succeed.then_some([7; 32]))
			}
			AgreementEffect::ConvertSecret(pending) => {
				assert_eq!(position, if beacon { 1 } else { 3 });
				assert!(matches!(pending.secret_role(), DhSecretRole::LocalIdentity));
				pending.resume(succeed)
			}
			AgreementEffect::Decapsulate(pending) => {
				assert!(beacon);
				assert_eq!(position, 2);
				assert_eq!(pending.ciphertext(), Some(&[33; 1088]));
				pending.resume(succeed.then_some([77; 32]))
			}
			AgreementEffect::Dh(pending) => {
				let request = pending.request();
				let (role, public) = if beacon {
					match dh {
						0 => (DhSecretRole::BeaconPrekey, [7; 32]),
						1 => (DhSecretRole::LocalIdentity, [25; 32]),
						2 => (DhSecretRole::BeaconPrekey, [25; 32]),
						3 => (DhSecretRole::BeaconOneTime, [25; 32]),
						_ => panic!("extra DH"),
					}
				} else {
					match dh {
						0 => (DhSecretRole::LocalIdentity, [3; 32]),
						1 => (DhSecretRole::ServerEphemeral, [7; 32]),
						2 => (DhSecretRole::ServerEphemeral, [3; 32]),
						3 => (DhSecretRole::ServerEphemeral, [4; 32]),
						_ => panic!("extra DH"),
					}
				};
				assert!(matches!(
					(request.secret_role, role),
					(DhSecretRole::LocalIdentity, DhSecretRole::LocalIdentity)
						| (DhSecretRole::ServerEphemeral, DhSecretRole::ServerEphemeral)
						| (DhSecretRole::BeaconPrekey, DhSecretRole::BeaconPrekey)
						| (DhSecretRole::BeaconOneTime, DhSecretRole::BeaconOneTime)
				));
				assert_eq!(request.public_key, &public);
				let byte = if zero_dh == Some(dh) {
					0
				} else {
					11 + dh as u8
				};
				dh += 1;
				pending.resume(succeed.then_some([byte; 32]))
			}
			AgreementEffect::RootKdf(pending) => {
				assert_eq!(dh, 4);
				assert_eq!(pending.request().info, PQXDH_INFO);
				assert_eq!(pending.request().input.as_slice(), root_input());
				pending.resume(succeed.then_some([83; 32]))
			}
		};
		position += 1;
	}
}

#[test]
fn role_specific_requests_bind_every_dh_operand_kem_coin_and_root_segment() {
	let effect = drive(server_start(RegistrationStatus::Fresh), false, None, None);
	let AgreementEffect::ServerComplete(accepted) = effect else {
		panic!("server did not complete")
	};
	assert_eq!(
		accepted.registration_id().as_bytes(),
		&[vec![29; 32], vec![4; 32]].concat()[..]
	);
	assert!(matches!(
		drive(beacon_start(&[11; 32], &[99; 81]), true, None, None),
		AgreementEffect::BeaconComplete(_)
	));
}

#[test]
fn every_primitive_failure_is_neutral_for_server_and_terminal_for_beacon() {
	for position in 0..9 {
		assert!(matches!(
			drive(
				server_start(RegistrationStatus::Fresh),
				false,
				Some(position),
				None
			),
			AgreementEffect::Rejected(None)
		));
	}
	for position in 0..8 {
		let effect = drive(
			beacon_start(&[11; 32], &[99; 81]),
			true,
			Some(position),
			None,
		);
		let AgreementEffect::Rejected(Some(aborted)) = effect else {
			panic!("missing terminal abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
}

#[test]
fn zero_dh_outputs_never_reach_root_kdf_or_a_registration_candidate() {
	for dh in 0..4 {
		assert!(matches!(
			drive(
				server_start(RegistrationStatus::Fresh),
				false,
				None,
				Some(dh)
			),
			AgreementEffect::Rejected(None)
		));
		assert!(matches!(
			drive(beacon_start(&[11; 32], &[99; 81]), true, None, Some(dh)),
			AgreementEffect::Rejected(Some(_))
		));
	}
}

#[test]
fn replay_rejects_before_effects_and_identity_rejects_after_dh_before_root() {
	assert!(matches!(
		server_start(RegistrationStatus::Consumed),
		AgreementEffect::Rejected(None)
	));
	let mut effect = beacon_start(&[12; 32], &[99; 81]);
	let mut dh = 0;
	loop {
		effect = match effect {
			AgreementEffect::ConvertPublic(pending) => {
				assert_eq!(pending.public_key(), &[12; 32]);
				pending.resume(Some([7; 32]))
			}
			AgreementEffect::ConvertSecret(pending) => pending.resume(true),
			AgreementEffect::Decapsulate(pending) => pending.resume(Some([77; 32])),
			AgreementEffect::Dh(pending) => {
				dh += 1;
				pending.resume(Some([7; 32]))
			}
			AgreementEffect::Rejected(Some(aborted)) => {
				assert_eq!(dh, 4);
				assert_eq!(aborted.server_key_id(), 42);
				break;
			}
			_ => panic!("wrong identity reached root or an unrelated role"),
		};
	}
}
