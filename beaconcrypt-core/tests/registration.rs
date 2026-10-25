// SPDX-License-Identifier: 0BSD

// These deterministic primitive responses exercise request ownership and lifecycle admission.
// Native integration tests separately execute the real signature, KEM, DH, KDF and record operations.

use beaconcrypt_core::agreement::{self, AgreementEffect};
use beaconcrypt_core::authentication::{AuthRole, SIGNING_CONTEXT, build_signature_input};
use beaconcrypt_core::pqxdh::{
	BeaconCoins, BeaconFresh, BeaconStartInputs, InitialRatchetKdfResponse, KeyIdAvailability,
	RegistrationStatus, ServerBinding, ServerState,
};
use beaconcrypt_core::registration::{self as registration, *};
use beaconcrypt_core::session::ServerAuthenticationPin;

fn hash_parts(request: HashRequest<'_>) -> Vec<&[u8]> {
	match request {
		HashRequest::Single(input) => vec![input],
		HashRequest::Triple(parts) => parts.to_vec(),
	}
}

fn server_binding() -> ServerBinding {
	ServerBinding {
		identity_public_key: [11; 32],
		identity_key_id: 42,
	}
}

fn pin() -> ServerAuthenticationPin {
	ServerAuthenticationPin::new(server_binding(), [17; 1952], [23; 64])
}

struct InitBytes {
	identity: Vec<u8>,
	prekey: Vec<u8>,
	one_time: Vec<u8>,
	pq: Vec<u8>,
	mldsa: Vec<u8>,
	signature: Vec<u8>,
}

impl InitBytes {
	fn packet(&self) -> InitPacket<'_> {
		InitPacket::from_slices(
			&self.identity,
			&self.prekey,
			&self.one_time,
			&self.pq,
			&self.mldsa,
			&self.signature,
		)
		.unwrap()
	}
}

fn start(reject_at: Option<usize>) -> Result<(BeaconPending, InitBytes), BeaconFresh> {
	let control = BeaconFresh::new(server_binding());
	let mut effect = registration::begin_beacon_init(
		control,
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
	let mut position = 0;
	loop {
		effect = match effect {
			BeaconInitEffect::Rejected(fresh) => return Err(fresh),
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
				let (pending, ()) = ready
					.publish((reject_at != Some(position)).then_some(()))?
					.into_parts();
				return Ok((pending, bytes));
			}
			BeaconInitEffect::Ed25519SigningRequested(pending) => {
				let request = pending.request();
				assert_eq!(request.public_key, &[29; 32]);
				assert!(matches!(request.role, AuthRole::Beacon));
				let mut signed = vec![0; 64];
				signed.extend_from_slice(request.message);
				pending.resume((reject_at != Some(position)).then_some(signed.as_slice()))
			}
			BeaconInitEffect::FingerprintRequested(pending) => {
				assert_eq!(hash_parts(pending.request()), [&[19; 1952][..]]);
				pending.resume((reject_at != Some(position)).then_some([31; 64]))
			}
			BeaconInitEffect::HashRequested(pending) => {
				assert_eq!(hash_parts(pending.request())[0].len(), 5495);
				pending.resume((reject_at != Some(position)).then_some([37; 64]))
			}
			BeaconInitEffect::MldsaSigningRequested(pending) => {
				let request = pending.request();
				assert_eq!(request.public_key, &[19; 1952]);
				assert_eq!(request.context, SIGNING_CONTEXT);
				assert_eq!(
					request.input,
					&build_signature_input(AuthRole::Beacon, &[37; 64])
				);
				pending.resume((reject_at != Some(position)).then_some(&[41; 3309][..]))
			}
		};
		position += 1;
	}
}

fn authenticate(bytes: &InitBytes, reject_at: Option<usize>) -> Option<AuthenticatedInit> {
	let mut effect = registration::begin_init_authentication(pin(), bytes.packet());
	let mut position = 0;
	loop {
		effect = match effect {
			InitAuthentication::Rejected => return None,
			InitAuthentication::Accepted(accepted) => return Some(accepted),
			InitAuthentication::HashRequested(pending) => {
				pending.resume((reject_at != Some(position)).then_some([37; 64]))
			}
			InitAuthentication::MldsaVerificationRequested(pending) => {
				assert_eq!(pending.request().public_key, &[19; 1952]);
				assert_eq!(
					pending.request().input,
					&build_signature_input(AuthRole::Beacon, &[37; 64])
				);
				pending.resume(reject_at != Some(position))
			}
			InitAuthentication::Ed25519VerificationRequested(pending) => {
				let request = pending.request();
				assert_eq!(request.public_key, &[29; 32]);
				let expected = match position {
					2 => &bytes.pq,
					3 => &bytes.prekey,
					4 => &bytes.one_time,
					_ => panic!("unexpected Ed verification"),
				};
				assert_eq!(request.signed, expected);
				let opened = request.signed[64..].to_vec();
				pending.resume((reject_at != Some(position)).then_some(opened.as_slice()))
			}
			InitAuthentication::ServerFingerprintRequested(pending) => {
				assert_eq!(hash_parts(pending.request())[0], &[17; 1952]);
				pending.resume((reject_at != Some(position)).then_some([23; 64]))
			}
			InitAuthentication::BeaconFingerprintRequested(pending) => {
				assert_eq!(hash_parts(pending.request())[0], &[19; 1952]);
				pending.resume((reject_at != Some(position)).then_some([31; 64]))
			}
		};
		position += 1;
	}
}

fn agreement(mut effect: AgreementEffect<'_>) -> AgreementEffect<'_> {
	loop {
		effect = match effect {
			AgreementEffect::Rejected(_)
			| AgreementEffect::ServerComplete(_)
			| AgreementEffect::BeaconComplete(_) => return effect,
			AgreementEffect::ConvertPublic(pending) => pending.resume(Some([7; 32])),
			AgreementEffect::ConvertSecret(pending) => pending.resume(true),
			AgreementEffect::GenerateEphemeral(pending) => pending.resume(Some([25; 32])),
			AgreementEffect::Encapsulate(pending) => pending.resume(Some(([33; 1088], [7; 32]))),
			AgreementEffect::Decapsulate(pending) => pending.resume(Some([7; 32])),
			AgreementEffect::Dh(pending) => pending.resume(Some([7; 32])),
			AgreementEffect::RootKdf(pending) => pending.resume(Some([42; 32])),
		};
	}
}

fn server_agreement() -> agreement::ServerAgreement {
	let (_, bytes) = start(None).unwrap();
	let accepted = authenticate(&bytes, None).unwrap();
	let AgreementEffect::ServerComplete(agreement) = agreement(agreement::begin_server_agreement(
		ServerState::new(42),
		RegistrationStatus::Fresh,
		accepted,
	)) else {
		panic!("agreement should succeed")
	};
	agreement
}

fn server_kdf() -> ServerInitialKdf<'static> {
	registration::begin_server_completion(
		ServerState::new(42),
		&pin(),
		KeyIdAvailability::Available,
		server_agreement(),
		b"application",
	)
	.unwrap()
}

fn server_seal() -> ServerInitialSeal<'static> {
	server_kdf()
		.resume(Some(InitialRatchetKdfResponse::from_bytes([1; 64])))
		.unwrap()
}

fn advance_send(
	kernel: beaconcrypt_core::ratchet::ConcreteRatchetKernel,
) -> beaconcrypt_core::ratchet::ConcreteRatchetKernel {
	use beaconcrypt_core::ratchet::*;
	let SendStart::SendKdfRequested(pending) = begin_send(kernel, ()) else {
		panic!("send should start")
	};
	let seal = pending.resume(RatchetKdfResponse::from_bytes([7; 76]));
	seal.finish(Some(())).0
}

fn server_hash(ciphertext: &[u8]) -> ServerResponseHash<'_> {
	let mut pending = server_seal();
	let request = pending.request();
	assert_eq!(
		request.plaintext,
		[&43u64.to_le_bytes()[..], &b"application"[..]]
	);
	assert_eq!(request.sequence, 1);
	assert_eq!(request.sender_key_id, 42);
	assert_eq!(request.target_key_id, 43);
	let kernel = advance_send(pending.take_kernel().unwrap());
	pending.resume(kernel, 1, Some(ciphertext)).unwrap()
}

#[test]
fn initial_signing_and_serialization_failures_return_the_original_fresh_binding() {
	for position in 0..7 {
		let Err(fresh) = start(Some(position)) else {
			panic!("failure must reject")
		};
		assert_eq!(fresh.expected_server_binding(), server_binding());
	}
}

#[test]
fn every_request_authentication_failure_prevents_an_agreement_capability() {
	let (_, bytes) = start(None).unwrap();
	for position in 0..7 {
		assert!(authenticate(&bytes, Some(position)).is_none());
	}
	let accepted = authenticate(&bytes, None).unwrap();
	let mut expected = [29; 64];
	expected[32..].fill(4);
	assert_eq!(accepted.registration_id().as_bytes(), &expected);
}

#[test]
fn server_completion_failures_preserve_the_actual_current_counter() {
	let rejected = |state: ServerState| assert_eq!(state.last_key_id(), 42);
	let result = registration::begin_server_completion(
		ServerState::new(42),
		&pin(),
		KeyIdAvailability::Available,
		server_agreement(),
		b"",
	);
	let Err(state) = result else {
		panic!("empty application must reject")
	};
	rejected(state);
	let result = registration::begin_server_completion(
		ServerState::new(42),
		&pin(),
		KeyIdAvailability::Occupied,
		server_agreement(),
		b"application",
	);
	let Err(state) = result else {
		panic!("collision must reject")
	};
	rejected(state);
	let Err(state) = server_kdf().resume(None) else {
		panic!("KDF failure must reject")
	};
	rejected(state);
	let mut pending = server_seal();
	let kernel = advance_send(pending.take_kernel().unwrap());
	let Err(state) = pending.resume(kernel, 1, None) else {
		panic!("seal failure must reject")
	};
	rejected(state);
	let ciphertext = [53; 99];
	let Err(state) = server_hash(&ciphertext).resume(None) else {
		panic!("hash failure must reject")
	};
	rejected(state);
	let pending = server_hash(&ciphertext).resume(Some([59; 64])).unwrap();
	let Err(state) = pending.resume(None) else {
		panic!("signing failure must reject")
	};
	rejected(state);
	let pending = server_hash(&ciphertext)
		.resume(Some([59; 64]))
		.unwrap()
		.resume(Some(&[61; 3309]))
		.unwrap();
	let Err(state) = pending.publish(None::<()>) else {
		panic!("serialization failure must reject")
	};
	rejected(state);
}

#[test]
fn delayed_response_uses_the_current_counter_and_publishes_only_after_serialization() {
	let pending = registration::begin_server_completion(
		ServerState::new(99),
		&pin(),
		KeyIdAvailability::Available,
		server_agreement(),
		b"application",
	)
	.unwrap();
	let mut pending = pending
		.resume(Some(InitialRatchetKdfResponse::from_bytes([1; 64])))
		.unwrap();
	assert_eq!(pending.request().target_key_id, 100);
	let kernel = advance_send(pending.take_kernel().unwrap());
	let ciphertext = [53; 99];
	let pending = pending.resume(kernel, 1, Some(&ciphertext)).unwrap();
	assert_eq!(hash_parts(pending.request())[2], &100u64.to_le_bytes());
	let pending = pending.resume(Some([59; 64])).unwrap();
	assert_eq!(pending.request().public_key, &[17; 1952]);
	assert_eq!(
		pending.request().input,
		&build_signature_input(AuthRole::Server, &[59; 64])
	);
	let ready = pending.resume(Some(&[61; 3309])).unwrap();
	assert_eq!(ready.message().key_id, 100);
	assert_eq!(ready.message().application_ciphertext, &ciphertext);
	let (control, binding, kernel, ()) = ready.publish(Some(())).unwrap().into_parts();
	assert_eq!(control.last_key_id(), 100);
	assert_eq!(binding.assigned_key_id(), 100);
	assert_eq!(binding.server_binding(), server_binding());
	assert_eq!(binding.beacon_identity_public_key(), &[29; 32]);
	assert_eq!(binding.server_fingerprint(), &[23; 64]);
	assert_eq!(binding.beacon_fingerprint(), &[31; 64]);
	assert_eq!(kernel.send_sequence(), 1);
	assert_eq!(kernel.receive_sequence(), 0);
}

fn response_packet(ciphertext: &[u8]) -> ResponsePacket<'_> {
	ResponsePacket::from_slices(
		&[11; 32],
		&[25; 32],
		&[33; 1088],
		43,
		ciphertext,
		&[41; 3309],
	)
	.unwrap()
}

fn beacon_agreement(ciphertext: &[u8]) -> agreement::BeaconAgreement<'_> {
	let (pending, _) = start(None).unwrap();
	let pending =
		registration::begin_response_authentication(pending, Some(response_packet(ciphertext)))
			.unwrap();
	let pending = pending.resume(Some([53; 64])).unwrap();
	assert_eq!(pending.request().public_key, &[17; 1952]);
	assert_eq!(
		pending.request().input,
		&build_signature_input(AuthRole::Server, &[53; 64])
	);
	let authenticated = pending.resume(true).unwrap();
	let AgreementEffect::BeaconComplete(agreement) =
		agreement(agreement::begin_beacon_agreement(authenticated))
	else {
		panic!("agreement should succeed")
	};
	agreement
}

fn beacon_open(ciphertext: &[u8]) -> BeaconInitialOpen<'_> {
	registration::begin_beacon_completion(beacon_agreement(ciphertext))
		.resume(Some(InitialRatchetKdfResponse::from_bytes([1; 64])))
		.unwrap()
}

fn advance_receive(
	kernel: beaconcrypt_core::ratchet::ConcreteRatchetKernel,
) -> beaconcrypt_core::ratchet::ConcreteRatchetKernel {
	use beaconcrypt_core::ratchet::*;
	let mut effect = begin_receive(kernel, 1, ());
	loop {
		effect = match effect {
			ReceiveEffect::ReceiveRejected { .. } => panic!("receive should start"),
			ReceiveEffect::ReceiveKdfRequested(pending) => {
				pending.resume(RatchetKdfResponse::from_bytes([7; 76]))
			}
			ReceiveEffect::ReceiveOpenRequested(open) => return open.finish(Some(())).0,
		};
	}
}

#[test]
fn every_response_authentication_failure_returns_the_retained_terminal_binding() {
	let ciphertext = [53; 99];
	let (pending, _) = start(None).unwrap();
	let Err(aborted) = registration::begin_response_authentication(pending, None) else {
		panic!("missing packet must abort")
	};
	assert_eq!(aborted.server_key_id(), 42);
	let (pending, _) = start(None).unwrap();
	let pending =
		registration::begin_response_authentication(pending, Some(response_packet(&ciphertext)))
			.unwrap();
	let Err(aborted) = pending.resume(None) else {
		panic!("hash failure must abort")
	};
	assert_eq!(aborted.server_key_id(), 42);
	let (pending, _) = start(None).unwrap();
	let pending =
		registration::begin_response_authentication(pending, Some(response_packet(&ciphertext)))
			.unwrap();
	let pending = pending.resume(Some([53; 64])).unwrap();
	let Err(aborted) = pending.resume(false) else {
		panic!("verification failure must abort")
	};
	assert_eq!(aborted.server_key_id(), 42);
	let Err(aborted) =
		registration::begin_beacon_completion(beacon_agreement(&ciphertext)).resume(None)
	else {
		panic!("KDF failure must abort")
	};
	assert_eq!(aborted.server_key_id(), 42);
}

#[test]
fn initial_open_admission_checks_the_complete_plaintext_and_publishes_its_actual_kernel() {
	let ciphertext = [53; 99];
	let mut valid = 43u64.to_le_bytes().to_vec();
	valid.extend_from_slice(b"application");
	let mut cases: Vec<(Option<Vec<u8>>, u64, u64)> = vec![(None, 1, 42)];
	for width in 0..=8 {
		cases.push((Some(valid[..width].to_vec()), 1, 42));
	}
	for sequence in [0, 2, u64::MAX] {
		cases.push((Some(valid.clone()), sequence, 42));
	}
	for sender in [0, 41, 43, u64::MAX] {
		cases.push((Some(valid.clone()), 1, sender));
	}
	for bit in 0..64 {
		let mut changed = (43u64 ^ (1u64 << bit)).to_le_bytes().to_vec();
		changed.extend_from_slice(b"application");
		cases.push((Some(changed), 1, 42));
	}
	for (plaintext, sequence, sender_key_id) in cases {
		let mut pending = beacon_open(&ciphertext);
		assert_eq!(pending.request().ciphertext, &ciphertext);
		assert_eq!(pending.request().sequence, 1);
		assert_eq!(pending.request().sender_key_id, 42);
		let kernel = advance_receive(pending.take_kernel().unwrap());
		let opened = plaintext.as_deref().map(|plaintext| InitialOpened {
			plaintext,
			sequence,
			sender_key_id,
		});
		let Err(aborted) = pending.resume(kernel, opened) else {
			panic!("malformed initial opening must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
	let mut pending = beacon_open(&ciphertext);
	let expected_ad = *pending.request().associated_data;
	let kernel = advance_receive(pending.take_kernel().unwrap());
	let completed = pending
		.resume(
			kernel,
			Some(InitialOpened {
				plaintext: &valid,
				sequence: 1,
				sender_key_id: 42,
			}),
		)
		.unwrap();
	let (control, binding, kernel, application) = completed.into_parts();
	assert_eq!(control.server_key_id(), 42);
	assert_eq!(control.assigned_key_id(), 43);
	assert_eq!(binding.associated_data(), &expected_ad);
	assert_eq!(binding.assigned_key_id(), 43);
	assert_eq!(application, b"application");
	assert_eq!(kernel.receive_sequence(), 1);
	assert_eq!(kernel.send_sequence(), 0);
	assert_eq!(kernel.receive_cache_len(), 0);
}

#[test]
fn fixed_width_packet_admission_rejects_short_and_long_fields_before_verification() {
	let (_, bytes) = start(None).unwrap();
	let good = [
		&bytes.identity,
		&bytes.prekey,
		&bytes.one_time,
		&bytes.pq,
		&bytes.mldsa,
		&bytes.signature,
	];
	for field in 0..6 {
		for width in [0, good[field].len() - 1, good[field].len() + 1] {
			let changed = vec![0; width];
			let mut fields = good.map(|field| field.as_slice());
			fields[field] = &changed;
			assert!(
				InitPacket::from_slices(
					fields[0], fields[1], fields[2], fields[3], fields[4], fields[5]
				)
				.is_none()
			);
		}
	}
	let good = [vec![11; 32], vec![25; 32], vec![33; 1088], vec![41; 3309]];
	for field in 0..4 {
		for width in [0, good[field].len() - 1, good[field].len() + 1] {
			let changed = vec![0; width];
			let mut fields = good.each_ref().map(|field| field.as_slice());
			fields[field] = &changed;
			assert!(
				ResponsePacket::from_slices(
					fields[0],
					fields[1],
					fields[2],
					43,
					b"ciphertext",
					fields[3]
				)
				.is_none()
			);
		}
	}
}
