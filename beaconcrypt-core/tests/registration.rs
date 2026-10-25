// SPDX-License-Identifier: 0BSD

// These deterministic primitive responses exercise request ownership and lifecycle admission.
// Native integration tests separately execute the real signature, KEM, DH, KDF and record operations.

use beaconcrypt_core::agreement::{self, AgreementEffect};
use beaconcrypt_core::authentication::{AuthRole, SIGNING_CONTEXT, build_signature_input};
use beaconcrypt_core::pqxdh::{
	BeaconCoins, BeaconFresh, BeaconStartInputs, InitialRatchetKdfResponse, KeyIdAvailability,
	RegistrationStatus, ServerBinding, ServerState,
};
use beaconcrypt_core::ratchet::{ConcreteRatchetKernel, RatchetKdfResponse};
use beaconcrypt_core::record_effects as records;
use beaconcrypt_core::registration::{self as registration, *};
use beaconcrypt_core::session::{RegistrationBinding, ServerAuthenticationPin, SessionBinding};

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

// This test interpreter authenticates every primitive input deterministically; it is not a crypto implementation.
fn digest(bytes: &[u8]) -> [u8; 64] {
	let mut output = std::array::from_fn(|index| index as u8);
	for (index, byte) in bytes.iter().enumerate() {
		let slot = index % output.len();
		output[slot] = output[slot].wrapping_add(*byte).rotate_left(1) ^ index as u8;
	}
	output
}

fn expected_ad() -> [u8; 281] {
	*RegistrationBinding::new(pin(), [37; 64], [29; 32], [31; 64]).associated_data()
}

fn step_response() -> RatchetKdfResponse {
	RatchetKdfResponse::from_bytes([7; 76])
}

fn tag(key: &[u8; 32], nonce: &[u8; 12], ad: &[u8; 281], plaintext: &[u8]) -> [u8; 16] {
	let hash = digest(&[key.as_slice(), nonce.as_slice(), ad.as_slice(), plaintext].concat());
	std::array::from_fn(|index| {
		hash[index] ^ hash[index + 16] ^ hash[index + 32] ^ hash[index + 48]
	})
}

fn seal_primitive(request: records::AeadSealRequest<'_>) -> (Vec<u8>, [u8; 16]) {
	assert_eq!(request.key, &[7; 32]);
	assert_eq!(request.nonce, &[7; 12]);
	assert_eq!(request.associated_data, &expected_ad());
	let plaintext = match request.plaintext {
		records::SealPlaintextRequest::Single(application) => application.to_vec(),
		records::SealPlaintextRequest::Prefixed {
			prefix,
			application,
		} => [prefix.as_slice(), application].concat(),
	};
	let tag = tag(
		request.key,
		request.nonce,
		request.associated_data,
		&plaintext,
	);
	(plaintext, tag)
}

fn open_primitive(request: Option<beaconcrypt_core::record::AeadRequest<'_>>) -> Option<Vec<u8>> {
	let request = request?;
	assert_eq!(request.key, &[7; 32]);
	assert_eq!(request.nonce, &[7; 12]);
	assert_eq!(request.associated_data, &expected_ad());
	let length = request.ciphertext.len().checked_sub(16)?;
	let (plaintext, supplied) = request.ciphertext.split_at(length);
	(supplied
		== tag(
			request.key,
			request.nonce,
			request.associated_data,
			plaintext,
		))
	.then(|| plaintext.to_vec())
}

fn commitment_hash(
	transcript: &mut beaconcrypt_core::commitment::CommitmentTranscript,
) -> [u8; 64] {
	let hash = digest(transcript.as_bytes());
	transcript.as_mut_bytes().fill(0);
	assert!(transcript.as_bytes().iter().all(|byte| *byte == 0));
	hash
}

fn assert_initial_commitment(transcript: &beaconcrypt_core::commitment::CommitmentTranscript) {
	let bytes = transcript.as_bytes();
	assert_eq!(&bytes[..32], &[7; 32]);
	assert_eq!(&bytes[32..44], &[7; 12]);
	assert_eq!(&bytes[44..325], &expected_ad());
	assert_eq!(
		&bytes[bytes.len() - 16..bytes.len() - 8],
		&1u64.to_le_bytes()
	);
	assert_eq!(&bytes[bytes.len() - 8..], &42u64.to_le_bytes());
}

fn raw_write(request: records::RecordWriteRequest<'_>) -> Vec<u8> {
	let records::RecordWriteRequest::Raw { parts } = request else {
		panic!("registration must request implicit raw encoding")
	};
	assert_eq!(parts[1].len(), 16);
	assert_eq!(parts[2].len(), 64);
	parts.concat()
}

fn with_server_writer<'application, Output>(
	pending: ServerInitialSeal<'application>,
	assigned: u64,
	action: impl for<'ciphertext> FnOnce(ServerRecordWrite<'application, 'ciphertext>) -> Output,
) -> Output {
	assert_eq!(pending.request().input(), &[1; 32]);
	let aead = pending.resume(Some(step_response())).unwrap();
	let request = aead.request();
	let records::SealPlaintextRequest::Prefixed {
		prefix,
		application,
	} = request.plaintext
	else {
		panic!("registration prefix must be source-owned")
	};
	assert_eq!(prefix, &assigned.to_le_bytes());
	assert_eq!(application, b"application");
	let (body, tag) = seal_primitive(aead.request());
	let mut commitment = aead.resume(Some((&body, tag))).unwrap();
	assert_initial_commitment(commitment.transcript());
	let hash = commitment_hash(commitment.transcript_mut());
	let writer = commitment.resume(Some(hash)).unwrap();
	action(writer)
}

fn server_ciphertext() -> Vec<u8> {
	with_server_writer(server_seal(), 43, |writer| raw_write(writer.request()))
}

fn server_hash(ciphertext: &[u8]) -> ServerResponseHash<'_> {
	with_server_writer(server_seal(), 43, |writer| {
		assert_eq!(raw_write(writer.request()), ciphertext);
		writer.resume(Some(ciphertext)).unwrap()
	})
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
	let Err(state) = server_seal().resume(None) else {
		panic!("record KDF failure must reject")
	};
	rejected(state);
	let aead = server_seal().resume(Some(step_response())).unwrap();
	let Err(state) = aead.resume(None) else {
		panic!("AEAD failure must reject")
	};
	rejected(state);
	let aead = server_seal().resume(Some(step_response())).unwrap();
	let (body, tag) = seal_primitive(aead.request());
	let commitment = aead.resume(Some((&body, tag))).unwrap();
	let Err(state) = commitment.resume(None) else {
		panic!("commitment hash failure must reject")
	};
	rejected(state);
	let Err(state) = with_server_writer(server_seal(), 43, |writer| writer.resume(None)) else {
		panic!("raw write failure must reject")
	};
	rejected(state);
	for width in [98, 100] {
		let malformed = vec![0; width];
		let result =
			with_server_writer(server_seal(), 43, |writer| writer.resume(Some(&malformed)));
		let Err(state) = result else {
			panic!("malformed raw write width must reject")
		};
		rejected(state);
	}
	let ciphertext = server_ciphertext();
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
	let pending = pending
		.resume(Some(InitialRatchetKdfResponse::from_bytes([1; 64])))
		.unwrap();
	let (control, binding, kernel, ()) = with_server_writer(pending, 100, |writer| {
		let ciphertext = raw_write(writer.request());
		let pending = writer.resume(Some(&ciphertext)).unwrap();
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
		ready.publish(Some(())).unwrap().into_parts()
	});
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

#[derive(Clone, Copy)]
enum ReceiveFailure {
	Kdf,
	Hash,
	Aead,
}

#[derive(Default)]
struct ReceiveTrace {
	kdfs: usize,
	hashes: usize,
	aeads: usize,
}

struct Completed {
	control: beaconcrypt_core::pqxdh::BeaconEstablished,
	binding: SessionBinding,
	kernel: ConcreteRatchetKernel,
	application: Vec<u8>,
}

fn complete_beacon(
	ciphertext: &[u8],
	failure: Option<ReceiveFailure>,
	trace: &mut ReceiveTrace,
) -> Result<Completed, beaconcrypt_core::pqxdh::BeaconAborted> {
	let mut effect = registration::begin_beacon_completion(beacon_agreement(ciphertext))
		.resume(Some(InitialRatchetKdfResponse::from_bytes([1; 64])))?;
	loop {
		effect = match effect {
			BeaconInitialOpen::KdfRequested(pending) => {
				trace.kdfs += 1;
				assert_eq!(pending.request().input(), &[1; 32]);
				pending
					.resume((!matches!(failure, Some(ReceiveFailure::Kdf))).then(step_response))?
			}
			BeaconInitialOpen::CommitmentRequested(mut pending) => {
				trace.hashes += 1;
				assert_initial_commitment(pending.transcript());
				let actual = commitment_hash(pending.transcript_mut());
				let matches = !matches!(failure, Some(ReceiveFailure::Hash))
					&& &actual == pending.supplied_commitment();
				pending.resume(matches)?
			}
			BeaconInitialOpen::AeadRequested(pending) => {
				trace.aeads += 1;
				let plaintext = if matches!(failure, Some(ReceiveFailure::Aead)) {
					None
				} else {
					open_primitive(pending.request())
				};
				let (control, binding, kernel, application) =
					pending.finish(plaintext.as_deref())?.into_parts();
				return Ok(Completed {
					control,
					binding,
					kernel,
					application: application.to_vec(),
				});
			}
		};
	}
}

// These are authenticated ciphertext substitutions, never independent completion metadata or kernels.
fn authenticated_payload(plaintext: &[u8], sequence: u64, sender: u64) -> Vec<u8> {
	let tag = tag(&[7; 32], &[7; 12], &expected_ad(), plaintext);
	let transcript = beaconcrypt_core::commitment::build_commitment_transcript(
		&[7; 32],
		&[7; 12],
		&expected_ad(),
		&tag,
		sequence,
		sender,
	);
	[
		plaintext,
		tag.as_slice(),
		digest(transcript.as_bytes()).as_slice(),
	]
	.concat()
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
	let ciphertext = server_ciphertext();
	let mut valid = 43u64.to_le_bytes().to_vec();
	valid.extend_from_slice(b"application");
	for width in 0..=8 {
		let payload = authenticated_payload(&valid[..width], 1, 42);
		let Err(aborted) = complete_beacon(&payload, None, &mut ReceiveTrace::default()) else {
			panic!("empty or short authenticated initial plaintext must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
	for bit in 0..64 {
		let mut changed = (43u64 ^ (1u64 << bit)).to_le_bytes().to_vec();
		changed.extend_from_slice(b"application");
		let payload = authenticated_payload(&changed, 1, 42);
		let Err(aborted) = complete_beacon(&payload, None, &mut ReceiveTrace::default()) else {
			panic!("every incorrect assigned-ID bit must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
	for (sequence, sender) in [
		(0, 42),
		(2, 42),
		(u64::MAX, 42),
		(1, 0),
		(1, 41),
		(1, 43),
		(1, u64::MAX),
	] {
		let payload = authenticated_payload(&valid, sequence, sender);
		let mut trace = ReceiveTrace::default();
		let Err(aborted) = complete_beacon(&payload, None, &mut trace) else {
			panic!("a ciphertext bound to other metadata must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
		assert_eq!((trace.kdfs, trace.hashes, trace.aeads), (1, 1, 0));
	}
	for failure in [
		ReceiveFailure::Kdf,
		ReceiveFailure::Hash,
		ReceiveFailure::Aead,
	] {
		let Err(aborted) =
			complete_beacon(&ciphertext, Some(failure), &mut ReceiveTrace::default())
		else {
			panic!("every primitive failure must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
	for offset in [0, ciphertext.len() - 80, ciphertext.len() - 1] {
		let mut substituted = ciphertext.clone();
		substituted[offset] ^= 1;
		let Err(aborted) = complete_beacon(&substituted, None, &mut ReceiveTrace::default()) else {
			panic!("body, tag and commitment substitution must abort")
		};
		assert_eq!(aborted.server_key_id(), 42);
	}
	let mut trace = ReceiveTrace::default();
	let completed = complete_beacon(&ciphertext, None, &mut trace).unwrap();
	assert_eq!((trace.kdfs, trace.hashes, trace.aeads), (1, 1, 1));
	assert_eq!(completed.control.server_key_id(), 42);
	assert_eq!(completed.control.assigned_key_id(), 43);
	assert_eq!(completed.binding.associated_data(), &expected_ad());
	assert_eq!(completed.binding.assigned_key_id(), 43);
	assert_eq!(completed.application, b"application");
	assert_eq!(completed.kernel.receive_sequence(), 1);
	assert_eq!(completed.kernel.send_sequence(), 0);
	assert_eq!(completed.kernel.receive_cache_len(), 0);
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

fn initial_record_kernel() -> ConcreteRatchetKernel {
	let pending = beaconcrypt_core::pqxdh::start_beacon_ratchet_kdf(&[42; 32]);
	assert_eq!(pending.request().input(), &[42; 32]);
	beaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(
		pending,
		InitialRatchetKdfResponse::from_bytes([1; 64]),
	)
}

type KernelSnapshot = (u64, u64, [u8; 32], [u8; 32], Vec<(u64, [u8; 32], [u8; 12])>);

fn kernel_snapshot(kernel: &ConcreteRatchetKernel) -> KernelSnapshot {
	let entries = (0..kernel.receive_cache_len())
		.map(|slot| {
			let (sequence, material) = kernel.receive_entry_at(slot).unwrap();
			(
				sequence,
				*material.key().as_bytes(),
				*material.nonce().as_bytes(),
			)
		})
		.collect();
	(
		kernel.send_sequence(),
		kernel.receive_sequence(),
		*kernel.send_chain().as_bytes(),
		*kernel.receive_chain().as_bytes(),
		entries,
	)
}

fn send_record(
	kernel: ConcreteRatchetKernel,
	application: &[u8],
) -> (ConcreteRatchetKernel, Vec<u8>) {
	let context = records::SealFrameContext::new(
		application,
		43,
		42,
		&expected_ad(),
		records::RecordEncoding::Raw,
	);
	let records::RecordSendStart::KdfRequested(pending) =
		records::begin_record_send(kernel, context)
	else {
		panic!("nonempty record should request its KDF")
	};
	let aead = pending.resume(step_response());
	let (body, tag) = seal_primitive(aead.request());
	let records::SealAfterAead::CommitmentRequested(mut pending) = aead.resume(Some((&body, tag)))
	else {
		panic!("actual detached result should request commitment")
	};
	let hash = commitment_hash(pending.transcript_mut());
	let records::SealAfterCommitment::WriteRequested(writer) = pending.resume(Some(hash)) else {
		panic!("actual hash should request writing")
	};
	let bytes = raw_write(writer.request());
	let (kernel, sealed) = writer.finish(Some(bytes));
	let sealed = sealed.unwrap();
	assert_eq!((sealed.key_id, sealed.seq), (43, kernel.send_sequence()));
	(kernel, sealed.ciphertext)
}

fn receive_record(
	kernel: ConcreteRatchetKernel,
	sequence: u64,
	ciphertext: &[u8],
	failure: Option<ReceiveFailure>,
	trace: &mut ReceiveTrace,
) -> (
	ConcreteRatchetKernel,
	Option<beaconcrypt_core::record::OpenedRecord<Vec<u8>>>,
) {
	let mut effect =
		records::begin_record_receive(kernel, sequence, ciphertext, &expected_ad(), 42);
	loop {
		effect = match effect {
			records::RecordReceiveEffect::Rejected(kernel) => return (kernel, None),
			records::RecordReceiveEffect::KdfRequested(pending) => {
				trace.kdfs += 1;
				if matches!(failure, Some(ReceiveFailure::Kdf)) {
					return (pending.cancel(), None);
				}
				pending.resume(step_response())
			}
			records::RecordReceiveEffect::CommitmentRequested(mut pending) => {
				trace.hashes += 1;
				let hash = commitment_hash(pending.transcript_mut());
				let matches = !matches!(failure, Some(ReceiveFailure::Hash))
					&& &hash == pending.supplied_commitment();
				pending.resume(matches)
			}
			records::RecordReceiveEffect::AeadRequested(pending) => {
				trace.aeads += 1;
				let plaintext = if matches!(failure, Some(ReceiveFailure::Aead)) {
					None
				} else {
					open_primitive(pending.request())
				};
				return pending.finish(plaintext);
			}
		};
	}
}

#[test]
fn composed_record_failures_roll_back_exactly_and_cached_success_rejects_replay() {
	let (sender, first) = send_record(initial_record_kernel(), b"first");
	let (sender, _) = send_record(sender, b"second");
	let (_, third) = send_record(sender, b"third");
	let mut receiver = initial_record_kernel();
	let before = kernel_snapshot(&receiver);
	for failure in [
		ReceiveFailure::Kdf,
		ReceiveFailure::Hash,
		ReceiveFailure::Aead,
	] {
		let (returned, opened) = receive_record(
			receiver,
			3,
			&third,
			Some(failure),
			&mut ReceiveTrace::default(),
		);
		assert!(opened.is_none());
		assert_eq!(kernel_snapshot(&returned), before);
		receiver = returned;
	}
	let mut changed = third.clone();
	changed[0] ^= 1;
	let (returned, opened) =
		receive_record(receiver, 3, &changed, None, &mut ReceiveTrace::default());
	assert!(opened.is_none());
	assert_eq!(kernel_snapshot(&returned), before);
	let (returned, opened) =
		receive_record(returned, 3, &third, None, &mut ReceiveTrace::default());
	let opened = opened.unwrap();
	assert_eq!(
		(opened.key_id, opened.seq, opened.plaintext.as_slice()),
		(42, 3, &b"third"[..])
	);
	assert_eq!(
		(returned.receive_sequence(), returned.receive_cache_len()),
		(3, 2)
	);
	receiver = returned;
	let before_cached = kernel_snapshot(&receiver);
	for failure in [ReceiveFailure::Hash, ReceiveFailure::Aead] {
		let mut trace = ReceiveTrace::default();
		let (returned, opened) = receive_record(receiver, 1, &first, Some(failure), &mut trace);
		assert!(opened.is_none());
		assert_eq!(trace.kdfs, 0);
		assert_eq!(kernel_snapshot(&returned), before_cached);
		receiver = returned;
	}
	let mut trace = ReceiveTrace::default();
	let (returned, opened) = receive_record(receiver, 1, &first, None, &mut trace);
	assert_eq!((trace.kdfs, trace.hashes, trace.aeads), (0, 1, 1));
	assert_eq!(opened.unwrap().plaintext, b"first");
	assert_eq!(returned.receive_cache_len(), 1);
	let before_replay = kernel_snapshot(&returned);
	let mut trace = ReceiveTrace::default();
	let (returned, opened) = receive_record(returned, 1, &first, None, &mut trace);
	assert!(opened.is_none());
	assert_eq!((trace.kdfs, trace.hashes, trace.aeads), (0, 0, 0));
	assert_eq!(kernel_snapshot(&returned), before_replay);
}
