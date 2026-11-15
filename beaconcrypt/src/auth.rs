// SPDX-License-Identifier: 0BSD

//! ML-DSA-65 identities and domain-separated registration transcript authentication.

#[cfg(any(feature = "server", test))]
use alloc::vec::Vec;

use beaconcrypt_core::authentication as transcript;
#[cfg(test)]
use beaconcrypt_parse::{InitKex, KexResponse};

use beaconcrypt_crypto::{TryCryptoRng, crypto_generichash};
#[cfg(any(feature = "beacon", test))]
use ml_dsa::{EncodedVerifyingKey, Signature, VerifyingKey};
use ml_dsa::{Keypair, MlDsa65, SigningKey};
#[cfg(test)]
pub(crate) use transcript::AuthRole;
use zeroize::Zeroizing;

// Literal exports keep cbindgen's C size constants available to the bindings.
pub const MLDSA_PUBLIC_KEY_LEN: usize = 1952;
pub const MLDSA_SIGNATURE_LEN: usize = 3309;
const _: () = assert!(MLDSA_PUBLIC_KEY_LEN == transcript::MLDSA_PUBLIC_KEY_LEN);
const _: () = assert!(MLDSA_SIGNATURE_LEN == transcript::MLDSA_SIGNATURE_LEN);
pub(crate) const TRANSCRIPT_HASH_LEN: usize = transcript::TRANSCRIPT_HASH_LEN;

type TranscriptHash = [u8; TRANSCRIPT_HASH_LEN];

/// A secret ML-DSA-65 identity reconstructed from a 32-byte seed.
///
/// The `ml-dsa` zeroize feature clears the retained seed and expanded secret key on drop.
pub struct MldsaIdentity {
	key: SigningKey<MlDsa65>,
}

impl MldsaIdentity {
	/// Generate an identity with the operating system's cryptographic random generator.
	#[cfg(feature = "std")]
	pub fn generate() -> Result<Self, crate::KeyGenError> {
		Self::generate_with_rng(&mut beaconcrypt_crypto::OsRng)
	}

	/// Generate an identity with caller-provided cryptographic entropy.
	pub fn generate_with_rng<R: TryCryptoRng + ?Sized>(
		rng: &mut R,
	) -> Result<Self, crate::KeyGenError> {
		let mut seed = Zeroizing::new([0; 32]);
		rng.try_fill_bytes(seed.as_mut())
			.map_err(|_| crate::KeyGenError)?;
		Ok(Self::from_seed(*seed))
	}

	/// Reconstruct an identity from secret, uniformly generated seed bytes.
	/// This does not derive a key from a password.
	pub fn from_seed(seed: [u8; 32]) -> Self {
		let seed = Zeroizing::new(seed);
		Self {
			key: SigningKey::from_seed((&*seed).into()),
		}
	}

	/// Export the secret seed into a buffer that is cleared when dropped.
	pub fn to_seed(&self) -> Zeroizing<[u8; 32]> {
		let seed: &[u8; 32] = self.key.as_seed().into();
		Zeroizing::new(*seed)
	}

	/// Return the canonical ML-DSA-65 public key encoding.
	pub fn public_key(&self) -> [u8; MLDSA_PUBLIC_KEY_LEN] {
		self.key.verifying_key().encode().into()
	}

	#[cfg(test)]
	pub(crate) fn sign(&self, role: AuthRole, transcript: &TranscriptHash) -> Option<Vec<u8>> {
		self.key
			.expanded_key()
			.sign_deterministic(
				&transcript::build_signature_input(role, transcript),
				&transcript::SIGNING_CONTEXT,
			)
			.ok()
			.map(|signature| signature.encode().to_vec())
	}
}

#[cfg(test)]
pub(crate) fn verify(
	public_key: &[u8],
	role: AuthRole,
	transcript: &TranscriptHash,
	signature: &[u8],
) -> bool {
	let Ok(encoded_key) = <&EncodedVerifyingKey<MlDsa65>>::try_from(public_key) else {
		return false;
	};
	let Ok(signature) = Signature::<MlDsa65>::try_from(signature) else {
		return false;
	};
	VerifyingKey::decode(encoded_key).verify_with_context(
		&transcript::build_signature_input(role, transcript),
		&transcript::SIGNING_CONTEXT,
		&signature,
	)
}

fn hash_state() -> Option<crypto_generichash::State> {
	crypto_generichash::State::new(None, TRANSCRIPT_HASH_LEN).ok()
}

fn finish_hash(mut state: crypto_generichash::State) -> Option<TranscriptHash> {
	state.finalize().try_into().ok()
}

/// Hash the remaining decoded request and the Server authentication pin; variable fields have LE64 lengths.
#[cfg(test)]
pub(crate) fn init_transcript_hash(
	init: &InitKex<'_>,
	server_kid: u64,
	pinned_server_ed: &[u8; 32],
	server_auth_key: &[u8; MLDSA_PUBLIC_KEY_LEN],
) -> Option<TranscriptHash> {
	let fields = transcript::InitFields {
		identity_key: init.identity_key.try_into().ok()?,
		pre_key: init.pre_key.try_into().ok()?,
		one_time_key: init.one_time_key.try_into().ok()?,
		pq_key: init.pq_key.try_into().ok()?,
	};
	let bytes =
		transcript::build_init_transcript(fields, server_kid, pinned_server_ed, server_auth_key);
	let mut state = hash_state()?;
	state.update(&bytes);
	finish_hash(state)
}

/// Hash the core's ordered response parts, excluding the authentication signature.
#[cfg(test)]
pub(crate) fn response_transcript_hash(
	init_hash: &TranscriptHash,
	response: &KexResponse<'_>,
) -> Option<TranscriptHash> {
	let fields = transcript::ResponseFields {
		identity_key: response.identity_key.try_into().ok()?,
		ephemeral_key: response.ephemeral_key.try_into().ok()?,
		kem_cipher_text: response.kem_cipher_text.try_into().ok()?,
		app_cipher_text: response.app_cipher_text,
		key_id: response.key_id,
	};
	let transcript = transcript::build_response_transcript(init_hash, fields)?;
	let mut state = hash_state()?;
	for part in transcript.parts() {
		state.update(part);
	}
	finish_hash(state)
}

// Interpret the core's exact primitive requests; legacy digest helpers are test-only.

pub(crate) fn execute_hash(
	request: &beaconcrypt_core::registration::HashRequest<'_>,
) -> Option<TranscriptHash> {
	let mut state = hash_state()?;
	match request {
		beaconcrypt_core::registration::HashRequest::Single(input) => state.update(input),
		beaconcrypt_core::registration::HashRequest::Triple(parts) => {
			for part in parts {
				state.update(part);
			}
		}
	}
	finish_hash(state)
}

pub(crate) fn server_pin(
	binding: beaconcrypt_core::pqxdh::ServerBinding,
	public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
) -> Option<beaconcrypt_core::session::ServerAuthenticationPin> {
	Some(beaconcrypt_core::registration::begin_server_pin(
		binding, public_key,
	))
}

#[cfg(any(feature = "beacon", test))]
pub(crate) fn verify_requested(
	request: &beaconcrypt_core::registration::MldsaVerificationRequest<'_>,
) -> bool {
	let Ok(encoded_key) = <&EncodedVerifyingKey<MlDsa65>>::try_from(request.public_key.as_slice())
	else {
		return false;
	};
	let Ok(signature) = Signature::<MlDsa65>::try_from(request.signature.as_slice()) else {
		return false;
	};
	VerifyingKey::decode(encoded_key).verify_with_context(
		request.input,
		&request.context,
		&signature,
	)
}

#[cfg(any(feature = "server", test))]
impl MldsaIdentity {
	pub(crate) fn sign_requested(
		&self,
		request: &beaconcrypt_core::registration::MldsaSigningRequest<'_>,
	) -> Option<Vec<u8>> {
		if self.public_key() != *request.public_key {
			return None;
		}
		self.key
			.expanded_key()
			.sign_deterministic(request.input, &request.context)
			.ok()
			.map(|signature| signature.encode().to_vec())
	}
}

#[cfg(feature = "server")]
pub(crate) fn authenticate_init(
	pin: beaconcrypt_core::session::ServerAuthenticationPin,
	packet: beaconcrypt_core::registration::InitPacket<'_>,
) -> Option<beaconcrypt_core::registration::AuthenticatedInit> {
	use beaconcrypt_core::registration::InitAuthentication;
	let mut effect = beaconcrypt_core::registration::begin_init_authentication(pin, packet);
	loop {
		effect = match effect {
			InitAuthentication::Rejected => return None,
			InitAuthentication::Accepted(authenticated) => return Some(authenticated),
			InitAuthentication::HashRequested(pending) => {
				let hash = execute_hash(&pending.request());
				pending.resume(hash)
			}

			InitAuthentication::Ed25519VerificationRequested(pending) => {
				let request = pending.request();
				let opened = (|| {
					let public_key =
						beaconcrypt_crypto::crypto_sign::PublicKey::from_bytes(request.public_key)
							.ok()?;
					beaconcrypt_crypto::crypto_sign::verify(request.signed, &public_key)
				})();
				pending.resume(opened.as_deref())
			}
		};
	}
}

#[cfg(feature = "beacon")]
pub(crate) fn authenticate_response<'a>(
	pending: beaconcrypt_core::registration::BeaconPending,
	packet: Option<beaconcrypt_core::registration::ResponsePacket<'a>>,
) -> Result<
	beaconcrypt_core::registration::AuthenticatedResponse<'a>,
	beaconcrypt_core::pqxdh::BeaconAborted,
> {
	let pending = beaconcrypt_core::registration::begin_response_authentication(pending, packet)?;
	let digest = execute_hash(&pending.request());
	let pending = pending.resume(digest)?;
	let verified = verify_requested(&pending.request());
	let pending = pending.resume(verified)?;
	let digest = execute_hash(&pending.request());
	pending.resume(digest)
}

/// Deterministic bytes and injected failures for entropy-routing tests only.
#[cfg(test)]
pub(crate) struct TestRng {
	pub(crate) calls: usize,
	fail_after: usize,
}

#[cfg(test)]
impl TestRng {
	pub(crate) fn new(fail_after: usize) -> Self {
		Self {
			calls: 0,
			fail_after,
		}
	}
}

#[cfg(test)]
impl beaconcrypt_crypto::TryRng for TestRng {
	type Error = beaconcrypt_crypto::CryptoError;

	fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
		let mut bytes = [0; 4];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u32::from_le_bytes(bytes))
	}

	fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
		let mut bytes = [0; 8];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u64::from_le_bytes(bytes))
	}

	fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Self::Error> {
		if self.calls >= self.fail_after {
			return Err(beaconcrypt_crypto::CryptoError);
		}
		self.calls += 1;
		for (offset, byte) in bytes.iter_mut().enumerate() {
			*byte = (offset as u8).wrapping_add(self.calls as u8);
		}
		Ok(())
	}
}

#[cfg(test)]
impl TryCryptoRng for TestRng {}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn requested_hashing_preserves_single_inputs_and_all_three_ordered_parts() {
		use beaconcrypt_core::registration::HashRequest;
		let expected = crypto_generichash::generichash(b"firstsecondthird", None, 64).unwrap();
		let single = execute_hash(&HashRequest::Single(b"firstsecondthird")).unwrap();
		let triple = execute_hash(&HashRequest::Triple([b"first", b"second", b"third"])).unwrap();
		assert_eq!(single.as_slice(), expected);
		assert_eq!(triple, single);
		assert_ne!(
			execute_hash(&HashRequest::Triple([b"second", b"first", b"third"])).unwrap(),
			single
		);
		assert_ne!(
			execute_hash(&HashRequest::Triple([b"first", b"second", b""])).unwrap(),
			single
		);
	}

	#[test]
	fn requested_signing_uses_the_selected_identity_and_exact_context() {
		use beaconcrypt_core::registration::{MldsaSigningRequest, MldsaVerificationRequest};
		let identity = MldsaIdentity::from_seed([7; 32]);
		let public_key = identity.public_key();
		let input = transcript::build_signature_input(AuthRole::Server, &[11; 64]);
		let request = MldsaSigningRequest {
			public_key: &public_key,
			role: AuthRole::Server,
			input: &input,
			context: transcript::SIGNING_CONTEXT,
		};
		let signature = identity.sign_requested(&request).unwrap();
		let mut verification = MldsaVerificationRequest {
			public_key: &public_key,
			input: &input,
			context: transcript::SIGNING_CONTEXT,
			signature: signature.as_slice().try_into().unwrap(),
		};
		assert!(verify_requested(&verification));
		verification.context[0] ^= 1;
		assert!(!verify_requested(&verification));
		let changed = MldsaSigningRequest {
			context: verification.context,
			..request
		};
		let changed_signature = identity.sign_requested(&changed).unwrap();
		verification.signature = changed_signature.as_slice().try_into().unwrap();
		assert!(verify_requested(&verification));
		verification.context = transcript::SIGNING_CONTEXT;
		assert!(!verify_requested(&verification));
		for other_key in [[0; MLDSA_PUBLIC_KEY_LEN], [u8::MAX; MLDSA_PUBLIC_KEY_LEN]] {
			assert_ne!(public_key, other_key);
			assert!(
				identity
					.sign_requested(&MldsaSigningRequest {
						public_key: &other_key,
						..request
					})
					.is_none()
			);
		}
	}

	#[test]
	fn identity_generation_uses_fallible_caller_entropy() {
		assert!(MldsaIdentity::generate_with_rng(&mut TestRng::new(0)).is_err());
		let mut rng = TestRng::new(1);
		let identity = MldsaIdentity::generate_with_rng(&mut rng).unwrap();
		let seed = core::array::from_fn(|offset| offset as u8 + 1);
		assert_eq!(
			identity.public_key(),
			MldsaIdentity::from_seed(seed).public_key()
		);
		assert_eq!(rng.calls, 1);
	}

	#[test]
	fn identity_seed_roundtrip_retains_signing_key() {
		let identity = MldsaIdentity::from_seed([7; 32]);
		let restored = MldsaIdentity::from_seed(*identity.to_seed());
		assert_eq!(*identity.to_seed(), [7; 32]);
		assert_eq!(identity.public_key(), restored.public_key());
		let transcript = [11; TRANSCRIPT_HASH_LEN];
		let signature = restored.sign(AuthRole::Beacon, &transcript).unwrap();
		assert_eq!(signature.len(), MLDSA_SIGNATURE_LEN);
		assert!(verify(
			&identity.public_key(),
			AuthRole::Beacon,
			&transcript,
			&signature
		));
		let generated = MldsaIdentity::generate().unwrap();
		let restored = MldsaIdentity::from_seed(*generated.to_seed());
		assert_eq!(generated.public_key(), restored.public_key());
		assert_ne!(
			generated.public_key(),
			MldsaIdentity::generate().unwrap().public_key()
		);
	}

	#[test]
	fn signature_binds_key_role_context_and_transcript() {
		let identity = MldsaIdentity::from_seed([3; 32]);
		let public_key = identity.public_key();
		let transcript = [19; TRANSCRIPT_HASH_LEN];
		let signature = identity.sign(AuthRole::Server, &transcript).unwrap();
		assert!(verify(
			&public_key,
			AuthRole::Server,
			&transcript,
			&signature
		));
		assert!(!verify(
			&public_key,
			AuthRole::Beacon,
			&transcript,
			&signature
		));
		assert!(!verify(
			&MldsaIdentity::from_seed([4; 32]).public_key(),
			AuthRole::Server,
			&transcript,
			&signature
		));
		let mut changed = transcript;
		changed[0] ^= 1;
		assert!(!verify(&public_key, AuthRole::Server, &changed, &signature));
		let decoded = Signature::<MlDsa65>::try_from(signature.as_slice()).unwrap();
		let verifier = identity.key.verifying_key();
		let mut expected_input = vec![b' '; 64];
		expected_input.extend_from_slice(b"beaconcrypt v1 server registration\0");
		expected_input.extend_from_slice(&transcript);
		assert!(verifier.verify_with_context(
			&expected_input,
			b"beaconcrypt registration auth v1",
			&decoded
		));
		assert!(!verifier.verify_with_context(
			&transcript::build_signature_input(AuthRole::Server, &transcript),
			b"different context",
			&decoded
		));
		assert!(!verifier.verify_with_context(
			&transcript::build_signature_input(AuthRole::Server, &transcript),
			&[],
			&decoded
		));
		let mut corrupted = signature.clone();
		corrupted[0] ^= 1;
		assert!(!verify(
			&public_key,
			AuthRole::Server,
			&transcript,
			&corrupted
		));
		assert!(!verify(
			&public_key,
			AuthRole::Server,
			&transcript,
			&signature[..3308]
		));
		corrupted = signature.clone();
		corrupted.push(0);
		assert!(!verify(
			&public_key,
			AuthRole::Server,
			&transcript,
			&corrupted
		));
		assert!(!verify(
			&public_key[..1951],
			AuthRole::Server,
			&transcript,
			&signature
		));
	}

	#[test]
	fn init_digest_binds_exact_fields_and_server_pin() {
		let fields = [vec![1; 33], vec![2; 98], vec![3; 98], vec![4; 1249]];
		let hash = |fields: &[Vec<u8>; 4], kid, ed, key| {
			init_transcript_hash(
				&InitKex {
					identity_key: &fields[0],
					pre_key: &fields[1],
					one_time_key: &fields[2],
					pq_key: &fields[3],
				},
				kid,
				ed,
				key,
			)
		};
		let expected = hash(&fields, 42, &[5; 32], &[7; 1952]).unwrap();
		let mut independent = b"beaconcrypt ML-DSA-65 init transcript v2\0".to_vec();
		independent.extend_from_slice(&42_u64.to_le_bytes());
		independent.extend_from_slice(&[5; 32]);
		independent.extend_from_slice(&[7; 1952]);
		for field in &fields {
			independent.extend_from_slice(&(field.len() as u64).to_le_bytes());
			independent.extend_from_slice(field);
		}
		assert_eq!(independent.len(), 3543);
		assert_eq!(
			expected.as_slice(),
			crypto_generichash::generichash(&independent, None, 64).unwrap()
		);
		for i in 0..4 {
			for offset in 0..fields[i].len() {
				let mut changed = fields.clone();
				changed[i][offset] ^= 1;
				assert_ne!(hash(&changed, 42, &[5; 32], &[7; 1952]), Some(expected));
			}
			for len in [0, fields[i].len() - 1, fields[i].len() + 1] {
				let mut changed = fields.clone();
				changed[i].resize(len, 0);
				assert!(hash(&changed, 42, &[5; 32], &[7; 1952]).is_none());
			}
		}
		assert_ne!(hash(&fields, 43, &[5; 32], &[7; 1952]), Some(expected));
		assert_ne!(hash(&fields, 42, &[6; 32], &[7; 1952]), Some(expected));
		assert_ne!(hash(&fields, 42, &[5; 32], &[8; 1952]), Some(expected));
	}

	#[test]
	fn response_digest_preserves_complete_signed_ciphertext_and_assigned_id() {
		let fields = [vec![1; 32], vec![2; 32], vec![3; 1088], vec![4; 89]];
		let hash = |init, fields: &[Vec<u8>; 4], kid| {
			response_transcript_hash(
				init,
				&KexResponse {
					identity_key: &fields[0],
					ephemeral_key: &fields[1],
					kem_cipher_text: &fields[2],
					app_cipher_text: &fields[3],
					key_id: kid,
					signature: &[],
				},
			)
		};
		let expected = hash(&[17; 64], &fields, 42).unwrap();
		let mut independent = b"beaconcrypt ML-DSA-65 response transcript v2\0".to_vec();
		independent.extend_from_slice(&[17; 64]);
		for field in &fields {
			independent.extend_from_slice(&(field.len() as u64).to_le_bytes());
			independent.extend_from_slice(field);
		}
		independent.extend_from_slice(&42_u64.to_le_bytes());
		assert_eq!(
			expected.as_slice(),
			crypto_generichash::generichash(&independent, None, 64).unwrap()
		);
		for i in 0..4 {
			let mut changed = fields.clone();
			changed[i][0] ^= 1;
			assert_ne!(hash(&[17; 64], &changed, 42), Some(expected));
			if i < 3 {
				changed[i].pop();
				assert!(hash(&[17; 64], &changed, 42).is_none());
			}
		}
		assert_ne!(hash(&[18; 64], &fields, 42), Some(expected));
		assert_ne!(hash(&[17; 64], &fields, 43), Some(expected));
	}
}
