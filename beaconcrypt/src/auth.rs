// SPDX-License-Identifier: 0BSD

//! ML-DSA-65 identities and domain-separated registration transcript authentication.

use beaconcrypt_core::authentication as transcript;
use beaconcrypt_parse::{InitKex, KexResponse};

use libsodium_rs::{crypto_generichash, ensure_init, random};
use ml_dsa::{EncodedVerifyingKey, Keypair, MlDsa65, Signature, SigningKey, VerifyingKey};
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
	/// Generate an identity with libsodium's cryptographic random generator.
	pub fn generate() -> Result<Self, crate::KeyGenError> {
		ensure_init().map_err(|_| crate::KeyGenError)?;
		let mut seed = Zeroizing::new([0; 32]);
		random::fill_bytes(seed.as_mut());
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
	ensure_init().ok()?;
	crypto_generichash::State::new(None, TRANSCRIPT_HASH_LEN).ok()
}

fn finish_hash(mut state: crypto_generichash::State) -> Option<TranscriptHash> {
	state.finalize().try_into().ok()
}

/// Fingerprint an exact ML-DSA-65 public key with unkeyed BLAKE2b-512.
pub(crate) fn public_key_hash(public_key: &[u8]) -> Option<TranscriptHash> {
	if public_key.len() != MLDSA_PUBLIC_KEY_LEN {
		return None;
	}
	let mut state = hash_state()?;
	state.update(public_key);
	finish_hash(state)
}

/// Hash the decoded request and both authentication pins; variable fields have LE64 lengths.
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
		mldsa_public_key: init.mldsa_public_key.try_into().ok()?,
	};
	let bytes =
		transcript::build_init_transcript(fields, server_kid, pinned_server_ed, server_auth_key);
	let mut state = hash_state()?;
	state.update(&bytes);
	finish_hash(state)
}

/// Hash the core's ordered response parts, excluding the authentication signature.
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

#[cfg(test)]
mod tests {
	use super::*;

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
	fn init_hash_binds_every_field_and_both_pins() {
		let fields = [vec![1; 33], vec![2; 98], vec![3; 98], vec![4; 1249]];
		let server_ed = [5; 32];
		let beacon_key = [6; MLDSA_PUBLIC_KEY_LEN];
		let server_key = [7; MLDSA_PUBLIC_KEY_LEN];
		let hash = |fields: &[Vec<u8>; 4], kid, ed, beacon, server| {
			init_transcript_hash(
				&InitKex {
					identity_key: &fields[0],
					pre_key: &fields[1],
					one_time_key: &fields[2],
					pq_key: &fields[3],
					mldsa_public_key: beacon,
					signature: &[],
				},
				kid,
				ed,
				server,
			)
			.unwrap()
		};
		let expected = hash(&fields, 42, &server_ed, &beacon_key, &server_key);
		for index in 0..fields.len() {
			let mut altered = fields.clone();
			altered[index][0] ^= 1;
			assert_ne!(
				expected,
				hash(&altered, 42, &server_ed, &beacon_key, &server_key)
			);
		}
		assert_ne!(
			expected,
			hash(&fields, 43, &server_ed, &beacon_key, &server_key)
		);
		let mut altered_ed = server_ed;
		altered_ed[0] ^= 1;
		assert_ne!(
			expected,
			hash(&fields, 42, &altered_ed, &beacon_key, &server_key)
		);
		let mut altered_key = beacon_key;
		altered_key[0] ^= 1;
		assert_ne!(
			expected,
			hash(&fields, 42, &server_ed, &altered_key, &server_key)
		);
		let mut altered_server_key = server_key;
		altered_server_key[0] ^= 1;
		assert_ne!(
			expected,
			hash(&fields, 42, &server_ed, &beacon_key, &altered_server_key)
		);
	}

	#[test]
	fn response_hash_binds_request_and_every_response_field() {
		let fields = [vec![1; 32], vec![2; 32], vec![3; 1088], vec![4; 89]];
		let init_hash = [17; TRANSCRIPT_HASH_LEN];
		let hash = |init, fields: &[Vec<u8>; 4], kid| {
			response_transcript_hash(
				init,
				&KexResponse {
					key_id: kid,
					identity_key: &fields[0],
					ephemeral_key: &fields[1],
					kem_cipher_text: &fields[2],
					app_cipher_text: &fields[3],
					signature: &[],
				},
			)
			.unwrap()
		};
		let expected = hash(&init_hash, &fields, 42);
		for index in 0..fields.len() {
			let mut altered = fields.clone();
			altered[index][0] ^= 1;
			assert_ne!(expected, hash(&init_hash, &altered, 42));
		}
		let mut changed_init = init_hash;
		changed_init[0] ^= 1;
		assert_ne!(expected, hash(&changed_init, &fields, 42));
		assert_ne!(expected, hash(&init_hash, &fields, 43));
	}

	#[test]
	fn malformed_fixed_transcript_fields_are_rejected() {
		let server_key = [7; MLDSA_PUBLIC_KEY_LEN];
		let init_fields = [
			vec![1; 33],
			vec![2; 98],
			vec![3; 98],
			vec![4; 1249],
			vec![6; 1952],
		];
		let init_hash = |fields: &[Vec<u8>; 5]| {
			init_transcript_hash(
				&InitKex {
					identity_key: &fields[0],
					pre_key: &fields[1],
					one_time_key: &fields[2],
					pq_key: &fields[3],
					mldsa_public_key: &fields[4],
					signature: &[],
				},
				42,
				&[5; 32],
				&server_key,
			)
		};
		assert!(init_hash(&init_fields).is_some());
		for (index, field) in init_fields.iter().enumerate() {
			for bad_length in [0, field.len() - 1, field.len() + 1] {
				let mut malformed = init_fields.clone();
				malformed[index].resize(bad_length, 0);
				assert!(
					init_hash(&malformed).is_none(),
					"Init field {index}, length {bad_length}"
				);
			}
		}
		let response_fields = [vec![1; 32], vec![2; 32], vec![3; 1088]];
		let response_hash = |fields: &[Vec<u8>; 3]| {
			response_transcript_hash(
				&[17; 64],
				&KexResponse {
					identity_key: &fields[0],
					ephemeral_key: &fields[1],
					kem_cipher_text: &fields[2],
					app_cipher_text: &[],
					key_id: 42,
					signature: &[],
				},
			)
		};
		assert!(response_hash(&response_fields).is_some());
		for (index, field) in response_fields.iter().enumerate() {
			for bad_length in [0, field.len() - 1, field.len() + 1] {
				let mut malformed = response_fields.clone();
				malformed[index].resize(bad_length, 0);
				assert!(
					response_hash(&malformed).is_none(),
					"Response field {index}, length {bad_length}"
				);
			}
		}
		let public_key = [0; MLDSA_PUBLIC_KEY_LEN];
		let fingerprint = public_key_hash(&public_key).unwrap();
		assert_eq!(
			fingerprint.as_slice(),
			crypto_generichash::generichash(&public_key, None, 64).unwrap()
		);
		assert!(public_key_hash(&public_key[..1951]).is_none());
	}

	#[test]
	fn core_transcripts_preserve_independent_blake2b_known_answers_and_exclude_signatures() {
		let init = InitKex {
			identity_key: &[1; 33],
			pre_key: &[2; 98],
			one_time_key: &[3; 98],
			pq_key: &[4; 1249],
			mldsa_public_key: &[6; 1952],
			signature: &[],
		};
		let init_hash = init_transcript_hash(&init, 42, &[5; 32], &[7; 1952]).unwrap();
		// Independently calculated with Python hashlib.blake2b over the former adapter formula.
		assert_eq!(
			init_hash,
			[
				0x10, 0x00, 0xe9, 0xb4, 0x23, 0x18, 0x62, 0x2b, 0xcb, 0x83, 0x37, 0x6d, 0x00, 0x5e,
				0x45, 0x2a, 0x09, 0xd6, 0xf1, 0xe8, 0x56, 0xd0, 0x6c, 0x9e, 0xb4, 0x19, 0x6f, 0xe1,
				0x4a, 0xda, 0x33, 0x77, 0xe3, 0x27, 0xb9, 0xf0, 0xc0, 0xc8, 0x7b, 0x17, 0xb6, 0xc7,
				0x8e, 0x9b, 0x7c, 0xee, 0xe6, 0x80, 0x3d, 0x1f, 0x43, 0x4e, 0x97, 0x51, 0xdc, 0x2f,
				0xfd, 0xb0, 0x6d, 0xa2, 0xf0, 0x12, 0x08, 0x90
			]
		);
		let mut old_init = b"beaconcrypt ML-DSA-65 init transcript v1\0".to_vec();
		old_init.extend_from_slice(&42_u64.to_le_bytes());
		old_init.extend_from_slice(&[5; 32]);
		old_init.extend_from_slice(&[6; 1952]);
		old_init.extend_from_slice(&[7; 1952]);
		for field in [
			init.identity_key,
			init.pre_key,
			init.one_time_key,
			init.pq_key,
		] {
			old_init.extend_from_slice(&(field.len() as u64).to_le_bytes());
			old_init.extend_from_slice(field);
		}
		assert_eq!(old_init.len(), 5495);
		assert_eq!(
			init_hash.as_slice(),
			crypto_generichash::generichash(&old_init, None, 64).unwrap()
		);
		assert_eq!(
			init_transcript_hash(
				&InitKex {
					signature: &[0x5a; 3309],
					..init
				},
				42,
				&[5; 32],
				&[7; 1952]
			),
			Some(init_hash)
		);

		let response = KexResponse {
			identity_key: &[1; 32],
			ephemeral_key: &[2; 32],
			kem_cipher_text: &[3; 1088],
			app_cipher_text: &[4; 89],
			key_id: 42,
			signature: &[],
		};
		let response_hash = response_transcript_hash(&[17; 64], &response).unwrap();
		assert_eq!(
			response_hash,
			[
				0x89, 0xba, 0xd2, 0xb7, 0xee, 0x00, 0x2e, 0x96, 0x8b, 0x38, 0x6d, 0xc3, 0x61, 0x9e,
				0xe2, 0xd4, 0xa8, 0x6f, 0xe6, 0x07, 0x31, 0x96, 0x6e, 0xee, 0x6c, 0x46, 0x2b, 0x8a,
				0x3c, 0xfd, 0xb3, 0x0f, 0xe8, 0x5f, 0x87, 0x6e, 0x85, 0x3b, 0x7e, 0x40, 0x62, 0x71,
				0xd7, 0x6d, 0xce, 0x63, 0x44, 0x5f, 0x6d, 0xd2, 0x2a, 0xa2, 0x09, 0x62, 0x1a, 0xb9,
				0x70, 0x3c, 0x99, 0x27, 0x66, 0x37, 0xd3, 0xd2
			]
		);
		let mut old_response = b"beaconcrypt ML-DSA-65 response transcript v1\0".to_vec();
		old_response.extend_from_slice(&[17; 64]);
		for field in [
			response.identity_key,
			response.ephemeral_key,
			response.kem_cipher_text,
			response.app_cipher_text,
		] {
			old_response.extend_from_slice(&(field.len() as u64).to_le_bytes());
			old_response.extend_from_slice(field);
		}
		old_response.extend_from_slice(&42_u64.to_le_bytes());
		assert_eq!(old_response.len(), 1390);
		assert_eq!(
			response_hash.as_slice(),
			crypto_generichash::generichash(&old_response, None, 64).unwrap()
		);
		assert_eq!(
			response_transcript_hash(
				&[17; 64],
				&KexResponse {
					signature: &[0xa5; 3309],
					..response
				}
			),
			Some(response_hash)
		);
	}
}
