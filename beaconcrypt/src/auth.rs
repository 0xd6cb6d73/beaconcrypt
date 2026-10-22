// SPDX-License-Identifier: 0BSD

//! ML-DSA-65 identities and domain-separated registration transcript authentication.

use beaconcrypt_parse::{InitKex, KexResponse};
use libsodium_rs::{crypto_generichash, ensure_init, random};
use ml_dsa::{EncodedVerifyingKey, Keypair, MlDsa65, Signature, SigningKey, VerifyingKey};
use zeroize::Zeroizing;

pub const MLDSA_PUBLIC_KEY_LEN: usize = 1952;
pub const MLDSA_SIGNATURE_LEN: usize = 3309;
pub(crate) const TRANSCRIPT_HASH_LEN: usize = 64;

type TranscriptHash = [u8; TRANSCRIPT_HASH_LEN];

const SIGNING_CONTEXT: &[u8] = b"beaconcrypt registration auth v1";
const INIT_TRANSCRIPT_DOMAIN: &[u8] = b"beaconcrypt ML-DSA-65 init transcript v1\0";
const RESPONSE_TRANSCRIPT_DOMAIN: &[u8] = b"beaconcrypt ML-DSA-65 response transcript v1\0";

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
			.sign_deterministic(&signature_input(role, transcript), SIGNING_CONTEXT)
			.ok()
			.map(|signature| signature.encode().to_vec())
	}
}

#[derive(Clone, Copy)]
pub(crate) enum AuthRole {
	Beacon,
	Server,
}

impl AuthRole {
	fn label(self) -> &'static [u8] {
		match self {
			Self::Beacon => b"beaconcrypt v1 beacon registration",
			Self::Server => b"beaconcrypt v1 server registration",
		}
	}
}

fn signature_input(role: AuthRole, transcript: &TranscriptHash) -> Vec<u8> {
	let mut input = Vec::with_capacity(64 + role.label().len() + 1 + transcript.len());
	input.extend_from_slice(&[b' '; 64]);
	input.extend_from_slice(role.label());
	input.push(0);
	input.extend_from_slice(transcript);
	input
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
		&signature_input(role, transcript),
		SIGNING_CONTEXT,
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

fn hash_field(state: &mut crypto_generichash::State, field: &[u8]) -> Option<()> {
	state.update(&u64::try_from(field.len()).ok()?.to_le_bytes());
	state.update(field);
	Some(())
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
	beacon_auth_key: &[u8; MLDSA_PUBLIC_KEY_LEN],
	server_auth_key: &[u8; MLDSA_PUBLIC_KEY_LEN],
) -> Option<TranscriptHash> {
	let mut state = hash_state()?;
	state.update(INIT_TRANSCRIPT_DOMAIN);
	state.update(&server_kid.to_le_bytes());
	state.update(pinned_server_ed);
	state.update(beacon_auth_key);
	state.update(server_auth_key);
	for field in [
		init.identity_key,
		init.pre_key,
		init.one_time_key,
		init.pq_key,
	] {
		hash_field(&mut state, field)?;
	}
	finish_hash(state)
}

/// Hash the complete decoded response after its request hash, excluding the authentication signature.
pub(crate) fn response_transcript_hash(
	init_hash: &TranscriptHash,
	response: &KexResponse<'_>,
) -> Option<TranscriptHash> {
	let mut state = hash_state()?;
	state.update(RESPONSE_TRANSCRIPT_DOMAIN);
	state.update(init_hash);
	for field in [
		response.identity_key,
		response.ephemeral_key,
		response.kem_cipher_text,
		response.app_cipher_text,
	] {
		hash_field(&mut state, field)?;
	}
	state.update(&response.key_id.to_le_bytes());
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
			&signature_input(AuthRole::Server, &transcript),
			b"different context",
			&decoded
		));
		assert!(!verifier.verify_with_context(
			&signature_input(AuthRole::Server, &transcript),
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
				},
				kid,
				ed,
				beacon,
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
	fn variable_field_boundaries_are_authenticated() {
		let public_key = [0; MLDSA_PUBLIC_KEY_LEN];
		let hash = |identity, prekey| {
			init_transcript_hash(
				&InitKex {
					identity_key: identity,
					pre_key: prekey,
					one_time_key: &[],
					pq_key: &[],
				},
				0,
				&[0; 32],
				&public_key,
				&public_key,
			)
			.unwrap()
		};
		assert_ne!(hash(b"ab", b"c"), hash(b"a", b"bc"));
		let fingerprint = public_key_hash(&public_key).unwrap();
		assert_eq!(
			fingerprint.as_slice(),
			crypto_generichash::generichash(&public_key, None, 64).unwrap()
		);
		assert!(public_key_hash(&public_key[..1951]).is_none());
	}
}
