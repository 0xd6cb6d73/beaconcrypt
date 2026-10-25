// SPDX-License-Identifier: 0BSD

use alloc::vec::Vec;
use curve25519_dalek::edwards::CompressedEdwardsY;
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use sha2::{Digest, Sha512};
use zeroize::Zeroizing;

use crate::{CryptoError, Result, TryCryptoRng};

pub const PUBLICKEYBYTES: usize = 32;
pub const SECRETKEYBYTES: usize = 64;
pub const SEEDBYTES: usize = 32;
pub const BYTES: usize = 64;

crate::public_bytes!(PublicKey, PUBLICKEYBYTES);
crate::secret_bytes!(SecretKey, SECRETKEYBYTES);

pub struct KeyPair {
	pub public_key: PublicKey,
	pub secret_key: SecretKey,
}

impl KeyPair {
	pub fn from_seed(seed: &[u8]) -> Result<Self> {
		let seed: &[u8; SEEDBYTES] = seed.try_into().map_err(|_| CryptoError)?;
		let key = SigningKey::from_bytes(seed);
		let encoded_secret = Zeroizing::new(key.to_keypair_bytes());
		Ok(Self {
			public_key: key.verifying_key().to_bytes().into(),
			secret_key: (*encoded_secret).into(),
		})
	}

	pub fn generate_with_rng<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self> {
		let mut seed = Zeroizing::new([0; SEEDBYTES]);
		rng.try_fill_bytes(&mut *seed).map_err(|_| CryptoError)?;
		Self::from_seed(&*seed)
	}

	#[cfg(feature = "std")]
	pub fn generate() -> Result<Self> {
		Self::generate_with_rng(&mut crate::OsRng)
	}
}

pub fn secret_key_to_seed(secret_key: &SecretKey) -> Result<[u8; SEEDBYTES]> {
	Ok(secret_key.0[..SEEDBYTES]
		.try_into()
		.expect("fixed-width seed"))
}

pub fn sign_detached(message: &[u8], secret_key: &SecretKey) -> Result<[u8; BYTES]> {
	let key = SigningKey::from_keypair_bytes(secret_key.as_bytes()).map_err(|_| CryptoError)?;
	Ok(key.sign(message).to_bytes())
}

pub fn sign(message: &[u8], secret_key: &SecretKey) -> Result<Vec<u8>> {
	let signature = sign_detached(message, secret_key)?;
	let capacity = BYTES.checked_add(message.len()).ok_or(CryptoError)?;
	let mut signed = Vec::new();
	signed
		.try_reserve_exact(capacity)
		.map_err(|_| CryptoError)?;
	signed.extend_from_slice(&signature);
	signed.extend_from_slice(message);
	Ok(signed)
}

pub fn verify_detached(signature: &[u8; BYTES], message: &[u8], public_key: &PublicKey) -> bool {
	let Ok(key) = VerifyingKey::from_bytes(public_key.as_bytes()) else {
		return false;
	};
	// libsodium accepts only canonical encodings and rejects small-order keys/R.
	if key.to_edwards().compress().as_bytes() != public_key.as_bytes() {
		return false;
	}
	key.verify_strict(message, &Signature::from_bytes(signature))
		.is_ok()
}

pub fn verify(signed_message: &[u8], public_key: &PublicKey) -> Option<Vec<u8>> {
	let signature = signed_message.get(..BYTES)?.try_into().ok()?;
	let message = &signed_message[BYTES..];
	verify_detached(signature, message, public_key).then(|| message.to_vec())
}

pub fn ed25519_pk_to_curve25519(public_key: &PublicKey) -> Result<[u8; 32]> {
	let point = CompressedEdwardsY(*public_key.as_bytes())
		.decompress()
		.ok_or(CryptoError)?;
	if point.compress().as_bytes() != public_key.as_bytes()
		|| point.is_small_order()
		|| !point.is_torsion_free()
	{
		return Err(CryptoError);
	}
	Ok(point.to_montgomery().to_bytes())
}

pub fn ed25519_sk_to_curve25519(secret_key: &SecretKey) -> Result<[u8; 32]> {
	let hash = Zeroizing::new(<[u8; 64]>::from(Sha512::digest(&secret_key.0[..SEEDBYTES])));
	let mut scalar: [u8; 32] = hash[..32].try_into().expect("fixed-width hash prefix");
	scalar[0] &= 248;
	scalar[31] &= 127;
	scalar[31] |= 64;
	Ok(scalar)
}
