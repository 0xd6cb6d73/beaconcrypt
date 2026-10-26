// SPDX-License-Identifier: 0BSD

use crate::{CryptoError, Result, TryCryptoRng};
use curve25519_dalek::montgomery::MontgomeryPoint;
use zeroize::Zeroizing;

pub const PUBLICKEYBYTES: usize = 32;
pub const SECRETKEYBYTES: usize = 32;
pub const SEEDBYTES: usize = 32;

crate::public_bytes!(PublicKey, PUBLICKEYBYTES);
crate::secret_bytes!(SecretKey, SECRETKEYBYTES);

pub struct KeyPair {
	pub public_key: PublicKey,
	pub secret_key: SecretKey,
}

impl KeyPair {
	fn from_secret(secret: &[u8; SECRETKEYBYTES]) -> Self {
		Self {
			public_key: MontgomeryPoint::mul_base_clamped(*secret).to_bytes().into(),
			secret_key: (*secret).into(),
		}
	}

	pub fn from_seed(seed: &[u8]) -> Result<Self> {
		let _: &[u8; SEEDBYTES] = seed.try_into().map_err(|_| CryptoError)?;
		let secret = Zeroizing::new(crate::crypto_generichash::generichash(
			seed,
			None,
			SECRETKEYBYTES,
		)?);
		Ok(Self::from_secret(
			secret.as_slice().try_into().expect("fixed-width secret"),
		))
	}

	pub fn generate_with_rng<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self> {
		let mut secret = Zeroizing::new([0; SECRETKEYBYTES]);
		rng.try_fill_bytes(&mut *secret).map_err(|_| CryptoError)?;
		Ok(Self::from_secret(&secret))
	}

	#[cfg(feature = "std")]
	pub fn generate() -> Result<Self> {
		Self::generate_with_rng(&mut crate::OsRng)
	}
}
