// SPDX-License-Identifier: 0BSD

pub mod mlkem768 {
	use crate::{CryptoError, Result, TryCryptoRng};
	#[allow(deprecated)]
	use ml_kem::ExpandedKeyEncoding;
	use ml_kem::{Decapsulate, DecapsulationKey768, EncapsulationKey768, KeyExport};
	use zeroize::Zeroizing;

	pub const PUBLICKEYBYTES: usize = 1184;
	pub const SECRETKEYBYTES: usize = 2400;
	pub const CIPHERTEXTBYTES: usize = 1088;
	pub const SHAREDSECRETBYTES: usize = 32;
	pub const SEEDBYTES: usize = 64;

	crate::public_bytes!(PublicKey, PUBLICKEYBYTES);
	crate::public_bytes!(Ciphertext, CIPHERTEXTBYTES);
	crate::secret_bytes!(SecretKey, SECRETKEYBYTES);
	crate::secret_bytes!(SharedSecret, SHAREDSECRETBYTES);
	crate::secret_bytes!(EncapsulationSeed, 32);

	pub struct KeyPair {
		pub public_key: PublicKey,
		pub secret_key: SecretKey,
	}

	impl KeyPair {
		#[allow(deprecated)]
		pub fn from_seed(seed: &[u8]) -> Result<Self> {
			let seed: &[u8; SEEDBYTES] = seed.try_into().map_err(|_| CryptoError)?;
			let key = DecapsulationKey768::from_seed((*seed).into());
			let expanded = Zeroizing::new(key.to_expanded_bytes());
			Ok(Self {
				public_key: <[u8; PUBLICKEYBYTES]>::from(key.encapsulation_key().to_bytes()).into(),
				secret_key: SecretKey::from_bytes(expanded.as_slice())?,
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

	pub fn encapsulate_deterministic(
		public: &PublicKey,
		seed: &EncapsulationSeed,
	) -> Result<(Ciphertext, SharedSecret)> {
		let key = EncapsulationKey768::new(public.as_bytes().into()).map_err(|_| CryptoError)?;
		let (ciphertext, secret) = key.encapsulate_deterministic(seed.as_bytes().into());
		let secret = Zeroizing::new(secret);
		Ok((
			<[u8; CIPHERTEXTBYTES]>::from(ciphertext).into(),
			SharedSecret::from_bytes(secret.as_slice())?,
		))
	}

	pub fn encapsulate_with_rng<R: TryCryptoRng + ?Sized>(
		public: &PublicKey,
		rng: &mut R,
	) -> Result<(Ciphertext, SharedSecret)> {
		let mut seed = EncapsulationSeed::from([0; 32]);
		rng.try_fill_bytes(&mut seed.0).map_err(|_| CryptoError)?;
		encapsulate_deterministic(public, &seed)
	}

	#[cfg(feature = "std")]
	pub fn encapsulate(public: &PublicKey) -> Result<(Ciphertext, SharedSecret)> {
		encapsulate_with_rng(public, &mut crate::OsRng)
	}

	#[allow(deprecated)]
	pub fn decapsulate(ciphertext: &Ciphertext, secret: &SecretKey) -> Result<SharedSecret> {
		let key = DecapsulationKey768::from_expanded_bytes(secret.as_bytes().into())
			.map_err(|_| CryptoError)?;
		let shared = Zeroizing::new(key.decapsulate(ciphertext.as_bytes().into()));
		SharedSecret::from_bytes(shared.as_slice())
	}
}
