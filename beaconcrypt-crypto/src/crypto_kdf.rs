// SPDX-License-Identifier: 0BSD

pub mod hkdf {
	pub mod sha512 {
		use crate::{CryptoError, Result};
		use alloc::vec::Vec;
		use sha2::Sha512;
		use zeroize::Zeroizing;

		crate::secret_bytes!(Key, 64);

		pub fn extract(salt: Option<&[u8]>, input: &[u8]) -> Result<Key> {
			let (prk, _) = ::hkdf::Hkdf::<Sha512>::extract(salt, input);
			let prk = Zeroizing::new(prk);
			Key::from_bytes(prk.as_slice())
		}

		pub fn expand(length: usize, info: Option<&[u8]>, key: &Key) -> Result<Vec<u8>> {
			if length > 255 * 64 {
				return Err(CryptoError);
			}
			let mut output = Zeroizing::new(Vec::new());
			output.try_reserve_exact(length).map_err(|_| CryptoError)?;
			output.resize(length, 0);
			::hkdf::Hkdf::<Sha512>::from_prk(key.as_bytes())
				.map_err(|_| CryptoError)?
				.expand(info.unwrap_or_default(), &mut output)
				.map_err(|_| CryptoError)?;
			Ok(core::mem::take(&mut *output))
		}
	}
}
