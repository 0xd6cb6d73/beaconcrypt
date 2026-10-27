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

		/// Expand into caller-owned storage without allocating. An oversized output is rejected before it is modified.
		pub fn expand_into(output: &mut [u8], info: Option<&[u8]>, key: &Key) -> Result<()> {
			::hkdf::Hkdf::<Sha512>::from_prk(key.as_bytes())
				.map_err(|_| CryptoError)?
				.expand(info.unwrap_or_default(), output)
				.map_err(|_| CryptoError)
		}

		pub fn expand(length: usize, info: Option<&[u8]>, key: &Key) -> Result<Vec<u8>> {
			if length > 255 * 64 {
				return Err(CryptoError);
			}
			let mut output = Zeroizing::new(Vec::new());
			output.try_reserve_exact(length).map_err(|_| CryptoError)?;
			output.resize(length, 0);
			expand_into(&mut output, info, key)?;
			Ok(core::mem::take(&mut *output))
		}
	}
}
