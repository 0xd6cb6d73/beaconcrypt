// SPDX-License-Identifier: 0BSD

pub mod chacha20poly1305_ietf {
	use crate::{CryptoError, Result};
	use alloc::vec::Vec;
	use chacha20poly1305::{ChaCha20Poly1305, KeyInit, aead::AeadInOut};

	pub const KEYBYTES: usize = 32;
	pub const NPUBBYTES: usize = 12;
	pub const ABYTES: usize = 16;

	crate::secret_bytes!(Key, KEYBYTES);
	crate::public_bytes!(Nonce, NPUBBYTES);

	impl Nonce {
		pub fn try_from_slice(bytes: &[u8]) -> Result<Self> {
			Self::from_bytes(bytes)
		}
	}

	pub fn encrypt_detached(
		message: &[u8],
		ad: Option<&[u8]>,
		nonce: &Nonce,
		key: &Key,
	) -> Result<(Vec<u8>, Vec<u8>)> {
		let mut ciphertext = Vec::new();
		ciphertext
			.try_reserve_exact(message.len())
			.map_err(|_| CryptoError)?;
		ciphertext.extend_from_slice(message);
		let tag = ChaCha20Poly1305::new(key.as_bytes().into())
			.encrypt_inout_detached(
				nonce.as_bytes().into(),
				ad.unwrap_or_default(),
				ciphertext.as_mut_slice().into(),
			)
			.map_err(|_| CryptoError)?;
		Ok((ciphertext, tag.to_vec()))
	}

	pub fn decrypt(
		ciphertext: &[u8],
		ad: Option<&[u8]>,
		nonce: &Nonce,
		key: &Key,
	) -> Result<Vec<u8>> {
		let split = ciphertext.len().checked_sub(ABYTES).ok_or(CryptoError)?;
		let (ciphertext, tag) = ciphertext.split_at(split);
		let tag: &[u8; ABYTES] = tag.try_into().expect("fixed-width authentication tag");
		let mut plaintext = zeroize::Zeroizing::new(Vec::new());
		plaintext
			.try_reserve_exact(ciphertext.len())
			.map_err(|_| CryptoError)?;
		plaintext.extend_from_slice(ciphertext);
		ChaCha20Poly1305::new(key.as_bytes().into())
			.decrypt_inout_detached(
				nonce.as_bytes().into(),
				ad.unwrap_or_default(),
				plaintext.as_mut_slice().into(),
				tag.into(),
			)
			.map_err(|_| CryptoError)?;
		Ok(core::mem::take(&mut *plaintext))
	}
}
