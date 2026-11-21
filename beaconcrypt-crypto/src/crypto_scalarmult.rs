// SPDX-License-Identifier: 0BSD

use crate::{CryptoError, Result};
use curve25519_dalek::montgomery::MontgomeryPoint;
use subtle::ConstantTimeEq;
use zeroize::Zeroizing;

pub const BYTES: usize = 32;

pub fn scalarmult(secret: &[u8], public: &[u8]) -> Result<[u8; BYTES]> {
	let secret = Zeroizing::new(<[u8; 32]>::try_from(secret).map_err(|_| CryptoError)?);
	let public: [u8; 32] = public.try_into().map_err(|_| CryptoError)?;
	let shared = MontgomeryPoint(public).mul_clamped(*secret).to_bytes();
	if bool::from(shared.ct_eq(&[0; BYTES])) {
		return Err(CryptoError);
	}
	Ok(shared)
}
