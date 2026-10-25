// SPDX-License-Identifier: 0BSD

//! The fixed primitive suite used by beaconcrypt, with portable key encodings.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub use rand_core::{TryCryptoRng, TryRng};

pub mod crypto_aead;
pub mod crypto_generichash;
pub mod crypto_kdf;
pub mod crypto_kem;
pub mod crypto_kx;
pub mod crypto_scalarmult;
pub mod crypto_sign;

/// A primitive input, authentication, allocation, or entropy failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CryptoError;

impl core::fmt::Display for CryptoError {
	fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
		f.write_str("cryptographic operation failed")
	}
}

impl core::error::Error for CryptoError {}

pub type Result<T> = core::result::Result<T, CryptoError>;

/// RustCrypto needs no global initialization; retained for source compatibility.
pub fn ensure_init() -> Result<()> {
	Ok(())
}

/// Operating-system entropy for hosted convenience constructors.
#[cfg(feature = "std")]
pub struct OsRng;

#[cfg(feature = "std")]
impl TryRng for OsRng {
	type Error = getrandom::Error;

	fn try_next_u32(&mut self) -> core::result::Result<u32, Self::Error> {
		getrandom::u32()
	}

	fn try_next_u64(&mut self) -> core::result::Result<u64, Self::Error> {
		getrandom::u64()
	}

	fn try_fill_bytes(&mut self, dst: &mut [u8]) -> core::result::Result<(), Self::Error> {
		getrandom::fill(dst)
	}
}

#[cfg(feature = "std")]
impl TryCryptoRng for OsRng {}

#[cfg(feature = "std")]
pub mod random {
	use crate::{CryptoError, Result};
	use alloc::vec::Vec;

	pub fn try_fill_bytes(bytes: &mut [u8]) -> Result<()> {
		getrandom::fill(bytes).map_err(|_| CryptoError)
	}

	pub fn fill_bytes(bytes: &mut [u8]) {
		try_fill_bytes(bytes).expect("operating-system entropy unavailable");
	}

	pub fn bytes(size: usize) -> Vec<u8> {
		let mut bytes = alloc::vec![0; size];
		fill_bytes(&mut bytes);
		bytes
	}
}

pub mod utils {
	use subtle::ConstantTimeEq;

	pub fn memcmp(left: &[u8], right: &[u8]) -> bool {
		left.ct_eq(right).into()
	}
}

macro_rules! public_bytes {
	($name:ident, $size:expr) => {
		#[derive(Clone, Debug, Eq, PartialEq)]
		pub struct $name([u8; $size]);
		impl $name {
			pub fn from_bytes(bytes: &[u8]) -> crate::Result<Self> {
				Ok(Self(bytes.try_into().map_err(|_| crate::CryptoError)?))
			}
			pub fn as_bytes(&self) -> &[u8; $size] {
				&self.0
			}
		}
		impl From<[u8; $size]> for $name {
			fn from(bytes: [u8; $size]) -> Self {
				Self(bytes)
			}
		}
		impl AsRef<[u8]> for $name {
			fn as_ref(&self) -> &[u8] {
				self.as_bytes()
			}
		}
	};
}

macro_rules! secret_bytes {
	($name:ident, $size:expr) => {
		#[derive(Clone, zeroize::Zeroize, zeroize::ZeroizeOnDrop)]
		pub struct $name([u8; $size]);
		impl $name {
			pub fn from_bytes(bytes: &[u8]) -> crate::Result<Self> {
				Ok(Self(bytes.try_into().map_err(|_| crate::CryptoError)?))
			}
			pub fn as_bytes(&self) -> &[u8; $size] {
				&self.0
			}
		}
		impl From<[u8; $size]> for $name {
			fn from(bytes: [u8; $size]) -> Self {
				Self(bytes)
			}
		}
		impl AsRef<[u8]> for $name {
			fn as_ref(&self) -> &[u8] {
				self.as_bytes()
			}
		}
		impl PartialEq for $name {
			fn eq(&self, other: &Self) -> bool {
				subtle::ConstantTimeEq::ct_eq(self.0.as_slice(), other.0.as_slice()).into()
			}
		}
		impl Eq for $name {}
		impl core::fmt::Debug for $name {
			fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
				f.write_str(concat!(stringify!($name), "([REDACTED])"))
			}
		}
	};
}

pub(crate) use {public_bytes, secret_bytes};
