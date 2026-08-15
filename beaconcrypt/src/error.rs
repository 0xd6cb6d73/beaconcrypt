// SPDX-License-Identifier: 0BSD

use std::{error::Error, fmt};

#[derive(Debug, Clone)]
pub struct KeyGenError;

impl fmt::Display for KeyGenError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Key generation failure")
	}
}

impl Error for KeyGenError {}

#[derive(Debug, Clone)]
pub struct EncodingError;

impl fmt::Display for EncodingError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Encoding failure")
	}
}

impl Error for EncodingError {}

#[derive(Debug, Clone)]
pub struct DecodingError;

impl fmt::Display for DecodingError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Decoding failure")
	}
}

impl Error for DecodingError {}

#[derive(Debug, Clone)]
pub struct SignatureError;

impl fmt::Display for SignatureError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Signature failure")
	}
}

impl Error for SignatureError {}

#[derive(Debug, Clone)]
pub struct CipherTextError;

impl fmt::Display for CipherTextError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Ciphertext failure")
	}
}

impl Error for CipherTextError {}

#[derive(Debug, Clone)]
pub struct DecryptionError;

impl fmt::Display for DecryptionError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Decryption failure")
	}
}

impl Error for DecryptionError {}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn errors_implement_std_error() {
		fn assert_error<T: Error>() {}

		assert_error::<KeyGenError>();
		assert_error::<EncodingError>();
		assert_error::<DecodingError>();
		assert_error::<SignatureError>();
		assert_error::<CipherTextError>();
		assert_error::<DecryptionError>();
	}

	#[test]
	fn errors_have_stable_human_readable_messages() {
		assert_eq!(KeyGenError.to_string(), "Key generation failure");
		assert_eq!(EncodingError.to_string(), "Encoding failure");
		assert_eq!(DecodingError.to_string(), "Decoding failure");
		assert_eq!(SignatureError.to_string(), "Signature failure");
		assert_eq!(CipherTextError.to_string(), "Ciphertext failure");
		assert_eq!(DecryptionError.to_string(), "Decryption failure");
	}
}
