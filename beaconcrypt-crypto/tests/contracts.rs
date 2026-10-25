// SPDX-License-Identifier: 0BSD

use beaconcrypt_crypto::{CryptoError, crypto_aead::chacha20poly1305_ietf, crypto_sign, utils};
use zeroize::Zeroize;

#[test]
fn comparison_checks_contents_and_lengths() {
	assert!(utils::memcmp(&[], &[]));
	assert!(utils::memcmp(b"same", b"same"));
	assert!(!utils::memcmp(b"same", b"sane"));
	assert!(!utils::memcmp(b"same", b"same\0"));
}

#[test]
fn secret_encodings_are_wiped_explicitly_and_redacted() {
	let mut key = chacha20poly1305_ietf::Key::from([0xa7; 32]);
	assert_eq!(format!("{key:?}"), "Key([REDACTED])");
	key.zeroize();
	assert_eq!(key.as_bytes(), &[0; 32]);
	let mut secret = crypto_sign::SecretKey::from([0xb9; 64]);
	assert_eq!(format!("{secret:?}"), "SecretKey([REDACTED])");
	secret.zeroize();
	assert_eq!(secret.as_bytes(), &[0; 64]);
}

#[test]
fn encoded_key_and_ciphertext_imports_require_exact_widths() {
	use beaconcrypt_crypto::{crypto_kdf::hkdf::sha512, crypto_kem::mlkem768, crypto_kx};
	macro_rules! width {
		($ty:path, $size:expr) => {{
			let input = vec![0x57; $size];
			let value = <$ty>::from_bytes(&input).unwrap();
			assert_eq!(value.as_bytes().as_slice(), input);
			assert_eq!(AsRef::<[u8]>::as_ref(&value), input);
			for length in [0, $size - 1, $size + 1] {
				assert!(<$ty>::from_bytes(&vec![0; length]).is_err());
			}
		}};
	}
	width!(crypto_sign::PublicKey, 32);
	width!(crypto_sign::SecretKey, 64);
	width!(crypto_kx::PublicKey, 32);
	width!(crypto_kx::SecretKey, 32);
	width!(chacha20poly1305_ietf::Key, 32);
	width!(chacha20poly1305_ietf::Nonce, 12);
	width!(sha512::Key, 64);
	width!(mlkem768::PublicKey, 1184);
	width!(mlkem768::SecretKey, 2400);
	width!(mlkem768::Ciphertext, 1088);
	width!(mlkem768::SharedSecret, 32);
	width!(mlkem768::EncapsulationSeed, 32);
}

#[test]
fn secret_equality_and_explicit_wiping_cover_all_secret_types() {
	use beaconcrypt_crypto::{crypto_kdf::hkdf::sha512, crypto_kem::mlkem768, crypto_kx};
	macro_rules! secret {
		($ty:path, $size:expr) => {{
			let mut value = <$ty>::from([0x57; $size]);
			assert_eq!(value, value.clone());
			assert_ne!(value, <$ty>::from([0x58; $size]));
			value.zeroize();
			assert_eq!(value.as_bytes(), &[0; $size]);
		}};
	}
	secret!(crypto_sign::SecretKey, 64);
	secret!(crypto_kx::SecretKey, 32);
	secret!(chacha20poly1305_ietf::Key, 32);
	secret!(sha512::Key, 64);
	secret!(mlkem768::SecretKey, 2400);
	secret!(mlkem768::SharedSecret, 32);
	secret!(mlkem768::EncapsulationSeed, 32);
}

#[test]
fn imported_signing_keys_must_have_a_matching_public_half() {
	let original = crypto_sign::KeyPair::from_seed(&[0x27; 32]).unwrap();
	let other = crypto_sign::KeyPair::from_seed(&[0x28; 32]).unwrap();
	let mut corrupted = *original.secret_key.as_bytes();
	corrupted[32..].copy_from_slice(other.public_key.as_bytes());
	let corrupted = crypto_sign::SecretKey::from_bytes(&corrupted).unwrap();
	assert!(crypto_sign::sign_detached(b"message", &corrupted).is_err());
	assert!(crypto_sign::sign(b"message", &corrupted).is_err());
}

#[test]
fn initialization_and_error_contracts() {
	assert!(beaconcrypt_crypto::ensure_init().is_ok());
	assert_eq!(CryptoError.to_string(), "cryptographic operation failed");
}

#[cfg(feature = "std")]
#[test]
fn hosted_random_helpers_supply_bytes_and_words() {
	use beaconcrypt_crypto::{OsRng, TryRng, random};
	let mut rng = OsRng;
	let first = rng.try_next_u64().unwrap();
	let second = rng.try_next_u64().unwrap();
	assert_ne!(first, second);
	let words = core::array::from_fn::<_, 4, _>(|_| rng.try_next_u32().unwrap());
	assert_ne!(words, [words[0]; 4]);
	let first = random::bytes(32);
	assert_eq!(first.len(), 32);
	assert_ne!(first, vec![0; 32]);
	let mut second = [0; 32];
	random::try_fill_bytes(&mut second).unwrap();
	assert_ne!(second, [0; 32]);
	assert_ne!(first.as_slice(), second);
	let mut direct = [0; 32];
	rng.try_fill_bytes(&mut direct).unwrap();
	assert_ne!(direct, [0; 32]);
	assert!(random::bytes(0).is_empty());
}
