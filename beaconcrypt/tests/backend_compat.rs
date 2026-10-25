// SPDX-License-Identifier: 0BSD

//! The pinned native implementation is an independent test oracle only.

use beaconcrypt_crypto as portable;
use libsodium_rs as sodium;

// Only the development oracle needs these compatibility symbols on Windows GNU.
// They are deliberately absent from the production RustCrypto library.
#[cfg(all(windows, target_env = "gnu"))]
mod windows_oracle {
	use core::ffi::{c_int, c_void};

	#[unsafe(no_mangle)]
	unsafe extern "C" fn memset_explicit(
		dest: *mut c_void,
		value: c_int,
		count: usize,
	) -> *mut c_void {
		unsafe { core::ptr::write_bytes(dest, value as u8, count) };
		core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
		dest
	}

	#[link(name = "bcrypt")]
	unsafe extern "system" {
		fn BCryptGenRandom(algorithm: *mut c_void, output: *mut u8, length: u32, flags: u32)
		-> i32;
	}

	#[allow(non_snake_case)]
	#[unsafe(no_mangle)]
	unsafe extern "system" fn SystemFunction036(output: *mut c_void, length: u32) -> u8 {
		let status = unsafe { BCryptGenRandom(core::ptr::null_mut(), output.cast(), length, 2) };
		u8::from(status >= 0)
	}
}

#[test]
fn ed25519_seed_signatures_and_converted_identity_match_sodium() {
	for seed_byte in [0, 1, 42, 127, 255] {
		let seed = [seed_byte; 32];
		let native = sodium::crypto_sign::KeyPair::from_seed(&seed).unwrap();
		let rust = portable::crypto_sign::KeyPair::from_seed(&seed).unwrap();
		assert_eq!(rust.public_key.as_bytes(), native.public_key.as_bytes());
		assert_eq!(rust.secret_key.as_bytes(), native.secret_key.as_bytes());
		assert_eq!(
			portable::crypto_sign::ed25519_pk_to_curve25519(&rust.public_key).unwrap(),
			sodium::crypto_sign::ed25519_pk_to_curve25519(&native.public_key).unwrap()
		);
		assert_eq!(
			portable::crypto_sign::ed25519_sk_to_curve25519(&rust.secret_key).unwrap(),
			sodium::crypto_sign::ed25519_sk_to_curve25519(&native.secret_key).unwrap()
		);
		for message in [&b""[..], &b"registration key\0binary"[..], &[0xa5; 129][..]] {
			let native_signed = sodium::crypto_sign::sign(message, &native.secret_key).unwrap();
			let rust_signed = portable::crypto_sign::sign(message, &rust.secret_key).unwrap();
			assert_eq!(rust_signed, native_signed);
			assert_eq!(
				portable::crypto_sign::sign_detached(message, &rust.secret_key).unwrap(),
				sodium::crypto_sign::sign_detached(message, &native.secret_key).unwrap()
			);
			assert_eq!(
				portable::crypto_sign::verify(&native_signed, &rust.public_key).unwrap(),
				message
			);
			assert_eq!(
				sodium::crypto_sign::verify(&rust_signed, &native.public_key).unwrap(),
				message
			);
			for offset in [0, 31, 32, 63] {
				let mut corrupt = native_signed.clone();
				corrupt[offset] ^= 0x80;
				assert_eq!(
					portable::crypto_sign::verify(&corrupt, &rust.public_key),
					sodium::crypto_sign::verify(&corrupt, &native.public_key)
				);
				assert!(portable::crypto_sign::verify(&corrupt, &rust.public_key).is_none());
			}
			assert!(
				portable::crypto_sign::verify(&native_signed[..63], &rust.public_key).is_none()
			);
		}
	}
}

#[test]
fn malformed_ed25519_points_and_noncanonical_signatures_match_sodium() {
	let valid = sodium::crypto_sign::KeyPair::from_seed(&[17; 32]).unwrap();
	let signature = sodium::crypto_sign::sign_detached(b"message", &valid.secret_key).unwrap();
	let mut points = vec![[0; 32], [0xff; 32], [1; 32]];
	let mut identity = [0; 32];
	identity[0] = 1;
	points.push(identity);
	// p and p+1 are noncanonical Edwards encodings; the high bit is the x sign.
	for first in [0xed, 0xee, 0xff] {
		for sign in [0x7f, 0xff] {
			let mut point = [0xff; 32];
			point[0] = first;
			point[31] = sign;
			points.push(point);
		}
	}
	// This includes off-curve points and points with a nontrivial torsion component.
	points.extend((0..=255).map(|byte| [byte; 32]));
	for point in points {
		let native = sodium::crypto_sign::PublicKey::from_bytes(&point).unwrap();
		let rust = portable::crypto_sign::PublicKey::from_bytes(&point).unwrap();
		assert_eq!(
			portable::crypto_sign::ed25519_pk_to_curve25519(&rust).ok(),
			sodium::crypto_sign::ed25519_pk_to_curve25519(&native).ok(),
			"conversion of {point:02x?}"
		);
		assert_eq!(
			portable::crypto_sign::verify_detached(&signature, b"message", &rust),
			sodium::crypto_sign::verify_detached(&signature, b"message", &native)
		);
	}
	let rust = portable::crypto_sign::PublicKey::from_bytes(valid.public_key.as_bytes()).unwrap();
	for replacement in [[0; 32], [0xff; 32], identity] {
		for offset in [0, 32] {
			let mut malformed = signature;
			malformed[offset..offset + 32].copy_from_slice(&replacement);
			assert_eq!(
				portable::crypto_sign::verify_detached(&malformed, b"message", &rust),
				sodium::crypto_sign::verify_detached(&malformed, b"message", &valid.public_key)
			);
		}
	}
}

#[test]
fn x25519_seed_derivation_aliases_and_low_order_rejection_match_sodium() {
	for seed in [[0; 32], [17; 32], [255; 32]] {
		let native = sodium::crypto_kx::KeyPair::from_seed(&seed).unwrap();
		let rust = portable::crypto_kx::KeyPair::from_seed(&seed).unwrap();
		assert_eq!(rust.public_key.as_bytes(), native.public_key.as_bytes());
		assert_eq!(rust.secret_key.as_bytes(), native.secret_key.as_bytes());
		let mut points = vec![[0; 32], [0xff; 32], [1; 32]];
		let mut one = [0; 32];
		one[0] = 1;
		points.push(one);
		for first in 0xec..=0xff {
			let mut point = [0xff; 32];
			point[0] = first;
			point[31] = 0x7f;
			points.push(point);
		}
		let mut valid: [u8; 32] = native.public_key.as_bytes().try_into().unwrap();
		points.push(valid);
		valid[31] ^= 0x80;
		points.push(valid);
		for point in points {
			assert_eq!(
				portable::crypto_scalarmult::scalarmult(rust.secret_key.as_bytes(), &point).ok(),
				sodium::crypto_scalarmult::scalarmult(native.secret_key.as_bytes(), &point).ok(),
				"X25519 input {point:02x?}"
			);
		}
	}
	for width in [0, 31, 33] {
		assert!(portable::crypto_scalarmult::scalarmult(&vec![0; width], &[9; 32]).is_err());
		assert!(portable::crypto_scalarmult::scalarmult(&[9; 32], &vec![0; width]).is_err());
	}
}

#[test]
fn mlkem768_serialization_encapsulation_and_implicit_rejection_match_sodium() {
	use portable::crypto_kem::mlkem768 as rust;
	use sodium::crypto_kem::mlkem768 as native;
	for byte in [0, 42, 255] {
		let seed = [byte; 64];
		let native_pair = native::KeyPair::from_seed(&seed).unwrap();
		let rust_pair = rust::KeyPair::from_seed(&seed).unwrap();
		assert_eq!(
			rust_pair.public_key.as_bytes(),
			native_pair.public_key.as_bytes()
		);
		assert_eq!(
			rust_pair.secret_key.as_bytes(),
			native_pair.secret_key.as_bytes()
		);
		let randomness = [byte ^ 0xa5; 32];
		let native_random = native::EncapsulationSeed::from_bytes(&randomness).unwrap();
		let rust_random = rust::EncapsulationSeed::from_bytes(&randomness).unwrap();
		let (native_cipher, native_shared) =
			native::encapsulate_deterministic(&native_pair.public_key, &native_random).unwrap();
		let (rust_cipher, rust_shared) =
			rust::encapsulate_deterministic(&rust_pair.public_key, &rust_random).unwrap();
		assert_eq!(rust_cipher.as_bytes(), native_cipher.as_bytes());
		assert_eq!(rust_shared.as_bytes(), native_shared.as_bytes());
		assert_eq!(
			rust::decapsulate(
				&rust::Ciphertext::from_bytes(native_cipher.as_bytes()).unwrap(),
				&rust_pair.secret_key
			)
			.unwrap()
			.as_bytes(),
			native_shared.as_bytes()
		);
		assert_eq!(
			native::decapsulate(
				&native::Ciphertext::from_bytes(rust_cipher.as_bytes()).unwrap(),
				&native_pair.secret_key
			)
			.unwrap()
			.as_bytes(),
			rust_shared.as_bytes()
		);
		for offset in [0, 1, 543, 1087] {
			let mut corrupted = *native_cipher.as_bytes();
			corrupted[offset] ^= 1;
			let native_rejected = native::decapsulate(
				&native::Ciphertext::from_bytes(&corrupted).unwrap(),
				&native_pair.secret_key,
			)
			.unwrap();
			let rust_rejected = rust::decapsulate(
				&rust::Ciphertext::from_bytes(&corrupted).unwrap(),
				&rust_pair.secret_key,
			)
			.unwrap();
			assert_eq!(rust_rejected.as_bytes(), native_rejected.as_bytes());
			assert_ne!(rust_rejected.as_bytes(), rust_shared.as_bytes());
		}
	}
	let malformed = [0xff; native::PUBLICKEYBYTES];
	let native_key = native::PublicKey::from_bytes(&malformed).unwrap();
	let rust_key = rust::PublicKey::from_bytes(&malformed).unwrap();
	assert!(
		native::encapsulate_deterministic(
			&native_key,
			&native::EncapsulationSeed::from_bytes(&[0; 32]).unwrap()
		)
		.is_err()
	);
	assert!(
		rust::encapsulate_deterministic(
			&rust_key,
			&rust::EncapsulationSeed::from_bytes(&[0; 32]).unwrap()
		)
		.is_err()
	);
}

#[test]
fn hkdf_sha512_salt_context_and_output_boundaries_match_sodium() {
	use portable::crypto_kdf::hkdf::sha512 as rust;
	use sodium::crypto_kdf::hkdf::sha512 as native;
	for salt in [None, Some(&b""[..]), Some(&b"salt\0bytes"[..])] {
		for ikm in [&b""[..], &[0x42; 32][..], &[0xa5; 192][..]] {
			let native_prk = native::extract(salt, ikm).unwrap();
			let rust_prk = rust::extract(salt, ikm).unwrap();
			for info in [None, Some(&b""[..]), Some(&b"domain\0bytes"[..])] {
				for size in [0, 1, 32, 64, 76, 129, 255 * 64, 255 * 64 + 1] {
					assert_eq!(
						rust::expand(size, info, &rust_prk).ok(),
						native::expand(size, info, &native_prk).ok(),
						"salt {salt:?}, info {info:?}, size {size}"
					);
				}
			}
		}
	}
}

#[test]
fn configured_length_blake2b_and_streaming_match_sodium() {
	for output_len in [0, 15, 16, 31, 32, 48, 64, 65] {
		for message in [&b""[..], &b"transcript\0bytes"[..], &[0x33; 257][..]] {
			let native = sodium::crypto_generichash::generichash(message, None, output_len).ok();
			let rust = portable::crypto_generichash::generichash(message, None, output_len).ok();
			assert_eq!(rust, native);
			if let Some(expected) = native {
				let mut stream =
					portable::crypto_generichash::State::new(None, output_len).unwrap();
				for chunk in message.chunks(7) {
					stream.update(chunk);
				}
				assert_eq!(stream.finalize(), expected);
			}
		}
	}
	let full = portable::crypto_generichash::generichash(b"digest", None, 64).unwrap();
	let short = portable::crypto_generichash::generichash(b"digest", None, 32).unwrap();
	assert_ne!(short, full[..32]);
}

#[test]
fn blake2b_key_lengths_and_keyed_streaming_match_sodium() {
	for key_len in [0, 1, 15, 16, 32, 64, 65] {
		let key = vec![0x5a; key_len];
		for output_len in [16, 32, 64] {
			for message in [&b""[..], &[0x55; 129][..]] {
				let expected =
					sodium::crypto_generichash::generichash(message, Some(&key), output_len).ok();
				assert_eq!(
					portable::crypto_generichash::generichash(message, Some(&key), output_len).ok(),
					expected
				);
				if let Some(expected) = expected {
					let mut state =
						portable::crypto_generichash::State::new(Some(&key), output_len).unwrap();
					for chunk in message.chunks(13) {
						state.update(chunk);
					}
					assert_eq!(state.finalize(), expected);
				}
			}
		}
	}
}

struct TestRng {
	byte: u8,
	fail: bool,
}

impl portable::TryRng for TestRng {
	type Error = portable::CryptoError;

	fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
		let mut bytes = [0; 4];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u32::from_le_bytes(bytes))
	}

	fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
		let mut bytes = [0; 8];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u64::from_le_bytes(bytes))
	}

	fn try_fill_bytes(&mut self, output: &mut [u8]) -> Result<(), Self::Error> {
		// An entropy source may modify its destination before reporting failure.
		output.fill(self.byte);
		if self.fail {
			return Err(portable::CryptoError);
		}
		Ok(())
	}
}

// Predictable bytes are intentionally confined to this reproducible test fixture.
impl portable::TryCryptoRng for TestRng {}

#[test]
fn caller_entropy_drives_keys_and_encapsulation_and_errors_are_reported() {
	use portable::{crypto_kem::mlkem768, crypto_kx, crypto_sign};
	let mut rng = TestRng {
		byte: 0x67,
		fail: false,
	};
	let ed = crypto_sign::KeyPair::generate_with_rng(&mut rng).unwrap();
	let ed_expected = sodium::crypto_sign::KeyPair::from_seed(&[0x67; 32]).unwrap();
	assert_eq!(ed.public_key.as_bytes(), ed_expected.public_key.as_bytes());
	let kx = crypto_kx::KeyPair::generate_with_rng(&mut rng).unwrap();
	assert_eq!(kx.secret_key.as_bytes(), &[0x67; 32]);
	let mut base = [0; 32];
	base[0] = 9;
	assert_eq!(
		kx.public_key.as_bytes(),
		&sodium::crypto_scalarmult::scalarmult(&[0x67; 32], &base).unwrap()
	);
	let kem = mlkem768::KeyPair::generate_with_rng(&mut rng).unwrap();
	let kem_expected = sodium::crypto_kem::mlkem768::KeyPair::from_seed(&[0x67; 64]).unwrap();
	assert_eq!(
		kem.public_key.as_bytes(),
		kem_expected.public_key.as_bytes()
	);
	let (ciphertext, shared) = mlkem768::encapsulate_with_rng(&kem.public_key, &mut rng).unwrap();
	let (expected_ciphertext, expected_shared) =
		sodium::crypto_kem::mlkem768::encapsulate_deterministic(
			&kem_expected.public_key,
			&sodium::crypto_kem::mlkem768::EncapsulationSeed::from_bytes(&[0x67; 32]).unwrap(),
		)
		.unwrap();
	assert_eq!(ciphertext.as_bytes(), expected_ciphertext.as_bytes());
	assert_eq!(shared.as_bytes(), expected_shared.as_bytes());
	rng.fail = true;
	assert!(crypto_sign::KeyPair::generate_with_rng(&mut rng).is_err());
	assert!(crypto_kx::KeyPair::generate_with_rng(&mut rng).is_err());
	assert!(mlkem768::KeyPair::generate_with_rng(&mut rng).is_err());
	assert!(mlkem768::encapsulate_with_rng(&kem.public_key, &mut rng).is_err());
}

#[test]
fn fixed_width_inputs_reject_truncation_and_extension() {
	macro_rules! check {
		($type:path, $width:expr) => {{
			let bytes = vec![0x79; $width];
			let value = <$type>::from_bytes(&bytes).unwrap();
			assert_eq!(value.as_bytes().as_slice(), bytes);
			for width in [0, $width - 1, $width + 1] {
				assert!(<$type>::from_bytes(&vec![0x79; width]).is_err());
			}
		}};
	}
	check!(portable::crypto_sign::PublicKey, 32);
	check!(portable::crypto_sign::SecretKey, 64);
	check!(portable::crypto_kx::PublicKey, 32);
	check!(portable::crypto_kx::SecretKey, 32);
	check!(portable::crypto_kem::mlkem768::PublicKey, 1184);
	check!(portable::crypto_kem::mlkem768::SecretKey, 2400);
	check!(portable::crypto_kem::mlkem768::Ciphertext, 1088);
	check!(portable::crypto_kem::mlkem768::SharedSecret, 32);
	check!(portable::crypto_kem::mlkem768::EncapsulationSeed, 32);
	check!(portable::crypto_kdf::hkdf::sha512::Key, 64);
	check!(portable::crypto_aead::chacha20poly1305_ietf::Key, 32);
	check!(portable::crypto_aead::chacha20poly1305_ietf::Nonce, 12);
	for width in [0, 31, 33, 63, 65] {
		if width != 32 {
			assert!(portable::crypto_sign::KeyPair::from_seed(&vec![0; width]).is_err());
			assert!(portable::crypto_kx::KeyPair::from_seed(&vec![0; width]).is_err());
		}
		assert!(portable::crypto_kem::mlkem768::KeyPair::from_seed(&vec![0; width]).is_err());
	}
	assert!(portable::crypto_aead::chacha20poly1305_ietf::Nonce::try_from_slice(&[0; 11]).is_err());
	assert!(portable::crypto_aead::chacha20poly1305_ietf::Nonce::try_from_slice(&[0; 13]).is_err());
}

#[test]
fn malformed_local_secret_material_is_rejected_before_cryptography() {
	use portable::{crypto_kem::mlkem768, crypto_sign};
	let pair = crypto_sign::KeyPair::from_seed(&[0x21; 32]).unwrap();
	assert_eq!(
		crypto_sign::secret_key_to_seed(&pair.secret_key).unwrap(),
		[0x21; 32]
	);
	let mut inconsistent_ed = *pair.secret_key.as_bytes();
	inconsistent_ed[32] ^= 1;
	let inconsistent_ed = crypto_sign::SecretKey::from_bytes(&inconsistent_ed).unwrap();
	assert!(crypto_sign::sign_detached(b"message", &inconsistent_ed).is_err());
	assert!(crypto_sign::sign(b"message", &inconsistent_ed).is_err());

	let kem = mlkem768::KeyPair::from_seed(&[0x22; 64]).unwrap();
	let (ciphertext, _) = mlkem768::encapsulate_deterministic(
		&kem.public_key,
		&mlkem768::EncapsulationSeed::from_bytes(&[0x23; 32]).unwrap(),
	)
	.unwrap();
	let mut wrong_public_hash = *kem.secret_key.as_bytes();
	wrong_public_hash[2336] ^= 1;
	assert!(
		mlkem768::decapsulate(
			&ciphertext,
			&mlkem768::SecretKey::from_bytes(&wrong_public_hash).unwrap()
		)
		.is_err()
	);
	let mut invalid_public_coefficients = *kem.secret_key.as_bytes();
	invalid_public_coefficients[1152..1184].fill(0xff);
	assert!(
		mlkem768::decapsulate(
			&ciphertext,
			&mlkem768::SecretKey::from_bytes(&invalid_public_coefficients).unwrap()
		)
		.is_err()
	);
	// These stricter local-key checks are deliberate: sodium's raw key wrappers
	// admit width-correct inconsistent key material. Generated keys interoperate.
}

#[test]
fn secret_wrappers_redact_debug_and_support_explicit_erasure() {
	use zeroize::{Zeroize, ZeroizeOnDrop};
	fn drops_secret<T: ZeroizeOnDrop>(_: &T) {}
	macro_rules! check {
		($type:path, $width:expr, $debug:literal) => {{
			let mut key = <$type>::from_bytes(&[0x7b; $width]).unwrap();
			drops_secret(&key);
			assert_eq!(format!("{key:?}"), concat!($debug, "([REDACTED])"));
			let clone = key.clone();
			assert_eq!(key, clone);
			key.zeroize();
			assert_eq!(key.as_bytes(), &[0; $width]);
			assert_ne!(key, clone);
		}};
	}
	check!(portable::crypto_sign::SecretKey, 64, "SecretKey");
	check!(portable::crypto_kx::SecretKey, 32, "SecretKey");
	check!(portable::crypto_kem::mlkem768::SecretKey, 2400, "SecretKey");
	check!(
		portable::crypto_kem::mlkem768::SharedSecret,
		32,
		"SharedSecret"
	);
	check!(
		portable::crypto_kem::mlkem768::EncapsulationSeed,
		32,
		"EncapsulationSeed"
	);
	check!(portable::crypto_kdf::hkdf::sha512::Key, 64, "Key");
	check!(portable::crypto_aead::chacha20poly1305_ietf::Key, 32, "Key");
	assert!(portable::utils::memcmp(&[], &[]));
	assert!(portable::utils::memcmp(b"abc", b"abc"));
	assert!(!portable::utils::memcmp(b"abc", b"abd"));
	assert!(!portable::utils::memcmp(b"abc", b"abc\0"));
}

#[test]
fn aead_ciphertext_tags_and_authentication_failures_match_sodium() {
	use portable::crypto_aead::chacha20poly1305_ietf as rust;
	use sodium::crypto_aead::chacha20poly1305_ietf as native;
	let native_key = native::Key::from_bytes(&[0x42; 32]).unwrap();
	let rust_key = rust::Key::from_bytes(&[0x42; 32]).unwrap();
	let native_nonce = native::Nonce::try_from_slice(&[0x24; 12]).unwrap();
	let rust_nonce = rust::Nonce::try_from_slice(&[0x24; 12]).unwrap();
	for message in [&b""[..], &b"record"[..], &[0x17; 257][..]] {
		for ad in [None, Some(&b""[..]), Some(&[0x55; 281][..])] {
			let (native_cipher, native_tag) =
				native::encrypt_detached(message, ad, &native_nonce, &native_key).unwrap();
			let (rust_cipher, rust_tag) =
				rust::encrypt_detached(message, ad, &rust_nonce, &rust_key).unwrap();
			assert_eq!(rust_cipher, native_cipher);
			assert_eq!(rust_tag.as_slice(), native_tag.as_slice());
			let mut combined = native_cipher;
			combined.extend_from_slice(&native_tag);
			assert_eq!(
				rust::decrypt(&combined, ad, &rust_nonce, &rust_key).unwrap(),
				message
			);
			assert_eq!(
				native::decrypt(&combined, ad, &native_nonce, &native_key).unwrap(),
				message
			);
			for offset in [0, combined.len() - 1] {
				let mut corrupted = combined.clone();
				corrupted[offset] ^= 1;
				assert!(rust::decrypt(&corrupted, ad, &rust_nonce, &rust_key).is_err());
			}
			assert!(rust::decrypt(&combined, Some(b"other"), &rust_nonce, &rust_key).is_err());
			assert!(rust::decrypt(&combined, ad, &rust::Nonce::from([0; 12]), &rust_key).is_err());
			assert!(rust::decrypt(&combined[..15], ad, &rust_nonce, &rust_key).is_err());
		}
	}
}

#[cfg(all(feature = "beacon", feature = "server"))]
mod protocol {
	use super::sodium;
	use beaconcrypt::{Beacon, ProviderBeacon, ProviderServer, Server};
	use beaconcrypt_parse::{CryptoFrame, InitKex, KexResponse};
	use ml_dsa::{EncodedVerifyingKey, Keypair, MlDsa65, Signature, SigningKey, VerifyingKey};

	const SERVER_ID: u64 = 19;
	const SERVER_SEED: [u8; 32] = [0x51; 32];
	const AUTH_SEED: [u8; 32] = [0x52; 32];
	const PQ_DOMAIN: &[u8] = b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768";
	const RATCHET_DOMAIN: &[u8] = b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305";

	fn hash(bytes: &[u8]) -> [u8; 64] {
		sodium::crypto_generichash::generichash(bytes, None, 64)
			.unwrap()
			.try_into()
			.unwrap()
	}

	fn hkdf(input: &[u8], info: &[u8], size: usize) -> Vec<u8> {
		let prk = sodium::crypto_kdf::hkdf::sha512::extract(None, input).unwrap();
		sodium::crypto_kdf::hkdf::sha512::expand(size, Some(info), &prk).unwrap()
	}

	fn append_field(bytes: &mut Vec<u8>, field: &[u8]) {
		bytes.extend_from_slice(&(field.len() as u64).to_le_bytes());
		bytes.extend_from_slice(field);
	}

	fn init_hash(init: InitKex<'_>, server_ed: &[u8], server_auth: &[u8]) -> [u8; 64] {
		let mut bytes = b"beaconcrypt ML-DSA-65 init transcript v1\0".to_vec();
		bytes.extend_from_slice(&SERVER_ID.to_le_bytes());
		bytes.extend_from_slice(server_ed);
		bytes.extend_from_slice(init.mldsa_public_key);
		bytes.extend_from_slice(server_auth);
		for field in [
			init.identity_key,
			init.pre_key,
			init.one_time_key,
			init.pq_key,
		] {
			append_field(&mut bytes, field);
		}
		hash(&bytes)
	}

	fn response_hash(init_hash: &[u8; 64], response: KexResponse<'_>) -> [u8; 64] {
		let mut bytes = b"beaconcrypt ML-DSA-65 response transcript v1\0".to_vec();
		bytes.extend_from_slice(init_hash);
		for field in [
			response.identity_key,
			response.ephemeral_key,
			response.kem_cipher_text,
			response.app_cipher_text,
		] {
			append_field(&mut bytes, field);
		}
		bytes.extend_from_slice(&response.key_id.to_le_bytes());
		hash(&bytes)
	}

	fn signing_input(server: bool, digest: &[u8; 64]) -> Vec<u8> {
		let mut bytes = vec![b' '; 64];
		bytes.extend_from_slice(if server {
			b"beaconcrypt v1 server registration"
		} else {
			b"beaconcrypt v1 beacon registration"
		});
		bytes.push(0);
		bytes.extend_from_slice(digest);
		bytes
	}

	fn sign_auth(key: &SigningKey<MlDsa65>, server: bool, digest: &[u8; 64]) -> Vec<u8> {
		key.expanded_key()
			.sign_deterministic(
				&signing_input(server, digest),
				b"beaconcrypt registration auth v1",
			)
			.unwrap()
			.encode()
			.to_vec()
	}

	fn verify_auth(key: &[u8], signature: &[u8], server: bool, digest: &[u8; 64]) {
		let encoded = <&EncodedVerifyingKey<MlDsa65>>::try_from(key).unwrap();
		let signature = Signature::<MlDsa65>::try_from(signature).unwrap();
		assert!(VerifyingKey::decode(encoded).verify_with_context(
			&signing_input(server, digest),
			b"beaconcrypt registration auth v1",
			&signature
		));
	}

	struct LegacySession {
		send: [u8; 32],
		receive: [u8; 32],
		send_seq: u64,
		receive_seq: u64,
		local_id: u64,
		remote_id: u64,
		ad: Vec<u8>,
	}

	impl LegacySession {
		fn new(
			secrets: [&[u8]; 5],
			server: bool,
			peer_id: u64,
			server_ed: &[u8],
			beacon_ed: &[u8],
			server_auth: &[u8],
			beacon_auth: &[u8],
		) -> Self {
			let mut root_input = vec![0xff; 32];
			for secret in secrets {
				root_input.extend_from_slice(secret);
			}
			assert_eq!(root_input.len(), 192);
			let root = hkdf(&root_input, PQ_DOMAIN, 32);
			let chains = hkdf(&root, RATCHET_DOMAIN, 64);
			let mut ad = vec![1];
			ad.extend_from_slice(server_ed);
			ad.push(1);
			ad.extend_from_slice(beacon_ed);
			ad.extend_from_slice(PQ_DOMAIN);
			ad.extend_from_slice(RATCHET_DOMAIN);
			ad.extend_from_slice(&hash(server_auth));
			ad.extend_from_slice(&hash(beacon_auth));
			assert_eq!(ad.len(), 281);
			let (send, receive) = if server {
				(&chains[..32], &chains[32..])
			} else {
				(&chains[32..], &chains[..32])
			};
			Self {
				send: send.try_into().unwrap(),
				receive: receive.try_into().unwrap(),
				send_seq: 0,
				receive_seq: 0,
				local_id: if server { SERVER_ID } else { peer_id },
				remote_id: if server { peer_id } else { SERVER_ID },
				ad,
			}
		}

		fn commitment(&self, material: &[u8], tag: &[u8], sequence: u64, sender: u64) -> [u8; 64] {
			let mut input = material[..32].to_vec();
			input.extend_from_slice(&material[64..76]);
			input.extend_from_slice(&self.ad);
			input.extend_from_slice(tag);
			input.extend_from_slice(&sequence.to_le_bytes());
			input.extend_from_slice(&sender.to_le_bytes());
			assert_eq!(input.len(), 357);
			hash(&input)
		}

		fn seal_raw(&mut self, plaintext: &[u8]) -> Vec<u8> {
			use sodium::crypto_aead::chacha20poly1305_ietf as aead;
			let material = hkdf(&self.send, RATCHET_DOMAIN, 76);
			self.send.copy_from_slice(&material[32..64]);
			self.send_seq += 1;
			let key = aead::Key::from_bytes(&material[..32]).unwrap();
			let nonce = aead::Nonce::try_from_slice(&material[64..76]).unwrap();
			let (mut cipher, tag) =
				aead::encrypt_detached(plaintext, Some(&self.ad), &nonce, &key).unwrap();
			let commitment = self.commitment(&material, &tag, self.send_seq, self.local_id);
			cipher.extend_from_slice(&tag);
			cipher.extend_from_slice(&commitment);
			cipher
		}

		fn seal(&mut self, plaintext: &[u8]) -> Vec<u8> {
			let ciphertext = self.seal_raw(plaintext);
			let mut output = vec![0; ciphertext.len() + 64];
			let written = beaconcrypt_parse::encode_frame(
				CryptoFrame {
					seq: self.send_seq,
					key_id: self.local_id,
					cipher_text: &ciphertext,
				},
				&mut output,
			);
			assert_ne!(written, 0);
			output.truncate(written);
			output
		}

		fn open_raw(&mut self, payload: &[u8], seq: u64) -> Vec<u8> {
			use sodium::crypto_aead::chacha20poly1305_ietf as aead;
			assert_eq!(seq, self.receive_seq + 1);
			let material = hkdf(&self.receive, RATCHET_DOMAIN, 76);
			let boundary = payload.len() - 64;
			let tag = &payload[boundary - 16..boundary];
			assert_eq!(
				&payload[boundary..],
				self.commitment(&material, tag, seq, self.remote_id)
			);
			let key = aead::Key::from_bytes(&material[..32]).unwrap();
			let nonce = aead::Nonce::try_from_slice(&material[64..76]).unwrap();
			let plaintext =
				aead::decrypt(&payload[..boundary], Some(&self.ad), &nonce, &key).unwrap();
			self.receive.copy_from_slice(&material[32..64]);
			self.receive_seq = seq;
			plaintext
		}

		fn open(&mut self, bytes: &[u8]) -> Vec<u8> {
			let frame = beaconcrypt_parse::decode_frame(bytes).unwrap();
			assert_eq!(frame.key_id, self.remote_id);
			self.open_raw(frame.cipher_text, frame.seq)
		}
	}

	fn encode_response(response: KexResponse<'_>) -> Vec<u8> {
		let mut output = vec![0; response.app_cipher_text.len() + 8192];
		let written = beaconcrypt_parse::encode_response(response, &mut output);
		assert_ne!(written, 0);
		output.truncate(written);
		output
	}

	#[test]
	fn portable_beacon_registers_and_exchanges_records_with_independent_sodium_server() {
		use sodium::{crypto_kem::mlkem768, crypto_kx, crypto_scalarmult, crypto_sign};
		let server = crypto_sign::KeyPair::from_seed(&SERVER_SEED).unwrap();
		let auth = SigningKey::<MlDsa65>::from_seed((&AUTH_SEED).into());
		let auth_public = auth.verifying_key().encode();
		let mut beacon =
			Beacon::try_new(SERVER_ID, server.public_key.as_bytes(), &auth_public).unwrap();
		let init_bytes = beacon.get_registration_bundle().unwrap();
		let init = beaconcrypt_parse::decode_init(&init_bytes).unwrap();
		let digest = init_hash(init, server.public_key.as_bytes(), &auth_public);
		verify_auth(init.mldsa_public_key, init.signature, false, &digest);
		let beacon_ed = crypto_sign::PublicKey::from_bytes(&init.identity_key[1..]).unwrap();
		let prekey = crypto_sign::verify(init.pre_key, &beacon_ed).unwrap();
		let onetime = crypto_sign::verify(init.one_time_key, &beacon_ed).unwrap();
		let pq = crypto_sign::verify(init.pq_key, &beacon_ed).unwrap();
		assert_eq!(&prekey[..2], &[4, 0x80]);
		assert_eq!(&onetime[..2], &[4, 0x81]);
		assert_eq!(pq[0], 3);
		let ephemeral = crypto_kx::KeyPair::from_seed(&[0x61; 32]).unwrap();
		let (kem_cipher, kem_shared) = mlkem768::encapsulate_deterministic(
			&mlkem768::PublicKey::from_bytes(&pq[1..]).unwrap(),
			&mlkem768::EncapsulationSeed::from_bytes(&[0x62; 32]).unwrap(),
		)
		.unwrap();
		let identity_secret = crypto_sign::ed25519_sk_to_curve25519(&server.secret_key).unwrap();
		let beacon_public = crypto_sign::ed25519_pk_to_curve25519(&beacon_ed).unwrap();
		let dh1 = crypto_scalarmult::scalarmult(&identity_secret, &prekey[2..]).unwrap();
		let dh2 =
			crypto_scalarmult::scalarmult(ephemeral.secret_key.as_bytes(), &beacon_public).unwrap();
		let dh3 =
			crypto_scalarmult::scalarmult(ephemeral.secret_key.as_bytes(), &prekey[2..]).unwrap();
		let dh4 =
			crypto_scalarmult::scalarmult(ephemeral.secret_key.as_bytes(), &onetime[2..]).unwrap();
		let assigned = 41u64;
		let mut legacy = LegacySession::new(
			[&dh1, &dh2, &dh3, &dh4, kem_shared.as_bytes()],
			true,
			assigned,
			server.public_key.as_bytes(),
			beacon_ed.as_bytes(),
			&auth_public,
			init.mldsa_public_key,
		);
		let mut plaintext = assigned.to_le_bytes().to_vec();
		plaintext.extend_from_slice(b"legacy registration");
		let encrypted = legacy.seal_raw(&plaintext);
		let response = KexResponse {
			identity_key: server.public_key.as_bytes(),
			ephemeral_key: ephemeral.public_key.as_bytes(),
			kem_cipher_text: kem_cipher.as_bytes(),
			app_cipher_text: &encrypted,
			key_id: assigned,
			signature: &[],
		};
		let signature = sign_auth(&auth, true, &response_hash(&digest, response));
		let response_bytes = encode_response(KexResponse {
			signature: &signature,
			..response
		});
		assert_eq!(
			beacon.finish_registration(&response_bytes).unwrap(),
			b"legacy registration"
		);
		let sent = beacon.encrypt_message(b"portable beacon record").unwrap();
		assert_eq!(legacy.open(&sent.ciphertext), b"portable beacon record");
		let received = legacy.seal(b"legacy server record");
		let mut corrupted = received.clone();
		*corrupted.last_mut().unwrap() ^= 1;
		let before = beacon.ratchet_status().unwrap();
		assert!(beacon.decrypt_message(&corrupted).is_none());
		assert_eq!(beacon.ratchet_status().unwrap(), before);
		assert_eq!(
			beacon.decrypt_message(&received).unwrap().plaintext,
			b"legacy server record"
		);
		assert!(beacon.decrypt_message(&received).is_none());
	}

	#[test]
	fn portable_server_registers_and_exchanges_records_with_independent_sodium_beacon() {
		use sodium::{crypto_kem::mlkem768, crypto_kx, crypto_scalarmult, crypto_sign};
		let mut server = Server::try_new(SERVER_ID, Some(&SERVER_SEED), Some(&AUTH_SEED)).unwrap();
		let beacon = crypto_sign::KeyPair::from_seed(&[0x71; 32]).unwrap();
		let auth = SigningKey::<MlDsa65>::from_seed((&[0x72; 32]).into());
		let auth_public = auth.verifying_key().encode();
		let prekey = crypto_kx::KeyPair::from_seed(&[0x73; 32]).unwrap();
		let onetime = crypto_kx::KeyPair::from_seed(&[0x74; 32]).unwrap();
		let pq = mlkem768::KeyPair::from_seed(&[0x75; 64]).unwrap();
		let mut identity = vec![1];
		identity.extend_from_slice(beacon.public_key.as_bytes());
		let mut prekey_bytes = vec![4, 0x80];
		prekey_bytes.extend_from_slice(prekey.public_key.as_bytes());
		let mut onetime_bytes = vec![4, 0x81];
		onetime_bytes.extend_from_slice(onetime.public_key.as_bytes());
		let mut pq_bytes = vec![3];
		pq_bytes.extend_from_slice(pq.public_key.as_bytes());
		let prekey_signed = crypto_sign::sign(&prekey_bytes, &beacon.secret_key).unwrap();
		let onetime_signed = crypto_sign::sign(&onetime_bytes, &beacon.secret_key).unwrap();
		let pq_signed = crypto_sign::sign(&pq_bytes, &beacon.secret_key).unwrap();
		let init = InitKex {
			identity_key: &identity,
			pre_key: &prekey_signed,
			one_time_key: &onetime_signed,
			pq_key: &pq_signed,
			mldsa_public_key: &auth_public,
			signature: &[],
		};
		let digest = init_hash(
			init,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let signature = sign_auth(&auth, false, &digest);
		let mut init_bytes = vec![0; 8192];
		let written = beaconcrypt_parse::encode_init(
			InitKex {
				signature: &signature,
				..init
			},
			&mut init_bytes,
		);
		assert_ne!(written, 0);
		init_bytes.truncate(written);
		let pending = server.get_shared_secret(&init_bytes).unwrap();
		assert!(server.get_shared_secret(&init_bytes).is_none());
		let response_bytes = server
			.build_registration_response(pending, Some(b"portable registration"))
			.unwrap();
		let response = beaconcrypt_parse::decode_response(&response_bytes.serialized).unwrap();
		verify_auth(
			&server.mldsa_public_key(),
			response.signature,
			true,
			&response_hash(&digest, response),
		);
		let server_ed = crypto_sign::PublicKey::from_bytes(response.identity_key).unwrap();
		let server_public = crypto_sign::ed25519_pk_to_curve25519(&server_ed).unwrap();
		let identity_secret = crypto_sign::ed25519_sk_to_curve25519(&beacon.secret_key).unwrap();
		let dh1 =
			crypto_scalarmult::scalarmult(prekey.secret_key.as_bytes(), &server_public).unwrap();
		let dh2 = crypto_scalarmult::scalarmult(&identity_secret, response.ephemeral_key).unwrap();
		let dh3 =
			crypto_scalarmult::scalarmult(prekey.secret_key.as_bytes(), response.ephemeral_key)
				.unwrap();
		let dh4 =
			crypto_scalarmult::scalarmult(onetime.secret_key.as_bytes(), response.ephemeral_key)
				.unwrap();
		let kem_shared = mlkem768::decapsulate(
			&mlkem768::Ciphertext::from_bytes(response.kem_cipher_text).unwrap(),
			&pq.secret_key,
		)
		.unwrap();
		let mut legacy = LegacySession::new(
			[&dh1, &dh2, &dh3, &dh4, kem_shared.as_bytes()],
			false,
			response.key_id,
			server_ed.as_bytes(),
			beacon.public_key.as_bytes(),
			&server.mldsa_public_key(),
			&auth_public,
		);
		let decrypted = legacy.open_raw(response.app_cipher_text, 1);
		assert_eq!(&decrypted[..8], &response.key_id.to_le_bytes());
		assert_eq!(&decrypted[8..], b"portable registration");
		let sent = legacy.seal(b"legacy beacon record");
		let mut corrupted = sent.clone();
		*corrupted.last_mut().unwrap() ^= 1;
		let before = server.ratchet_status(response.key_id).unwrap();
		assert!(server.decrypt_message(&corrupted).is_none());
		assert_eq!(server.ratchet_status(response.key_id).unwrap(), before);
		assert_eq!(
			server.decrypt_message(&sent).unwrap().plaintext,
			b"legacy beacon record"
		);
		assert!(server.decrypt_message(&sent).is_none());
		let reply = server
			.encrypt_message(b"portable server record", response.key_id)
			.unwrap();
		assert_eq!(legacy.open(&reply.ciphertext), b"portable server record");
	}
}
