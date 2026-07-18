// SPDX-License-Identifier: 0BSD

#[cfg(feature = "pqxdh")]
use libsodium_rs::{crypto_kem, crypto_kx, crypto_sign};

use crate::shared::{CryptoProvider, KexDerivedSecret, STATE};
use std::{mem, slice::from_raw_parts};

#[cfg(feature = "pqxdh")]
type KemCiphertext = crypto_kem::mlkem768::Ciphertext;
#[cfg(feature = "pqxdh")]
type SignVerificationKey = crypto_sign::PublicKey;
#[cfg(feature = "pqxdh")]
type EphemeralKexPubKey = crypto_kx::PublicKey;
pub struct RegResponse {
	pub serialized: Vec<u8>,
	pub kid: u64,
}

#[derive(Clone)]
pub struct RegistrationOutput {
	pub kem_ciphertext: KemCiphertext,
	pub derived_secret: KexDerivedSecret,
	pub ephemeral: EphemeralKexPubKey,
	pub public_key: SignVerificationKey,
}

pub trait ProviderServer {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput>;

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse>;
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
///
/// * `bytes` - A serialized `phase1_capnp::init_kex` from the network
/// * `bytes_len` - The size of the `bytes` buffer
/// * `data` - The contents of the initial message to send back to the agent, as bytes
/// * `data_len` - The size of the `data` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
/// ## Returns
///
/// * i32 - Values other than 0 indicate failure
///
#[unsafe(no_mangle)]
pub unsafe extern "C" fn register_beacon(
	bytes: *const u8,
	bytes_len: usize,
	data: *const u8,
	data_len: usize,
	mut _response: *mut *mut u8,
	response_len: *mut usize,
	response_capa: *mut usize,
	mut _pk: *mut *mut u8,
	pk_len: *mut usize,
	pk_capa: *mut usize,
	key_id: *mut u64,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_slice = unsafe { from_raw_parts(bytes, bytes_len) };
	match state.get_shared_secret(data_slice) {
		Some(secrets) => {
			let to_encrypt = if data.is_null() || data_len == 0 {
				None
			} else {
				Some(unsafe { from_raw_parts(data, data_len) })
			};
			match state.build_registration_response(secrets.clone(), to_encrypt) {
				Some(mut response) => {
					let beacon_key_id = response.kid;
					unsafe {
						*_response = response.serialized.as_mut_ptr();
						*response_len = response.serialized.len();
						*response_capa = response.serialized.capacity();
						mem::forget(response);
						let mut pk = secrets.public_key.as_ref().to_vec();
						*_pk = pk.as_mut_ptr();
						*pk_len = pk.len();
						*pk_capa = pk.capacity();
						mem::forget(pk);
						*key_id = beacon_key_id;
					};
					0
				}
				None => -1i32,
			}
		}
		None => -1i32,
	}
}

/// This function takes a raw `cryptoframe_capnp::crypto_frame`. It needs to know the ID of the beacon that encrypted the message
/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `key_id` - The ID of the beacon to decrypt for
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_beacon_message(
	key_id: u64,
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_slice = unsafe { from_raw_parts(bytes, bytes_len) };

	match state.decrypt_message(data_slice, key_id) {
		Some(mut plaintext) => {
			unsafe {
				*_out = plaintext.as_mut_ptr();
				*out_len = plaintext.len();
				*out_capa = plaintext.capacity();
				mem::forget(plaintext);
			};
			0
		}
		None => -1,
	}
}

/// This function takes a raw `protogram_capnp::proto_gram` and returns a plaintext if the signature is valid. It does not need to know the ID of the beacon that created the message
/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `protogram_capnp::proto_gram`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_beacon_message_signed(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_slice = unsafe { from_raw_parts(bytes, bytes_len) };

	match state.verify_signature(data_slice) {
		Some(verified) => match state.decrypt_message(&verified.data, verified.key_id) {
			Some(mut plaintext) => {
				unsafe {
					*_out = plaintext.as_mut_ptr();
					*out_len = plaintext.len();
					*out_capa = plaintext.capacity();
					mem::forget(plaintext);
				};
				0
			}
			None => -1,
		},
		None => -1,
	}
}

/// Encrypts a plaintext to the beacon identified by `key_id`. The output is intended to be sent directly over the network
/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `key_id` - The ID of the beacon to encypt for
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_beacon(
	key_id: u64,
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_slice = unsafe { from_raw_parts(bytes, bytes_len) };
	match state.encrypt_message(data_slice, key_id) {
		Some(mut ciphertext) => {
			unsafe {
				*_out = ciphertext.as_mut_ptr();
				*out_len = ciphertext.len();
				*out_capa = ciphertext.capacity();
				mem::forget(ciphertext);
			};
			0
		}
		None => -1,
	}
}

/// Encrypts a plaintext to the beacon identified by `key_id`. The output is intended to be sent directly over the network
/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `key_id` - The sequence number for the beacon to encypt to
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_beacon_signed(
	key_id: u64,
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut state = STATE.lock().unwrap();
	let data_slice = unsafe { from_raw_parts(bytes, bytes_len) };
	match state.encrypt_message(data_slice, key_id) {
		Some(ciphertext) => match state.sign_message(ciphertext.as_slice()) {
			Some(mut signed) => {
				unsafe {
					*_out = signed.as_mut_ptr();
					*out_len = signed.len();
					*out_capa = signed.capacity();
					mem::forget(signed);
				};
				0
			}
			None => -1,
		},
		None => -1,
	}
}
