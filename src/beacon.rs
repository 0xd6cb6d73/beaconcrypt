// SPDX-License-Identifier: 0BSD

use crate::shared::{CryptoProvider, INITIALIZED, Provider, STATE};
use libsodium_rs::crypto_sign;
use std::{mem, ptr::slice_from_raw_parts, sync::atomic::Ordering, vec};

pub trait ProviderBeacon {
	fn get_registration_bundle(&self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn process_initial_message(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut net_vec = vec![0u8; bytes_len];
	let net_slice = slice_from_raw_parts(bytes, bytes_len);
	net_vec.copy_from_slice(unsafe { net_slice.as_ref().unwrap() });
	let mut state = STATE.lock().unwrap();
	match state.finish_registration(net_vec.as_slice()) {
		Some(mut plaintext) => {
			unsafe {
				*_out = plaintext.as_mut_ptr();
				*out_len = plaintext.len();
				*out_capa = plaintext.capacity();
				mem::forget(plaintext);
			};
			0i32
		}
		None => -1i32,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn process_initial_message_signed(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let mut net_vec = vec![0u8; bytes_len];
	let net_slice = slice_from_raw_parts(bytes, bytes_len);
	net_vec.copy_from_slice(unsafe { net_slice.as_ref().unwrap() });

	let mut state = STATE.lock().unwrap();
	match state.verify_signature(net_vec.as_slice()) {
		Some(verified) => match state.finish_registration(&verified) {
			Some(mut plaintext) => {
				unsafe {
					*_out = plaintext.as_mut_ptr();
					*out_len = plaintext.len();
					*out_capa = plaintext.capacity();
					mem::forget(plaintext);
				};
				0i32
			}
			None => -1i32,
		},
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_server_message(
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
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };

	let srv_seq = state.server_kid();
	match state.decrypt_message(&data_vec, srv_seq, true) {
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

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn decrypt_server_message_signed(
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
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };

	match state.verify_signature(data_vec.as_slice()) {
		Some(verified) => {
			let srv_seq = state.server_kid();
			match state.decrypt_message(&verified, srv_seq, true) {
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
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_server(
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
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let srv_seq = state.server_kid();
	match state.encrypt_message(data_vec.as_slice(), false, srv_seq) {
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

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn encrypt_to_server_signed(
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
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let srv_seq = state.server_kid();
	match state.encrypt_message(data_vec.as_slice(), false, srv_seq) {
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

/// # Safety
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Whatever you want to be encrypted to the server
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn generate_registration(
	mut _out: *mut *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	let state = STATE.lock().unwrap();
	match state.get_registration_bundle() {
		Some(mut data) => {
			unsafe {
				*_out = data.as_mut_ptr();
				*out_len = data.len();
				*out_capa = data.capacity();
				mem::forget(data);
			};
			0
		}
		None => -1,
	}
}

/// This function is safe to call multiple times. It is used to initialize beacons with a hardcoded server public key. You should always use this on beacons
/// ## Arguments
///
/// * `is_beacon` - Whether the current instance is a beacon
/// * `server_seq` - The ID of the server's identity key for the campaign
#[unsafe(no_mangle)]
pub extern "C" fn init_for_server(
	is_beacon: bool,
	server_seq: u64,
	server_pk: *const u8,
	server_pk_len: u64,
) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		let pk_slice = slice_from_raw_parts(server_pk, server_pk_len.try_into().unwrap());
		let mut pk_vec = vec![0u8; crypto_sign::PUBLICKEYBYTES];
		pk_vec.copy_from_slice(unsafe { pk_slice.as_ref().unwrap() });
		*state = Provider::new(is_beacon, server_seq, Some(&pk_vec), None);
	}
}
