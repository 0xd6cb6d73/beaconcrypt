// SPDX-License-Identifier: 0BSD

use crate::{BeaconCryptPqxdh, CryptoProvider, ProviderBeacon, ProviderServer};
use std::mem;
use std::slice;

#[repr(C)]
pub struct GoBuffer {
	pub ptr: *mut u8,
	pub len: usize,
	pub cap: usize,
}

#[repr(C)]
pub struct GoRegistrationResponse {
	pub response: GoBuffer,
	pub beacon_pk: GoBuffer,
	pub key_id: u64,
}

fn empty_buffer() -> GoBuffer {
	GoBuffer {
		ptr: std::ptr::null_mut(),
		len: 0,
		cap: 0,
	}
}

fn into_buffer(mut data: Vec<u8>) -> GoBuffer {
	let buffer = GoBuffer {
		ptr: data.as_mut_ptr(),
		len: data.len(),
		cap: data.capacity(),
	};
	mem::forget(data);
	buffer
}

unsafe fn input<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
	if ptr.is_null() || len == 0 {
		None
	} else {
		Some(unsafe { slice::from_raw_parts(ptr, len) })
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_free_buffer(buffer: GoBuffer) {
	if !buffer.ptr.is_null() {
		unsafe { Vec::from_raw_parts(buffer.ptr, buffer.len, buffer.cap) };
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_server_new(server_kid: u64) -> *mut BeaconCryptPqxdh {
	Box::into_raw(Box::new(BeaconCryptPqxdh::new(
		false, server_kid, None, None,
	)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_server_new_from_seed(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
) -> *mut BeaconCryptPqxdh {
	let seed = unsafe { input(seed_ptr, seed_len) };
	Box::into_raw(Box::new(BeaconCryptPqxdh::new(
		false, server_kid, None, seed,
	)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_beacon_new(
	server_kid: u64,
	server_pk_ptr: *const u8,
	server_pk_len: usize,
) -> *mut BeaconCryptPqxdh {
	let server_pk = unsafe { input(server_pk_ptr, server_pk_len) };
	Box::into_raw(Box::new(BeaconCryptPqxdh::new(
		true, server_kid, server_pk, None,
	)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_free(handle: *mut BeaconCryptPqxdh) {
	if !handle.is_null() {
		unsafe { drop(Box::from_raw(handle)) };
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_identity_pk(handle: *const BeaconCryptPqxdh) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	into_buffer(provider.identity_pk().as_ref().to_vec())
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_generate_registration(handle: *mut BeaconCryptPqxdh) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &mut *handle };
	provider
		.get_registration_bundle()
		.map(into_buffer)
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_register_beacon(
	handle: *mut BeaconCryptPqxdh,
	reg_ptr: *const u8,
	reg_len: usize,
	msg_ptr: *const u8,
	msg_len: usize,
) -> GoRegistrationResponse {
	if handle.is_null() {
		return GoRegistrationResponse {
			response: empty_buffer(),
			beacon_pk: empty_buffer(),
			key_id: 0,
		};
	}
	let provider = unsafe { &mut *handle };
	let Some(registration) = (unsafe { input(reg_ptr, reg_len) }) else {
		return GoRegistrationResponse {
			response: empty_buffer(),
			beacon_pk: empty_buffer(),
			key_id: 0,
		};
	};
	let message = unsafe { input(msg_ptr, msg_len) };
	let Some(secret) = provider.get_shared_secret(registration) else {
		return GoRegistrationResponse {
			response: empty_buffer(),
			beacon_pk: empty_buffer(),
			key_id: 0,
		};
	};
	let beacon_pk = secret.public_key.as_ref().to_vec();
	let Some(response) = provider.build_registration_response(secret, message) else {
		return GoRegistrationResponse {
			response: empty_buffer(),
			beacon_pk: empty_buffer(),
			key_id: 0,
		};
	};
	GoRegistrationResponse {
		response: into_buffer(response.serialized),
		beacon_pk: into_buffer(beacon_pk),
		key_id: response.kid,
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_process_initial_message(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.finish_registration(data)
		.map(into_buffer)
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_encrypt_to_beacon(
	handle: *mut BeaconCryptPqxdh,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	encrypt(handle, ptr, len, key_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_encrypt_to_beacon_signed(
	handle: *mut BeaconCryptPqxdh,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	match provider.encrypt_message(data, key_id) {
		Some(ciphertext) => provider
			.sign_message(ciphertext.as_slice())
			.map(into_buffer)
			.unwrap_or_else(empty_buffer),
		None => empty_buffer(),
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_decrypt_beacon_message(
	handle: *mut BeaconCryptPqxdh,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	decrypt(handle, ptr, len, key_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_decrypt_beacon_message_signed(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	match provider.verify_signature(data) {
		Some(verified) => provider
			.decrypt_message(&verified.data, verified.key_id)
			.map(into_buffer)
			.unwrap_or_else(empty_buffer),
		None => empty_buffer(),
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_encrypt_to_server(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	encrypt(handle, ptr, len, provider.server_kid())
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_encrypt_to_server_signed(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	let srv_kid = provider.server_kid();
	match provider.encrypt_message(data, srv_kid) {
		Some(ciphertext) => provider
			.sign_message(ciphertext.as_slice())
			.map(into_buffer)
			.unwrap_or_else(empty_buffer),
		None => empty_buffer(),
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_decrypt_server_message(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	decrypt(handle, ptr, len, provider.server_kid())
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_go_decrypt_server_message_signed(
	handle: *mut BeaconCryptPqxdh,
	ptr: *const u8,
	len: usize,
) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	match provider.verify_signature(data) {
		Some(verified) => provider
			.decrypt_message(&verified.data, provider.server_kid())
			.map(into_buffer)
			.unwrap_or_else(empty_buffer),
		None => empty_buffer(),
	}
}

fn encrypt(handle: *mut BeaconCryptPqxdh, ptr: *const u8, len: usize, key_id: u64) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.encrypt_message(data, key_id)
		.map(into_buffer)
		.unwrap_or_else(empty_buffer)
}

fn decrypt(handle: *mut BeaconCryptPqxdh, ptr: *const u8, len: usize, key_id: u64) -> GoBuffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.decrypt_message(data, key_id)
		.map(into_buffer)
		.unwrap_or_else(empty_buffer)
}
