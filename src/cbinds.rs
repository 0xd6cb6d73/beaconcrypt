// SPDX-License-Identifier: 0BSD

use crate::server::{RecvState, SendState};
use crate::{Beacon, ProviderBeacon, ProviderServer, Server};
use std::mem;
use std::slice;

#[repr(C)]
pub struct Buffer {
	pub ptr: *mut u8,
	pub len: usize,
	pub cap: usize,
}

#[repr(C)]
pub struct RegistrationResponse {
	pub response: Buffer,
	pub key_id: u64,
}

#[repr(C)]
pub struct EncryptState {
	pub data: Buffer,
	/// Complete RatchetManager serialized as JSON.
	pub state: Buffer,
	pub key_id: u64,
	pub seq: u64,
}

fn empty_buffer() -> Buffer {
	Buffer {
		ptr: std::ptr::null_mut(),
		len: 0,
		cap: 0,
	}
}

fn into_buffer(mut data: Vec<u8>) -> Buffer {
	let buffer = Buffer {
		ptr: data.as_mut_ptr(),
		len: data.len(),
		cap: data.capacity(),
	};
	mem::forget(data);
	buffer
}

fn empty_encrypt_state() -> EncryptState {
	EncryptState {
		data: empty_buffer(),
		state: empty_buffer(),
		key_id: 0,
		seq: 0,
	}
}

fn into_send_state(state: SendState) -> Option<EncryptState> {
	let serialized_state = serde_json::to_vec(&state.state).ok()?;
	Some(EncryptState {
		data: into_buffer(state.data),
		state: into_buffer(serialized_state),
		key_id: state.kid,
		seq: state.seq,
	})
}

fn into_recv_state(state: RecvState) -> Option<EncryptState> {
	let serialized_state = serde_json::to_vec(&state.state).ok()?;
	Some(EncryptState {
		data: into_buffer(state.data),
		state: into_buffer(serialized_state),
		key_id: state.kid,
		seq: state.seq,
	})
}

unsafe fn input<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
	if ptr.is_null() || len == 0 {
		None
	} else {
		Some(unsafe { slice::from_raw_parts(ptr, len) })
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_free_buffer(buffer: Buffer) {
	if !buffer.ptr.is_null() {
		unsafe { Vec::from_raw_parts(buffer.ptr, buffer.len, buffer.cap) };
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new(server_kid: u64) -> *mut Server {
	Box::into_raw(Box::new(Server::new(server_kid, None)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new_from_seed(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
) -> *mut Server {
	let seed = unsafe { input(seed_ptr, seed_len) };
	Box::into_raw(Box::new(Server::new(server_kid, seed)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new_from_state(
	state_ptr: *const u8,
	state_len: usize,
) -> *mut Server {
	let Some(state) = (unsafe { input(state_ptr, state_len) }) else {
		return std::ptr::null_mut();
	};
	let Ok(state) = std::str::from_utf8(state) else {
		return std::ptr::null_mut();
	};
	let Some(provider) = <Server as ProviderServer>::try_from_state(state) else {
		return std::ptr::null_mut();
	};

	Box::into_raw(Box::new(provider))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_new(
	server_kid: u64,
	server_pk_ptr: *const u8,
	server_pk_len: usize,
) -> *mut Beacon {
	let Some(server_pk) = (unsafe { input(server_pk_ptr, server_pk_len) }) else {
		return std::ptr::null_mut();
	};
	Box::into_raw(Box::new(Beacon::new(server_kid, server_pk)))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_free(handle: *mut Server) {
	if !handle.is_null() {
		unsafe { drop(Box::from_raw(handle)) };
	}
}
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_free(handle: *mut Beacon) {
	if !handle.is_null() {
		unsafe { drop(Box::from_raw(handle)) };
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_identity_pk(handle: *const Server) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	into_buffer(provider.identity_pk().as_ref().to_vec())
}
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_identity_pk(handle: *const Beacon) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	into_buffer(provider.identity_pk().as_ref().to_vec())
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_generate_registration(handle: *mut Beacon) -> Buffer {
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
pub extern "C" fn beaconcrypt_register_beacon(
	handle: *mut Server,
	reg_ptr: *const u8,
	reg_len: usize,
	msg_ptr: *const u8,
	msg_len: usize,
) -> RegistrationResponse {
	if handle.is_null() {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	}
	let provider = unsafe { &mut *handle };
	let Some(registration) = (unsafe { input(reg_ptr, reg_len) }) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let message = unsafe { input(msg_ptr, msg_len) };
	let Some(secret) = provider.get_shared_secret(registration) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Some(response) = provider.build_registration_response(secret, message) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	RegistrationResponse {
		response: into_buffer(response.serialized),
		key_id: response.kid,
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_process_initial_message(
	handle: *mut Beacon,
	ptr: *const u8,
	len: usize,
) -> Buffer {
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
pub extern "C" fn beaconcrypt_encrypt_to_beacon(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	encrypt(handle, ptr, len, key_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_decrypt_beacon_message(
	handle: *mut Server,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	decrypt(handle, ptr, len)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_and_update(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> EncryptState {
	if handle.is_null() {
		return empty_encrypt_state();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_encrypt_state();
	};
	let provider = unsafe { &mut *handle };
	provider
		.encrypt_and_update(data, key_id)
		.and_then(into_send_state)
		.unwrap_or_else(empty_encrypt_state)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_and_update_json(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.encrypt_and_update_json(data, key_id)
		.map(|state| into_buffer(state.into_bytes()))
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_decrypt_and_update(
	handle: *mut Server,
	ptr: *const u8,
	len: usize,
) -> EncryptState {
	if handle.is_null() {
		return empty_encrypt_state();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_encrypt_state();
	};
	let provider = unsafe { &mut *handle };
	provider
		.decrypt_and_update(data)
		.and_then(into_recv_state)
		.unwrap_or_else(empty_encrypt_state)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_decrypt_and_update_json(
	handle: *mut Server,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.decrypt_and_update_json(data)
		.map(|state| into_buffer(state.into_bytes()))
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_export_state(handle: *const Server) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	provider
		.export_state()
		.map(|state| into_buffer(state.into_bytes()))
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_to_server(
	handle: *mut Beacon,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.encrypt_message(data)
		.map(|e| into_buffer(e.ciphertext))
		.unwrap_or_else(empty_buffer)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_decrypt_server_message(
	handle: *mut Beacon,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.decrypt_message(data)
		.map(|d| into_buffer(d.plaintext))
		.unwrap_or_else(empty_buffer)
}

fn encrypt(handle: *mut Server, ptr: *const u8, len: usize, key_id: u64) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.encrypt_message(data, key_id)
		.map(|encrypted| into_buffer(encrypted.ciphertext))
		.unwrap_or_else(empty_buffer)
}

fn decrypt(handle: *mut Server, ptr: *const u8, len: usize) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(data) = (unsafe { input(ptr, len) }) else {
		return empty_buffer();
	};
	let provider = unsafe { &mut *handle };
	provider
		.decrypt_message(data)
		.map(|decrypted| into_buffer(decrypted.plaintext))
		.unwrap_or_else(empty_buffer)
}
