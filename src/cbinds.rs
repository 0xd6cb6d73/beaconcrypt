// SPDX-License-Identifier: 0BSD

use crate::persistence::BindingServer;
use crate::server::{RecvState, SendState};
use crate::{Beacon, ProviderBeacon};
use std::mem;
use std::slice;

/// Opaque server handle owned by the C caller.
pub struct Server(BindingServer);

/// Heap-allocated byte buffer returned by the C API.
///
/// A non-empty buffer must be released exactly once with `beaconcrypt_free_buffer`. An empty buffer has a null `ptr` and indicates either empty output or failure, depending on the called function.
#[repr(C)]
pub struct Buffer {
	/// Pointer to the first byte, or null when the buffer is empty.
	pub ptr: *mut u8,
	/// Number of initialized bytes available through `ptr`.
	pub len: usize,
	/// Allocation capacity reserved for `beaconcrypt_free_buffer`; callers must not modify it.
	pub cap: usize,
}

/// Result returned after a successful server-side beacon registration.
#[repr(C)]
pub struct RegistrationResponse {
	/// Serialized registration response for the beacon.
	pub response: Buffer,
	/// Key identifier assigned to the registered beacon.
	pub key_id: u64,
}

/// Message output accompanied by observational ratchet metadata.
#[repr(C)]
pub struct EncryptState {
	/// Ciphertext for encryption calls or plaintext for decryption calls.
	pub data: Buffer,
	/// Inert plaintext ratchet JSON for observation only.
	/// It is secret-bearing, unauthenticated, and not restorable.
	pub state: Buffer,
	/// Key identifier used by the ratchet operation.
	pub key_id: u64,
	/// Ratchet sequence number used by the operation.
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
	let serialized_state = state.state.as_str().as_bytes().to_vec();
	Some(EncryptState {
		data: into_buffer(state.data),
		state: into_buffer(serialized_state),
		key_id: state.kid,
		seq: state.seq,
	})
}

fn into_recv_state(state: RecvState) -> Option<EncryptState> {
	let serialized_state = state.state.as_str().as_bytes().to_vec();
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

/// Release a byte buffer returned by this API.
///
/// Passing an empty buffer is allowed. The buffer and its pointer must not be used after this call.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_free_buffer(buffer: Buffer) {
	if !buffer.ptr.is_null() {
		unsafe { Vec::from_raw_parts(buffer.ptr, buffer.len, buffer.cap) };
	}
}

/// Create a server with a randomly generated identity key.
///
/// Returns an owned handle, or null on failure. Release a non-null handle with `beaconcrypt_server_free`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new(server_kid: u64) -> *mut Server {
	BindingServer::create_binding(server_kid, None)
		.map(|server| Box::into_raw(Box::new(Server(server))))
		.unwrap_or(std::ptr::null_mut())
}

/// Create a server with an optional deterministic identity seed.
///
/// A null pointer or zero length selects a random identity key. A non-empty seed must contain exactly `beaconcrypt_ED25519_SEED_SIZE` readable bytes.
///
/// Returns an owned handle, or null when creation fails. Release a non-null handle with `beaconcrypt_server_free`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new_from_seed(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
) -> *mut Server {
	let seed = unsafe { input(seed_ptr, seed_len) };
	BindingServer::create_binding(server_kid, seed)
		.map(|server| Box::into_raw(Box::new(Server(server))))
		.unwrap_or(std::ptr::null_mut())
}

/// Restore a server from trusted checkpoint bytes.
///
/// The caller must reject stale or untrusted checkpoints. These bytes are plaintext and are not cryptographically authenticated.
///
/// Restoration advances the generation, so export and save the returned handle immediately before using it. Returns an owned handle, or null for invalid state.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new_from_state(
	state_ptr: *const u8,
	state_len: usize,
) -> *mut Server {
	let Some(state) = (unsafe { input(state_ptr, state_len) }) else {
		return std::ptr::null_mut();
	};
	BindingServer::restore_binding(state.to_vec())
		.map(|server| Box::into_raw(Box::new(Server(server))))
		.unwrap_or(std::ptr::null_mut())
}

/// Export the current plaintext checkpoint.
///
/// Save it immediately after every accepted receive or other state-changing call and before using that call's output.
/// A normal rejected receive leaves the checkpoint unchanged.
/// Returns an empty buffer on failure.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_export_state(handle: *const Server) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	provider
		.0
		.export_binding_state()
		.map(into_buffer)
		.unwrap_or_else(|_| empty_buffer())
}

/// Create a beacon bound to a server identity public key.
///
/// `server_pk_ptr` must point to an Ed25519 public key of the length implied by the API constants.
///
/// Returns an owned handle, or null when the public-key input is absent. Release a non-null handle with `beaconcrypt_beacon_free`.
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

/// Release a server handle created by this API.
///
/// Passing null is allowed. The handle must not be used after this call.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_free(handle: *mut Server) {
	if !handle.is_null() {
		unsafe { drop(Box::from_raw(handle)) };
	}
}
/// Release a beacon handle created by this API.
///
/// Passing null is allowed. The handle must not be used after this call.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_free(handle: *mut Beacon) {
	if !handle.is_null() {
		unsafe { drop(Box::from_raw(handle)) };
	}
}

/// Copy the server identity public key into a caller-owned buffer.
///
/// Returns an empty buffer when `handle` is null.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_identity_pk(handle: *const Server) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	into_buffer(provider.0.identity_pk().as_ref().to_vec())
}
/// Copy the beacon identity public key into a caller-owned buffer.
///
/// Returns an empty buffer when `handle` is null.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_identity_pk(handle: *const Beacon) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let provider = unsafe { &*handle };
	into_buffer(provider.identity_pk().as_ref().to_vec())
}

/// Generate the beacon's serialized registration bundle.
///
/// Returns an empty buffer when the handle is invalid or the beacon cannot generate a bundle in its current state.
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

/// Register a beacon and build its initial server response.
///
/// `msg_ptr` may be null when `msg_len` is zero to omit the initial message. On failure, returns an empty response with key identifier zero.
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
	let provider = &mut unsafe { &mut *handle }.0;
	let Some(registration) = (unsafe { input(reg_ptr, reg_len) }) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let message = unsafe { input(msg_ptr, msg_len) };
	let Ok(Some(secret)) = provider.get_shared_secret(registration) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Ok(Some(response)) = provider.build_registration_response(secret, message) else {
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

/// Finish beacon registration and return the optional initial plaintext message.
///
/// Returns an empty buffer when the input is invalid, registration fails, or no initial message was supplied.
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

/// Encrypt a message from the server to the beacon identified by `key_id`.
///
/// Returns an empty buffer when the handle or input is invalid, the key is unknown, or encryption fails.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_to_beacon(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	encrypt(handle, ptr, len, key_id)
}

/// Decrypt a beacon-to-server message.
///
/// Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_decrypt_beacon_message(
	handle: *mut Server,
	ptr: *const u8,
	len: usize,
) -> Buffer {
	decrypt(handle, ptr, len)
}

/// Encrypt a server-to-beacon message and return observational ratchet metadata.
///
/// Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.encrypt_and_update(data, key_id)
		.ok()
		.flatten()
		.and_then(into_send_state)
		.unwrap_or_else(empty_encrypt_state)
}

/// Encrypt a server-to-beacon message and return the result and ratchet metadata as JSON.
///
/// Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.encrypt_and_update_json(data, key_id)
		.ok()
		.flatten()
		.map(|state| into_buffer(state.into_bytes()))
		.unwrap_or_else(empty_buffer)
}

/// Decrypt a beacon-to-server message and return observational ratchet metadata.
///
/// Returns an empty `beaconcrypt_EncryptState` when the operation fails. Persist the server checkpoint before using the returned output.
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.decrypt_and_update(data)
		.ok()
		.flatten()
		.and_then(into_recv_state)
		.unwrap_or_else(empty_encrypt_state)
}

/// Decrypt a beacon-to-server message and return the result and ratchet metadata as JSON.
///
/// Returns an empty buffer when the operation fails. Persist the server checkpoint before using the returned output.
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.decrypt_and_update_json(data)
		.ok()
		.flatten()
		.map(|state| into_buffer(state.into_bytes()))
		.unwrap_or_else(empty_buffer)
}

/// Encrypt a message from the beacon to its server.
///
/// Returns an empty buffer when the handle or input is invalid or encryption fails.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_to_server(
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
		.encrypt_message(data)
		.map(|e| into_buffer(e.ciphertext))
		.unwrap_or_else(empty_buffer)
}

/// Decrypt a server-to-beacon message.
///
/// Returns an empty buffer when the handle or input is invalid, authentication fails, or the ratchet rejects the message.
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.encrypt_message(data, key_id)
		.ok()
		.flatten()
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
	let provider = &mut unsafe { &mut *handle }.0;
	provider
		.decrypt_message(data)
		.ok()
		.flatten()
		.map(|decrypted| into_buffer(decrypted.plaintext))
		.unwrap_or_else(empty_buffer)
}
