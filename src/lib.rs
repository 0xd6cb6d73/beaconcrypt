// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
mod beacon;
#[cfg(feature = "cnsa2")]
mod cnsa2;
mod error;
#[cfg(feature = "pqxdh")]
mod pqxdh;
#[cfg(feature = "server")]
mod server;
mod shared;

#[cfg(all(windows, target_env = "gnu"))]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset_explicit(
	dest: *mut std::ffi::c_void,
	ch: std::ffi::c_int,
	count: usize,
) -> *mut std::ffi::c_void {
	unsafe { std::ptr::write_bytes(dest, ch as u8, count) };
	std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
	dest
}

#[cfg(all(windows, target_env = "gnu"))]
#[link(name = "bcrypt")]
unsafe extern "system" {
	fn BCryptGenRandom(
		algorithm: *mut std::ffi::c_void,
		buffer: *mut u8,
		buffer_len: u32,
		flags: u32,
	) -> i32;
}

#[cfg(all(windows, target_env = "gnu"))]
#[unsafe(no_mangle)]
pub unsafe extern "system" fn SystemFunction036(
	buffer: *mut std::ffi::c_void,
	buffer_len: u32,
) -> u8 {
	const BCRYPT_USE_SYSTEM_PREFERRED_RNG: u32 = 0x00000002;
	let status = unsafe {
		BCryptGenRandom(
			std::ptr::null_mut(),
			buffer.cast::<u8>(),
			buffer_len,
			BCRYPT_USE_SYSTEM_PREFERRED_RNG,
		)
	};
	u8::from(status >= 0)
}

#[cfg(feature = "beacon")]
pub use beacon::ProviderBeacon;
pub use error::{
	CipherTextError, DecodingError, DecryptionError, EncodingError, KeyGenError, SignatureError,
};
#[cfg(feature = "pqxdh")]
pub use pqxdh::BeaconCryptPqxdh;
#[cfg(feature = "server")]
pub use server::{ProviderServer, RegResponse, RegistrationOutput};
pub use shared::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, CryptoProvider, DH_OUT_LEN, ED25519_SEED_SIZE,
	KDF_RATCHET_OUTPUT_LEN, KDF_STATE_SIZE, KEX_KDF_OUT_LEN, SignType,
};

capnp::generated_code!(pub mod phase1_capnp);
capnp::generated_code!(pub mod phase2_capnp);
capnp::generated_code!(pub mod cryptoframe_capnp);
capnp::generated_code!(pub mod protogram_capnp);

#[cfg(feature = "pybinds")]
use pyo3::prelude::*;

#[cfg(feature = "pqxdh")]
mod gobinds {
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
	pub extern "C" fn beaconcrypt_go_generate_registration(
		handle: *mut BeaconCryptPqxdh,
	) -> GoBuffer {
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
		encrypt(handle, ptr, len, true, key_id)
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
		match provider.encrypt_message(data, true, key_id) {
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
		decrypt(handle, ptr, len, key_id, false)
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
		encrypt(handle, ptr, len, false, provider.server_kid())
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
		decrypt(handle, ptr, len, provider.server_kid(), true)
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
				.decrypt_message(&verified.data, provider.server_kid(), true)
				.map(into_buffer)
				.unwrap_or_else(empty_buffer),
			None => empty_buffer(),
		}
	}

	fn encrypt(
		handle: *mut BeaconCryptPqxdh,
		ptr: *const u8,
		len: usize,
		stob: bool,
		key_id: u64,
	) -> GoBuffer {
		if handle.is_null() {
			return empty_buffer();
		}
		let Some(data) = (unsafe { input(ptr, len) }) else {
			return empty_buffer();
		};
		let provider = unsafe { &mut *handle };
		provider
			.encrypt_message(data, stob, key_id)
			.map(into_buffer)
			.unwrap_or_else(empty_buffer)
	}

	fn decrypt(
		handle: *mut BeaconCryptPqxdh,
		ptr: *const u8,
		len: usize,
		key_id: u64,
		stob: bool,
	) -> GoBuffer {
		if handle.is_null() {
			return empty_buffer();
		}
		let Some(data) = (unsafe { input(ptr, len) }) else {
			return empty_buffer();
		};
		let provider = unsafe { &mut *handle };
		provider
			.decrypt_message(data, key_id, stob)
			.map(into_buffer)
			.unwrap_or_else(empty_buffer)
	}
}

#[cfg(feature = "pybinds")]
#[pymodule(name = "beaconcrypt")]
pub mod beaconcrypt_py {
	use crate::{BeaconCryptPqxdh, CryptoProvider, ProviderBeacon, ProviderServer, RegResponse};
	use pyo3::prelude::*;

	#[pyclass(name = "RegResponse")]
	pub struct RegResponsePy {
		_0: RegResponse,
	}

	#[pymethods]
	impl RegResponsePy {
		pub fn serialized(&self) -> &Vec<u8> {
			&self._0.serialized
		}

		pub fn key_id(&self) -> u64 {
			self._0.kid
		}
	}

	impl From<RegResponse> for RegResponsePy {
		fn from(value: RegResponse) -> Self {
			Self { _0: value }
		}
	}

	#[pyclass(name = "BeaconCryptServer")]
	pub struct Server {
		_0: BeaconCryptPqxdh,
	}

	#[pymethods]
	impl Server {
		#[new]
		fn new(kid: u64, id_seed: Option<&[u8]>) -> Self {
			Self {
				_0: BeaconCryptPqxdh::new(false, kid, None, id_seed),
			}
		}

		fn register_beacon(
			&mut self,
			reg_buffer: &[u8],
			initial_message: Option<&[u8]>,
		) -> Option<RegResponsePy> {
			match self._0.get_shared_secret(reg_buffer) {
				Some(secrets) => self
					._0
					.build_registration_response(secrets.clone(), initial_message)
					.map(|response| response.into()),
				None => None,
			}
		}

		fn decrypt_beacon_message(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
			self._0.decrypt_message(&data, kid, false)
		}

		fn decrypt_beacon_message_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			match self._0.verify_signature(&data) {
				Some(verified) => self.decrypt_beacon_message(verified.data, verified.key_id),
				None => None,
			}
		}

		fn encrypt_to_beacon(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
			self._0.encrypt_message(&data, true, kid)
		}

		fn encrypt_to_beacon_signed(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
			match self.encrypt_to_beacon(data, kid) {
				Some(ciphertext) => self._0.sign_message(ciphertext.as_slice()),
				None => None,
			}
		}

		fn id_pk(&self) -> &[u8] {
			self._0.identity_pk().as_bytes()
		}
	}

	#[pyclass(name = "BeaconCryptBeacon")]
	pub struct Beacon {
		_0: BeaconCryptPqxdh,
	}
	#[pymethods]
	impl Beacon {
		#[new]
		fn new(server_kid: u64, server_id_pk: Option<&[u8]>) -> Self {
			Self {
				_0: BeaconCryptPqxdh::new(true, server_kid, server_id_pk, None),
			}
		}

		/// Begin the beacon registration process. The output buffer should be sent as-is over the network.
		fn generate_registration(&mut self) -> Option<Vec<u8>> {
			self._0.get_registration_bundle()
		}

		/// Process the registration response and optional initial data. The raw buffer sent by the server must be passed as-is as `data`. The response contains the contents of the initial message, or nothing if there was none. Once this function returns, the beacon is registered
		fn process_initial_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			self._0.finish_registration(data.as_slice())
		}

		fn decrypt_server_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			let srv_seq = self._0.server_kid();
			println!("{}", srv_seq);
			self._0.decrypt_message(&data, srv_seq, true)
		}

		fn decrypt_server_message_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			match self._0.verify_signature(&data) {
				Some(verified) => self.decrypt_server_message(verified.data),
				None => None,
			}
		}

		fn encrypt_message_to_server(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			let srv_seq = self._0.server_kid();
			self._0.encrypt_message(&data, false, srv_seq)
		}

		fn encrypt_to_server_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
			match self.encrypt_message_to_server(data) {
				Some(ciphertext) => self._0.sign_message(ciphertext.as_slice()),
				None => None,
			}
		}
	}
}
