// SPDX-License-Identifier: 0BSD

use std::{cell::Cell, ffi::c_void, slice};
use zeroize::Zeroizing;

use crate::cbinds::{
	Buffer, RegistrationResponse, STATUS_ENCODING, STATUS_GENERATION_EXHAUSTED,
	STATUS_INITIALIZATION, STATUS_INVALID_ARGUMENT, STATUS_INVALID_SNAPSHOT,
	STATUS_MISSING_SNAPSHOT, STATUS_OK, STATUS_REJECTED, STATUS_STALE_GENERATION, empty_buffer,
	into_buffer,
};
use crate::{RowError, RowServer, RowStore, RowTransaction, SnapshotLineage};

/// A database-backed row server. Serialize calls on one handle and never reenter it from callbacks.
pub struct RowServerHandle(RowServer<Box<dyn RowStore>>, Cell<u32>);

/// A storage failure, including an uncertain commit outcome. No operation output is released.
pub const ROW_STATUS_STORAGE: u32 = 13;

/// A serializable database transaction interface. `begin`, `store` and `commit` return true on success. `commit` must durably commit the outer transaction before returning true. `rollback` must safely discard any active transaction or do nothing if none exists; it is called after failed begin or commit callbacks. `load` returns 0 for absence, 1 after synchronously calling the sink exactly once, and -1 on error. Loads must lock rows or otherwise prevent concurrent lost updates, including absent-key insertion races. Values are secret, opaque bytes; keys must be stored exactly. Constructors consume context immediately, and invoke destroy exactly once, including on failure. Borrowed pointers and sinks must not escape callbacks. Callbacks must not unwind or reenter the handle. The database must protect integrity, provenance and rollback resistance.
#[repr(C)]
pub struct RowStoreCallbacks {
	pub context: *mut c_void,
	pub begin: Option<unsafe extern "C" fn(*mut c_void) -> bool>,
	pub load: Option<
		unsafe extern "C" fn(
			*mut c_void,
			*const u8,
			usize,
			*mut c_void,
			unsafe extern "C" fn(*mut c_void, *const u8, usize),
		) -> i32,
	>,
	pub store:
		Option<unsafe extern "C" fn(*mut c_void, *const u8, usize, *const u8, usize) -> bool>,
	pub commit: Option<unsafe extern "C" fn(*mut c_void) -> bool>,
	pub rollback: Option<unsafe extern "C" fn(*mut c_void)>,
	pub destroy: Option<unsafe extern "C" fn(*mut c_void)>,
}

struct CallbackStore(RowStoreCallbacks);

impl Drop for CallbackStore {
	fn drop(&mut self) {
		if let Some(destroy) = self.0.destroy {
			unsafe { destroy(self.0.context) };
		}
	}
}

#[derive(Default)]
struct Loaded {
	bytes: Option<Zeroizing<Vec<u8>>>,
	invalid: bool,
}

unsafe extern "C" fn load_sink(context: *mut c_void, bytes: *const u8, len: usize) {
	let loaded = unsafe { &mut *context.cast::<Loaded>() };
	if loaded.bytes.is_some() || (bytes.is_null() && len != 0) || len > isize::MAX as usize {
		loaded.invalid = true;
		return;
	}
	let value = if len == 0 {
		Vec::new()
	} else {
		unsafe { slice::from_raw_parts(bytes, len) }.to_vec()
	};
	loaded.bytes = Some(Zeroizing::new(value));
}

fn storage_error() -> RowError {
	RowError::Storage("database callback failed".into())
}

impl RowTransaction for CallbackStore {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		let mut loaded = Loaded::default();
		let status = unsafe {
			self.0.load.expect("validated callback")(
				self.0.context,
				key.as_ptr(),
				key.len(),
				(&mut loaded as *mut Loaded).cast(),
				load_sink,
			)
		};
		match (status, loaded.invalid, loaded.bytes) {
			(0, false, None) => Ok(None),
			(1, false, Some(mut bytes)) => Ok(Some(std::mem::take(&mut *bytes))),
			_ => Err(storage_error()),
		}
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		if unsafe {
			self.0.store.expect("validated callback")(
				self.0.context,
				key.as_ptr(),
				key.len(),
				value.as_ptr(),
				value.len(),
			)
		} {
			Ok(())
		} else {
			Err(storage_error())
		}
	}
}

impl RowStore for CallbackStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		if !unsafe { self.0.begin.expect("validated callback")(self.0.context) } {
			unsafe { self.0.rollback.expect("validated callback")(self.0.context) };
			return Err(storage_error());
		}
		let result = operation(self).and_then(|()| {
			if unsafe { self.0.commit.expect("validated callback")(self.0.context) } {
				Ok(())
			} else {
				Err(storage_error())
			}
		});
		if result.is_err() {
			unsafe { self.0.rollback.expect("validated callback")(self.0.context) };
		}
		result
	}
}

fn status(error: RowError) -> u32 {
	match error {
		RowError::Storage(_) => ROW_STATUS_STORAGE,
		RowError::Conflict => STATUS_STALE_GENERATION,
		RowError::MissingIdentity => STATUS_MISSING_SNAPSHOT,
		RowError::InvalidRow => STATUS_INVALID_SNAPSHOT,
		RowError::GenerationExhausted => STATUS_GENERATION_EXHAUSTED,
		RowError::Initialization => STATUS_INITIALIZATION,
		RowError::OutputEncoding => STATUS_ENCODING,
	}
}

fn valid(store: &CallbackStore) -> bool {
	store.0.begin.is_some()
		&& store.0.load.is_some()
		&& store.0.store.is_some()
		&& store.0.commit.is_some()
		&& store.0.rollback.is_some()
}

unsafe fn bytes<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
	if len > isize::MAX as usize || (ptr.is_null() && len != 0) {
		return None;
	}
	if len == 0 {
		Some(&[])
	} else {
		Some(unsafe { slice::from_raw_parts(ptr, len) })
	}
}

fn construct(
	result: Result<RowServer<Box<dyn RowStore>>, RowError>,
	out: *mut u32,
) -> *mut RowServerHandle {
	match result {
		Ok(server) => {
			if !out.is_null() {
				unsafe { *out = STATUS_OK };
			}
			Box::into_raw(Box::new(RowServerHandle(server, Cell::new(STATUS_OK))))
		}
		Err(error) => {
			if !out.is_null() {
				unsafe { *out = status(error) };
			}
			std::ptr::null_mut()
		}
	}
}

/// Create a server in an empty database namespace. Lineage must have 32 bytes; each optional seed has zero or 32 bytes. Store context is consumed even on invalid arguments.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_create(
	kid: u64,
	seed: *const u8,
	seed_len: usize,
	mldsa: *const u8,
	mldsa_len: usize,
	callbacks: RowStoreCallbacks,
	lineage: *const u8,
	lineage_len: usize,
	status_out: *mut u32,
) -> *mut RowServerHandle {
	let store = CallbackStore(callbacks);
	if !status_out.is_null() {
		unsafe { *status_out = STATUS_INVALID_ARGUMENT };
	}
	let Some(seed) = (unsafe { bytes(seed, seed_len) }) else {
		return std::ptr::null_mut();
	};
	let Some(mldsa) = (unsafe { bytes(mldsa, mldsa_len) }) else {
		return std::ptr::null_mut();
	};
	let Some(lineage) = (unsafe { bytes(lineage, lineage_len) }).and_then(|b| b.try_into().ok())
	else {
		return std::ptr::null_mut();
	};
	if !valid(&store) || !matches!(seed.len(), 0 | 32) || !matches!(mldsa.len(), 0 | 32) {
		return std::ptr::null_mut();
	}
	let store: Box<dyn RowStore> = Box::new(store);
	construct(
		RowServer::create(
			kid,
			(!seed.is_empty()).then_some(seed),
			(!mldsa.is_empty()).then_some(mldsa),
			store,
			SnapshotLineage::from_bytes(lineage),
		),
		status_out,
	)
}

/// Open an existing namespace without loading peers or advancing their state. Store context is consumed even on failure.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_open(
	callbacks: RowStoreCallbacks,
	lineage: *const u8,
	lineage_len: usize,
	status_out: *mut u32,
) -> *mut RowServerHandle {
	let store = CallbackStore(callbacks);
	if !status_out.is_null() {
		unsafe { *status_out = STATUS_INVALID_ARGUMENT };
	}
	let Some(lineage) = (unsafe { bytes(lineage, lineage_len) }).and_then(|b| b.try_into().ok())
	else {
		return std::ptr::null_mut();
	};
	if !valid(&store) {
		return std::ptr::null_mut();
	}
	let store: Box<dyn RowStore> = Box::new(store);
	construct(
		RowServer::open(store, SnapshotLineage::from_bytes(lineage)),
		status_out,
	)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_free(handle: *mut RowServerHandle) {
	if !handle.is_null() {
		drop(unsafe { Box::from_raw(handle) });
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_last_status(handle: *const RowServerHandle) -> u32 {
	if handle.is_null() {
		STATUS_INVALID_ARGUMENT
	} else {
		unsafe { &*handle }.1.get()
	}
}

fn complete<T>(status_out: &Cell<u32>, result: Result<Option<T>, RowError>) -> Option<T> {
	match result {
		Ok(Some(value)) => {
			status_out.set(STATUS_OK);
			Some(value)
		}
		Ok(None) => {
			status_out.set(STATUS_REJECTED);
			None
		}
		Err(error) => {
			status_out.set(status(error));
			None
		}
	}
}

/// A null message with zero length omits the initial payload; a non-null zero-length message supplies an empty payload and rejects response construction after consuming the registration.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_register(
	handle: *mut RowServerHandle,
	registration: *const u8,
	registration_len: usize,
	message: *const u8,
	message_len: usize,
) -> RegistrationResponse {
	let empty = || RegistrationResponse {
		response: empty_buffer(),
		key_id: 0,
	};
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(registration) = (unsafe { bytes(registration, registration_len) }) else {
		return empty();
	};
	let has_message = !message.is_null();
	let Some(message) = (unsafe { bytes(message, message_len) }) else {
		return empty();
	};
	match complete(
		&server.1,
		server
			.0
			.register_beacon(registration, has_message.then_some(message)),
	) {
		Some(response) => RegistrationResponse {
			response: into_buffer(response.serialized),
			key_id: response.kid,
		},
		None => empty(),
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_encrypt(
	handle: *mut RowServerHandle,
	data: *const u8,
	len: usize,
	kid: u64,
) -> Buffer {
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_buffer();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = (unsafe { bytes(data, len) }) else {
		return empty_buffer();
	};
	complete(&server.1, server.0.encrypt_message(data, kid))
		.map_or_else(empty_buffer, |value| into_buffer(value.ciphertext))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_decrypt(
	handle: *mut RowServerHandle,
	data: *const u8,
	len: usize,
) -> Buffer {
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_buffer();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = (unsafe { bytes(data, len) }) else {
		return empty_buffer();
	};
	complete(&server.1, server.0.decrypt_message(data))
		.map_or_else(empty_buffer, |value| into_buffer(value.plaintext))
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_identity_pk(handle: *const RowServerHandle) -> Buffer {
	unsafe { handle.as_ref() }.map_or_else(empty_buffer, |server| {
		into_buffer(server.0.identity_pk().as_bytes().to_vec())
	})
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_mldsa_public_key(
	handle: *const RowServerHandle,
) -> Buffer {
	unsafe { handle.as_ref() }.map_or_else(empty_buffer, |server| {
		into_buffer(server.0.mldsa_public_key().to_vec())
	})
}
