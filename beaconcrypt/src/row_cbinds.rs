// SPDX-License-Identifier: 0BSD

use std::{cell::Cell, ffi::c_void, slice};
use zeroize::Zeroizing;

use crate::cbinds::{
	Buffer, RegistrationResponse, STATUS_ENCODING, STATUS_GENERATION_EXHAUSTED,
	STATUS_INITIALIZATION, STATUS_INVALID_ARGUMENT, STATUS_INVALID_SNAPSHOT,
	STATUS_MISSING_SNAPSHOT, STATUS_OK, STATUS_REJECTED, STATUS_STALE_GENERATION, empty_buffer,
	into_buffer,
};
use crate::{
	RowError, RowRegistrationDecision, RowRegistrationPhase, RowServer, RowSession, RowStore,
	RowTransaction, RowTransition, SnapshotLineage,
};

/// A database-backed row server. Serialize calls on one handle and never reenter it from callbacks.
pub struct RowServerHandle(RowServer<Box<dyn RowStore>>, Cell<u32>);

/// A committed row message and authenticated peer/sequence metadata. Free `data` with `beaconcrypt_free_buffer`; it contains ciphertext for encrypt and plaintext for decrypt. Failure returns an empty buffer and zero metadata; inspect the server's last status.
#[repr(C)]
pub struct RowMessageBuffer {
	pub data: Buffer,
	pub key_id: u64,
	pub seq: u64,
}

fn empty_message() -> RowMessageBuffer {
	RowMessageBuffer {
		data: empty_buffer(),
		key_id: 0,
		seq: 0,
	}
}

/// A storage failure, including an uncertain commit outcome. No operation output is released.
pub const ROW_STATUS_STORAGE: u32 = 13;
pub const ROW_STATUS_INVALID_SESSION: u32 = 14;
pub const ROW_PHASE_ACCEPTANCE: u32 = 1;
pub const ROW_PHASE_COMPLETION: u32 = 2;

/// A serializable database transaction interface. `begin`, `store` and `commit` return true on success. `commit` must durably commit the outer transaction before returning true. `rollback` must safely discard any active transaction or do nothing if none exists; it is called after failed begin or commit callbacks. `load` returns 0 for absence, 1 after synchronously calling the sink exactly once, and -1 on error. Protect every read, including absence, with locks or atomic read-set validation at commit. Values are secret, opaque bytes; keys must be stored exactly. Constructors consume context immediately, and invoke destroy exactly once, including on failure. Borrowed pointers and sinks must not escape callbacks. Callbacks must not unwind or reenter the handle. The database must protect integrity, provenance and rollback resistance.
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
		RowError::InvalidSession => ROW_STATUS_INVALID_SESSION,
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
	beaconcrypt_row_server_encrypt_with_metadata(handle, data, len, kid).data
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_encrypt_with_metadata(
	handle: *mut RowServerHandle,
	data: *const u8,
	len: usize,
	kid: u64,
) -> RowMessageBuffer {
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_message();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = (unsafe { bytes(data, len) }) else {
		return empty_message();
	};
	complete(&server.1, server.0.encrypt_message(data, kid)).map_or_else(empty_message, |value| {
		RowMessageBuffer {
			data: into_buffer(value.ciphertext),
			key_id: value.key_id,
			seq: value.seq,
		}
	})
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_decrypt(
	handle: *mut RowServerHandle,
	data: *const u8,
	len: usize,
) -> Buffer {
	beaconcrypt_row_server_decrypt_with_metadata(handle, data, len).data
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_decrypt_with_metadata(
	handle: *mut RowServerHandle,
	data: *const u8,
	len: usize,
) -> RowMessageBuffer {
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_message();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = (unsafe { bytes(data, len) }) else {
		return empty_message();
	};
	complete(&server.1, server.0.decrypt_message(data)).map_or_else(empty_message, |value| {
		RowMessageBuffer {
			data: into_buffer(value.plaintext),
			key_id: value.key_id,
			seq: value.seq,
		}
	})
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

/// A trusted callback-scoped transaction session. The pointer and any calls using it must remain on the callback's thread and must not escape that callback. Recursive session calls are rejected and abort the transaction. Session outputs are pending and must not be published before the outer server call succeeds. Do not reenter the owning server.
pub struct RowSessionHandle {
	session: *mut RowSession<'static>,
	status: Cell<u32>,
	invalid_argument: Cell<bool>,
	invalid_session: Cell<bool>,
	busy: Cell<bool>,
}

/// The effect of an operation inside a transaction. `message.data` is null when no message was produced. `changed` can be true even without a message. Free a non-null message buffer with `beaconcrypt_free_buffer`. These bytes are pending until the outer transaction succeeds.
#[repr(C)]
pub struct RowTransitionBuffer {
	pub message: RowMessageBuffer,
	pub changed: bool,
}

fn session_handle(session: &mut RowSession<'_>) -> RowSessionHandle {
	RowSessionHandle {
		// The handle is only reachable during the callback while this borrow remains valid.
		session: (session as *mut RowSession<'_>).cast::<RowSession<'static>>(),
		status: Cell::new(STATUS_OK),
		invalid_argument: Cell::new(false),
		invalid_session: Cell::new(false),
		busy: Cell::new(false),
	}
}

fn callback_output(output: Loaded, succeeded: bool) -> Result<Zeroizing<Vec<u8>>, RowError> {
	if succeeded
		&& !output.invalid
		&& let Some(bytes) = output.bytes
	{
		return Ok(bytes);
	}
	Err(RowError::Storage(
		"application callback failed or returned invalid output".into(),
	))
}

fn session_callback_output(
	handle: &RowSessionHandle,
	output: Loaded,
	succeeded: bool,
) -> Result<Zeroizing<Vec<u8>>, RowError> {
	if handle.invalid_session.get() {
		return Err(RowError::InvalidSession);
	}
	callback_output(output, succeeded && !handle.invalid_argument.get())
}

struct SessionCall<'a>(&'a RowSessionHandle);
impl Drop for SessionCall<'_> {
	fn drop(&mut self) {
		self.0.busy.set(false);
	}
}
impl RowSessionHandle {
	fn enter(&self) -> Option<SessionCall<'_>> {
		if self.invalid_session.get() {
			self.status.set(ROW_STATUS_INVALID_SESSION);
			return None;
		}
		if self.invalid_argument.get() {
			self.status.set(STATUS_INVALID_ARGUMENT);
			return None;
		}
		if self.busy.replace(true) {
			self.invalid_session.set(true);
			self.status.set(ROW_STATUS_INVALID_SESSION);
			return None;
		}
		Some(SessionCall(self))
	}
}

/// Compose application rows and at most one native transition in one durable transaction. The callback returns true after calling its supplied sink exactly once, including for an empty result; false aborts. The sink copies bytes synchronously and must not escape the callback. Context is borrowed for this call; no destructor is invoked. The callback is trusted not to publish pending results. Only this function's returned buffer is commit-gated; an error returns a null buffer and sets last_status.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_transaction(
	handle: *mut RowServerHandle,
	context: *mut c_void,
	callback: Option<
		unsafe extern "C" fn(
			*mut c_void,
			*mut RowSessionHandle,
			*mut c_void,
			unsafe extern "C" fn(*mut c_void, *const u8, usize),
		) -> bool,
	>,
) -> Buffer {
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_buffer();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let Some(callback) = callback else {
		return empty_buffer();
	};
	let output = server.0.transaction(|session| {
		let mut handle = session_handle(session);
		let mut output = Loaded::default();
		let succeeded = unsafe {
			callback(
				context,
				&mut handle,
				(&mut output as *mut Loaded).cast(),
				load_sink,
			)
		};
		session_callback_output(&handle, output, succeeded)
	});
	complete(&server.1, output.map(Some)).map_or_else(empty_buffer, |mut bytes| {
		into_buffer(std::mem::take(&mut *bytes))
	})
}

/// Compose the two registration commits. Acceptance returns 0 for a final result, 1 to continue, or -1 to abort; it calls its sink exactly once for 0 or 1, supplying final-result or completion-context bytes respectively. Completion returns true and calls its sink exactly once with final-result bytes, or returns false to abort. All sinks copy synchronously and must not escape their callback. The acceptance callback can return a cached result without accepting, or accept once and continue with application context. Completion runs only after confirmed acceptance commit. On error, phase_out is ACCEPTANCE or COMPLETION; completion means acceptance definitely committed. Unknown commits require authoritative application-row lookup. Context and callbacks are borrowed only for this call.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_server_registration_transaction(
	handle: *mut RowServerHandle,
	context: *mut c_void,
	accept: Option<
		unsafe extern "C" fn(
			*mut c_void,
			*mut RowSessionHandle,
			*mut c_void,
			unsafe extern "C" fn(*mut c_void, *const u8, usize),
		) -> i32,
	>,
	finish: Option<
		unsafe extern "C" fn(
			*mut c_void,
			*mut RowSessionHandle,
			*const u8,
			usize,
			*mut c_void,
			unsafe extern "C" fn(*mut c_void, *const u8, usize),
		) -> bool,
	>,
	phase_out: *mut u32,
) -> Buffer {
	if !phase_out.is_null() {
		unsafe { *phase_out = ROW_PHASE_ACCEPTANCE };
	}
	let Some(server) = (unsafe { handle.as_mut() }) else {
		return empty_buffer();
	};
	server.1.set(STATUS_INVALID_ARGUMENT);
	let (Some(accept), Some(finish)) = (accept, finish) else {
		return empty_buffer();
	};
	let output = server.0.registration_transaction(
		|session| {
			let mut handle = session_handle(session);
			let mut output = Loaded::default();
			let decision = unsafe {
				accept(
					context,
					&mut handle,
					(&mut output as *mut Loaded).cast(),
					load_sink,
				)
			};
			let output = session_callback_output(&handle, output, decision == 0 || decision == 1)?;
			Ok(if decision == 0 {
				RowRegistrationDecision::Return(output)
			} else {
				RowRegistrationDecision::Continue(output)
			})
		},
		|session, accepted: Zeroizing<Vec<u8>>| {
			let mut handle = session_handle(session);
			let mut output = Loaded::default();
			let succeeded = unsafe {
				finish(
					context,
					&mut handle,
					accepted.as_ptr(),
					accepted.len(),
					(&mut output as *mut Loaded).cast(),
					load_sink,
				)
			};
			session_callback_output(&handle, output, succeeded)
		},
	);
	match output {
		Ok(mut output) => {
			server.1.set(STATUS_OK);
			if !phase_out.is_null() {
				unsafe { *phase_out = 0 };
			}
			into_buffer(std::mem::take(&mut *output))
		}
		Err(error) => {
			server.1.set(status(error.source));
			if !phase_out.is_null() {
				unsafe {
					*phase_out = match error.phase {
						RowRegistrationPhase::Acceptance => ROW_PHASE_ACCEPTANCE,
						RowRegistrationPhase::Completion => ROW_PHASE_COMPLETION,
					}
				};
			}
			empty_buffer()
		}
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_last_status(handle: *const RowSessionHandle) -> u32 {
	unsafe { handle.as_ref() }.map_or(STATUS_INVALID_ARGUMENT, |handle| handle.status.get())
}

fn session_bytes<'a>(
	handle: &RowSessionHandle,
	pointer: *const u8,
	len: usize,
) -> Option<&'a [u8]> {
	let output = unsafe { bytes(pointer, len) };
	if output.is_none() {
		handle.invalid_argument.set(true);
	}
	output
}

/// Application keys are scoped separately from native records. A null result with STATUS_REJECTED is absence; a non-null zero-length buffer is a present empty value.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_load(
	handle: *mut RowSessionHandle,
	key: *const u8,
	key_len: usize,
) -> Buffer {
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return empty_buffer();
	};
	let Some(_guard) = handle.enter() else {
		return empty_buffer();
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let Some(key) = session_bytes(handle, key, key_len) else {
		return empty_buffer();
	};
	let result = unsafe { &mut *handle.session }.load_application(key);
	complete(&handle.status, result).map_or_else(empty_buffer, |mut value| {
		into_buffer(std::mem::take(&mut *value))
	})
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_store(
	handle: *mut RowSessionHandle,
	key: *const u8,
	key_len: usize,
	value: *const u8,
	value_len: usize,
) -> bool {
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return false;
	};
	let Some(_guard) = handle.enter() else {
		return false;
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let (Some(key), Some(value)) = (
		session_bytes(handle, key, key_len),
		session_bytes(handle, value, value_len),
	) else {
		return false;
	};
	let result = unsafe { &mut *handle.session }.store_application(key, value);
	complete(&handle.status, result.map(Some)).is_some()
}

fn session_transition(
	handle: &RowSessionHandle,
	output: Result<RowTransition, RowError>,
) -> RowTransitionBuffer {
	match output {
		Ok(output) => {
			handle.status.set(STATUS_OK);
			RowTransitionBuffer {
				message: output
					.message
					.map_or_else(empty_message, |message| RowMessageBuffer {
						data: into_buffer(message.data().to_vec()),
						key_id: message.key_id(),
						seq: message.sequence(),
					}),
				changed: output.changed,
			}
		}
		Err(error) => {
			handle.status.set(status(error));
			RowTransitionBuffer {
				message: empty_message(),
				changed: false,
			}
		}
	}
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_encrypt(
	handle: *mut RowSessionHandle,
	data: *const u8,
	len: usize,
	kid: u64,
) -> RowTransitionBuffer {
	let empty = || RowTransitionBuffer {
		message: empty_message(),
		changed: false,
	};
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return empty();
	};
	let Some(_guard) = handle.enter() else {
		return empty();
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = session_bytes(handle, data, len) else {
		return empty();
	};
	let output = unsafe { &mut *handle.session }.encrypt_message(data, kid);
	session_transition(handle, output)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_decrypt(
	handle: *mut RowSessionHandle,
	data: *const u8,
	len: usize,
) -> RowTransitionBuffer {
	let empty = || RowTransitionBuffer {
		message: empty_message(),
		changed: false,
	};
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return empty();
	};
	let Some(_guard) = handle.enter() else {
		return empty();
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = session_bytes(handle, data, len) else {
		return empty();
	};
	let output = unsafe { &mut *handle.session }.decrypt_message(data);
	session_transition(handle, output)
}

#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_accept_registration(
	handle: *mut RowSessionHandle,
	data: *const u8,
	len: usize,
) -> bool {
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return false;
	};
	let Some(_guard) = handle.enter() else {
		return false;
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let Some(data) = session_bytes(handle, data, len) else {
		return false;
	};
	let output = unsafe { &mut *handle.session }.accept_registration(data);
	match output {
		Ok(accepted) => {
			handle
				.status
				.set(if accepted { STATUS_OK } else { STATUS_REJECTED });
			accepted
		}
		Err(error) => {
			handle.status.set(status(error));
			false
		}
	}
}

/// A null initial message uses the protocol witness; a non-null empty one attempts an empty payload. This function is valid only in the completion callback.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_row_session_complete_registration(
	handle: *mut RowSessionHandle,
	message: *const u8,
	len: usize,
) -> RowTransitionBuffer {
	let empty = || RowTransitionBuffer {
		message: empty_message(),
		changed: false,
	};
	let Some(handle) = (unsafe { handle.as_ref() }) else {
		return empty();
	};
	let Some(_guard) = handle.enter() else {
		return empty();
	};
	handle.status.set(STATUS_INVALID_ARGUMENT);
	let Some(bytes) = session_bytes(handle, message, len) else {
		return empty();
	};
	let output = unsafe { &mut *handle.session }
		.complete_registration((!message.is_null()).then_some(bytes));
	session_transition(handle, output)
}

#[cfg(test)]
mod composition_tests {
	use super::*;

	#[test]
	fn invalid_argument_blocks_later_native_access() {
		let handle = RowSessionHandle {
			session: std::ptr::null_mut(),
			status: Cell::new(STATUS_OK),
			invalid_argument: Cell::new(false),
			invalid_session: Cell::new(false),
			busy: Cell::new(false),
		};
		let pointer = (&handle as *const RowSessionHandle).cast_mut();
		for key_len in [1, 0] {
			assert!(!beaconcrypt_row_session_store(
				pointer,
				std::ptr::null(),
				key_len,
				std::ptr::null(),
				0,
			));
			assert_eq!(handle.status.get(), STATUS_INVALID_ARGUMENT);
		}
	}

	#[test]
	fn recursive_session_call_is_rejected_before_borrowing_native_session() {
		let handle = RowSessionHandle {
			session: std::ptr::null_mut(),
			status: Cell::new(STATUS_OK),
			invalid_argument: Cell::new(false),
			invalid_session: Cell::new(false),
			busy: Cell::new(false),
		};
		let pointer = (&handle as *const RowSessionHandle).cast_mut();
		let guard = handle.enter().unwrap();
		// The deliberately absent native pointer must never be dereferenced by a nested call.
		assert!(!beaconcrypt_row_session_store(
			pointer,
			std::ptr::null(),
			0,
			std::ptr::null(),
			0,
		));
		assert_eq!(handle.status.get(), ROW_STATUS_INVALID_SESSION);
		drop(guard);
		assert!(!handle.busy.get());
		assert!(!beaconcrypt_row_session_store(
			pointer,
			std::ptr::null(),
			0,
			std::ptr::null(),
			0,
		));
		assert_eq!(handle.status.get(), ROW_STATUS_INVALID_SESSION);
		let output = Loaded {
			bytes: Some(Zeroizing::new(Vec::new())),
			invalid: false,
		};
		assert_eq!(
			session_callback_output(&handle, output, true).err(),
			Some(RowError::InvalidSession)
		);
	}
}
