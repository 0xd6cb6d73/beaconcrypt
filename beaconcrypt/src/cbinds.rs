// SPDX-License-Identifier: 0BSD

use crate::persistence::{
	BindingSnapshotStore, PersistenceError, PersistentServer, ServerSnapshot, SnapshotHead,
	SnapshotLineage, SnapshotStore,
};
use crate::server::{RecvState, SendState};
use crate::{Beacon, ProviderBeacon, SendOutcome};
use std::cell::{Cell, UnsafeCell};
use std::ffi::c_void;
use std::mem;
use std::slice;
use zeroize::{Zeroize, Zeroizing};

/// Opaque server handle owned by the C caller.
///
/// Callers must serialize all access to one handle, including queries and destruction. Store callbacks must not reenter their owning handle; such a call is refused with `STATUS_INVALID_ARGUMENT` or an empty result, and a reentrant free is ignored.
pub struct Server(
	Exclusive<PersistentServer<Box<dyn SnapshotStore>>>,
	Cell<u32>,
);

/// Owner state that at most one entry point can borrow at a time.
///
/// Entry points hold only a shared reference to their handle, so a reentrant call can observe the
/// busy flag without aliasing the active call's mutable borrow.
pub(crate) struct Exclusive<T> {
	value: UnsafeCell<T>,
	busy: Cell<bool>,
}

/// Exclusive access released when dropped.
pub(crate) struct ExclusiveGuard<'a, T> {
	value: &'a mut T,
	busy: &'a Cell<bool>,
}

impl<T> Exclusive<T> {
	pub(crate) const fn new(value: T) -> Self {
		Self {
			value: UnsafeCell::new(value),
			busy: Cell::new(false),
		}
	}

	/// Borrow the owner, or return `None` while another entry point on this handle is active.
	pub(crate) fn enter(&self) -> Option<ExclusiveGuard<'_, T>> {
		if self.busy.replace(true) {
			return None;
		}
		// The busy flag admits one guard at a time, and `Cell` keeps the handle single-threaded.
		Some(ExclusiveGuard {
			value: unsafe { &mut *self.value.get() },
			busy: &self.busy,
		})
	}

	pub(crate) fn is_busy(&self) -> bool {
		self.busy.get()
	}

	#[cfg(test)]
	pub(crate) fn get_mut(&mut self) -> &mut T {
		self.value.get_mut()
	}
}

impl<T> core::ops::Deref for ExclusiveGuard<'_, T> {
	type Target = T;
	fn deref(&self) -> &T {
		self.value
	}
}

impl<T> core::ops::DerefMut for ExclusiveGuard<'_, T> {
	fn deref_mut(&mut self) -> &mut T {
		self.value
	}
}

impl<T> Drop for ExclusiveGuard<'_, T> {
	fn drop(&mut self) {
		self.busy.set(false);
	}
}

pub const STATUS_OK: u32 = 0;
pub const STATUS_REJECTED: u32 = 1;
pub const STATUS_INVALID_ARGUMENT: u32 = 2;
pub const STATUS_MISSING_SNAPSHOT: u32 = 3;
pub const STATUS_INVALID_SNAPSHOT: u32 = 4;
pub const STATUS_NON_CANONICAL_SNAPSHOT: u32 = 5;
pub const STATUS_STALE_GENERATION: u32 = 6;
pub const STATUS_GENERATION_EXHAUSTED: u32 = 7;
pub const STATUS_ENCODING: u32 = 8;
pub const STATUS_OUTPUT_ENCODING: u32 = 9;
pub const STATUS_INITIALIZATION: u32 = 10;
pub const STATUS_DIGEST: u32 = 11;
pub const STATUS_POISONED: u32 = 12;
pub const STATUS_STORAGE: u32 = 13;
// Status 14 belongs to invalid row transaction sessions.
pub const STATUS_COMMIT_UNKNOWN: u32 = 15;

/// Non-secret identity of one complete server snapshot. Its digest is not an authenticator.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SnapshotHeadInfo {
	pub lineage: [u8; 32],
	pub generation: u64,
	pub digest: [u8; 32],
}

impl From<SnapshotHead> for SnapshotHeadInfo {
	fn from(head: SnapshotHead) -> Self {
		Self {
			lineage: *head.lineage().as_bytes(),
			generation: head.generation(),
			digest: head.digest(),
		}
	}
}

impl From<SnapshotHeadInfo> for SnapshotHead {
	fn from(head: SnapshotHeadInfo) -> Self {
		Self::from_parts(
			SnapshotLineage::from_bytes(head.lineage),
			head.generation,
			head.digest,
		)
	}
}

/// Trusted, rollback-resistant, linearizable durable storage for one server lineage.
///
/// `load` returns false without calling `sink` for an empty store. Otherwise it calls `sink` synchronously exactly once with nonempty borrowed snapshot bytes and returns true; Rust copies the bytes before `sink` returns. `compare_and_swap` compares the complete current head against `expected` (null means an empty store), validates the successor, and durably stores the exact replacement bytes and head before returning true. The store must protect integrity, provenance and freshness; snapshot bytes and digests do not authenticate themselves.
///
/// Constructors take ownership of `context` immediately, including on failure. `destroy`, when supplied, runs exactly once after the final callback; otherwise the caller manages the context lifetime. All callbacks and borrowed arguments remain valid until they return, must not unwind, retain borrowed pointers, call the sink after `load` returns, or reenter the owning handle. The caller serializes access to the handle and store.
///
/// This original callback layout preserves the legacy C ABI. Use `SnapshotStoreCallbacksV2` and the constructors ending in `_v2` to report storage failures separately from absence and comparison rejection.
#[repr(C)]
pub struct SnapshotStoreCallbacks {
	pub context: *mut c_void,
	pub load: Option<
		unsafe extern "C" fn(
			context: *mut c_void,
			sink_context: *mut c_void,
			sink: unsafe extern "C" fn(*mut c_void, *const u8, usize),
		) -> bool,
	>,
	pub compare_and_swap: Option<
		unsafe extern "C" fn(
			context: *mut c_void,
			expected: *const SnapshotHeadInfo,
			replacement: *const u8,
			replacement_len: usize,
		) -> bool,
	>,
	pub destroy: Option<unsafe extern "C" fn(context: *mut c_void)>,
}

/// Versioned snapshot callbacks with storage-error reporting.
///
/// `last_error` reports the result of the immediately preceding load or CAS callback: STATUS_OK, STATUS_STORAGE for a definite failure without a commit, or STATUS_COMMIT_UNKNOWN if a CAS may have committed. Reset this status when beginning each callback. A null `last_error` retains the legacy empty-store or conflict interpretation of false. Context ownership and callback lifetime rules are the same as `SnapshotStoreCallbacks`.
#[repr(C)]
pub struct SnapshotStoreCallbacksV2 {
	pub callbacks: SnapshotStoreCallbacks,
	pub last_error: Option<unsafe extern "C" fn(context: *mut c_void) -> u32>,
}

struct CallbackStore {
	callbacks: SnapshotStoreCallbacks,
	last_error: Option<unsafe extern "C" fn(context: *mut c_void) -> u32>,
}

impl CallbackStore {
	fn check_error(&self) -> Result<(), PersistenceError> {
		let status = self.last_error.map_or(STATUS_OK, |callback| unsafe {
			callback(self.callbacks.context)
		});
		match status {
			STATUS_OK => Ok(()),
			STATUS_COMMIT_UNKNOWN => Err(PersistenceError::CommitUnknown),
			_ => Err(PersistenceError::Storage),
		}
	}
}

impl Drop for CallbackStore {
	fn drop(&mut self) {
		if let Some(destroy) = self.callbacks.destroy {
			unsafe { destroy(self.callbacks.context) };
		}
	}
}

#[derive(Default)]
struct SnapshotLoad {
	bytes: Option<Zeroizing<Vec<u8>>>,
	invalid: bool,
}

unsafe extern "C" fn snapshot_load_sink(context: *mut c_void, bytes: *const u8, len: usize) {
	let loaded = unsafe { &mut *context.cast::<SnapshotLoad>() };
	if loaded.invalid
		|| loaded.bytes.is_some()
		|| bytes.is_null()
		|| len == 0
		|| len > isize::MAX as usize
	{
		loaded.invalid = true;
		return;
	}
	loaded.bytes = Some(Zeroizing::new(
		unsafe { slice::from_raw_parts(bytes, len) }.to_vec(),
	));
}

impl SnapshotStore for CallbackStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, PersistenceError> {
		let mut loaded = SnapshotLoad::default();
		let present = unsafe {
			(self.callbacks.load.ok_or(PersistenceError::Storage)?)(
				self.callbacks.context,
				(&mut loaded as *mut SnapshotLoad).cast(),
				snapshot_load_sink,
			)
		};
		self.check_error()?;
		if !present && loaded.bytes.is_none() && !loaded.invalid {
			return Ok(None);
		}
		if !present || loaded.invalid || loaded.bytes.is_none() {
			return Ok(Some(ServerSnapshot::from_bytes(Vec::new())));
		}
		Ok(loaded
			.bytes
			.map(|mut bytes| ServerSnapshot::from_bytes(mem::take(&mut *bytes))))
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, PersistenceError> {
		let expected = expected.copied().map(SnapshotHeadInfo::from);
		let committed = unsafe {
			(self
				.callbacks
				.compare_and_swap
				.expect("validated store callback"))(
				self.callbacks.context,
				expected
					.as_ref()
					.map_or(std::ptr::null(), std::ptr::from_ref),
				abi_ptr(replacement.as_bytes()),
				replacement.as_bytes().len(),
			)
		};
		self.check_error()?;
		Ok(committed)
	}
}

fn error_status(error: PersistenceError) -> u32 {
	match error {
		PersistenceError::MissingSnapshot => STATUS_MISSING_SNAPSHOT,
		PersistenceError::InvalidSnapshot => STATUS_INVALID_SNAPSHOT,
		PersistenceError::NonCanonicalSnapshot => STATUS_NON_CANONICAL_SNAPSHOT,
		PersistenceError::StaleGeneration => STATUS_STALE_GENERATION,
		PersistenceError::GenerationExhausted => STATUS_GENERATION_EXHAUSTED,
		PersistenceError::Encoding => STATUS_ENCODING,
		PersistenceError::OutputEncoding => STATUS_OUTPUT_ENCODING,
		PersistenceError::Initialization => STATUS_INITIALIZATION,
		PersistenceError::Digest => STATUS_DIGEST,
		PersistenceError::Poisoned => STATUS_POISONED,
		PersistenceError::Storage => STATUS_STORAGE,
		PersistenceError::CommitUnknown => STATUS_COMMIT_UNKNOWN,
	}
}

fn complete<T>(status: &Cell<u32>, result: Result<T, PersistenceError>) -> Option<T> {
	match result {
		Ok(value) => {
			status.set(STATUS_OK);
			Some(value)
		}
		Err(error) => {
			status.set(error_status(error));
			None
		}
	}
}

fn complete_operation<T>(
	status: &Cell<u32>,
	result: Result<Option<T>, PersistenceError>,
) -> Option<T> {
	let output = complete(status, result)?;
	if output.is_none() {
		status.set(STATUS_REJECTED);
	}
	output
}

fn set_status_out(status_out: *mut u32, status: u32) {
	if !status_out.is_null() {
		unsafe { *status_out = status };
	}
}

fn server_result(
	result: Result<PersistentServer<Box<dyn SnapshotStore>>, PersistenceError>,
	status_out: *mut u32,
) -> *mut Server {
	match result {
		Ok(server) => {
			set_status_out(status_out, STATUS_OK);
			Box::into_raw(Box::new(Server(
				Exclusive::new(server),
				Cell::new(STATUS_OK),
			)))
		}
		Err(error) => {
			set_status_out(status_out, error_status(error));
			std::ptr::null_mut()
		}
	}
}

fn callback_store(
	callbacks: SnapshotStoreCallbacksV2,
	status_out: *mut u32,
) -> Option<Box<dyn SnapshotStore>> {
	let store = CallbackStore {
		callbacks: callbacks.callbacks,
		last_error: callbacks.last_error,
	};
	if store.callbacks.load.is_none() || store.callbacks.compare_and_swap.is_none() {
		set_status_out(status_out, STATUS_INVALID_ARGUMENT);
		return None;
	}
	Some(Box::new(store))
}

/// Heap-allocated byte buffer returned by the C API.
///
/// A buffer with a non-null `ptr` must be released exactly once with `beaconcrypt_free_buffer`. A null `ptr` indicates either empty output or failure, depending on the called function. Where a function distinguishes absence from a present empty value, the present empty value is a non-null buffer with zero `len`; it owns a real allocation and is released like any other buffer. No buffer, and no byte pointer passed to a callback, carries a dangling address: a zero-length callback slice is null or points to a valid static byte, which must not be read or written.
#[repr(C)]
pub struct Buffer {
	/// Pointer to the first byte, null for no output, or a valid allocation when a present value is empty.
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

/// No send key was consumed and no output is available.
pub const SEND_OUTCOME_REJECTED: u32 = 0;
/// A send key was consumed and the message contains the successful output.
pub const SEND_OUTCOME_SENT: u32 = 1;
/// A send key was consumed, but no output could be constructed.
pub const SEND_OUTCOME_CONSUMED_WITHOUT_OUTPUT: u32 = 2;

/// Explicit send effect. Inspect `status` first; `outcome` is meaningful only for STATUS_OK. Only SEND_OUTCOME_SENT contains buffers and metadata. Release both message buffers with `beaconcrypt_free_buffer`. A persistent successful outcome is published only after its state commits; persistence errors suppress the outcome and output.
#[repr(C)]
pub struct SendResult {
	pub status: u32,
	pub outcome: u32,
	pub message: EncryptState,
}

pub(crate) fn failed_send_result(status: u32) -> SendResult {
	SendResult {
		status,
		outcome: SEND_OUTCOME_REJECTED,
		message: empty_encrypt_state(),
	}
}

pub(crate) fn send_result<T>(
	outcome: SendOutcome<T>,
	sent: impl FnOnce(T) -> EncryptState,
) -> SendResult {
	match outcome {
		SendOutcome::Rejected => failed_send_result(STATUS_OK),
		SendOutcome::ConsumedWithoutOutput => SendResult {
			status: STATUS_OK,
			outcome: SEND_OUTCOME_CONSUMED_WITHOUT_OUTPUT,
			message: empty_encrypt_state(),
		},
		SendOutcome::Sent(value) => SendResult {
			status: STATUS_OK,
			outcome: SEND_OUTCOME_SENT,
			message: sent(value),
		},
	}
}

pub(crate) fn encrypted_state(value: crate::Encrypted) -> EncryptState {
	EncryptState {
		data: into_buffer(value.ciphertext),
		state: empty_buffer(),
		key_id: value.key_id,
		seq: value.seq,
	}
}

fn outcome_update(value: SendState) -> EncryptState {
	EncryptState {
		data: into_buffer(value.data),
		state: into_buffer(value.state.as_str().as_bytes().to_vec()),
		key_id: value.kid,
		seq: value.seq,
	}
}

pub(crate) fn empty_buffer() -> Buffer {
	Buffer {
		ptr: std::ptr::null_mut(),
		len: 0,
		cap: 0,
	}
}

// Rust represents empty slices and unallocated vectors with a dangling address such as 0x1.
// Foreign runtimes may treat such a value in a pointer-typed slot as corruption (Go aborts
// when it copies a stack holding one), so no dangling address may cross this ABI.
static EMPTY_BYTES: u8 = 0;

/// The address passed to foreign callbacks for `bytes`: a valid static address when empty.
pub(crate) fn abi_ptr(bytes: &[u8]) -> *const u8 {
	if bytes.is_empty() {
		&raw const EMPTY_BYTES
	} else {
		bytes.as_ptr()
	}
}

pub(crate) fn into_buffer(mut data: Vec<u8>) -> Buffer {
	// A present empty buffer owns a real allocation, so its non-null pointer stays freeable.
	if data.capacity() == 0 {
		data.reserve_exact(1);
	}
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

// Required inputs reject null, empty and lengths that no Rust slice can have.
unsafe fn input<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
	if ptr.is_null() || len == 0 || len > isize::MAX as usize {
		None
	} else {
		Some(unsafe { slice::from_raw_parts(ptr, len) })
	}
}

// A null or zero-length seed selects generation; an impossible length is invalid, not absent.
unsafe fn seed_input<'a>(ptr: *const u8, len: usize) -> Result<Option<&'a [u8]>, ()> {
	if len > isize::MAX as usize {
		return Err(());
	}
	Ok(unsafe { input(ptr, len) })
}

// Optional values preserve presence even when the provided slice is empty.
unsafe fn optional_input<'a>(ptr: *const u8, len: usize) -> Result<Option<&'a [u8]>, ()> {
	if len > isize::MAX as usize || (ptr.is_null() && len != 0) {
		return Err(());
	}
	if ptr.is_null() {
		Ok(None)
	} else {
		Ok(Some(unsafe { slice::from_raw_parts(ptr, len) }))
	}
}

unsafe fn send_input<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
	unsafe { optional_input(ptr, len) }
		.ok()
		.map(|input| input.unwrap_or(&[]))
}

/// Release a byte buffer returned by this API.
///
/// Passing an empty buffer is allowed. The buffer and its pointer must not be used after this call.
/// The complete allocation is wiped before release. Copies retained by the caller are not erased.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_free_buffer(buffer: Buffer) {
	if !buffer.ptr.is_null() {
		let mut bytes = unsafe { Vec::from_raw_parts(buffer.ptr, buffer.len, buffer.cap) };
		bytes.zeroize();
	}
}

/// Create a server with independently generated Ed25519 and ML-DSA-65 identity keys.
///
/// Returns an owned handle, or null on failure. Release a non-null handle with `beaconcrypt_server_free`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new(server_kid: u64) -> *mut Server {
	server_result(
		PersistentServer::create(
			server_kid,
			None,
			None,
			Box::<BindingSnapshotStore>::default(),
		),
		std::ptr::null_mut(),
	)
}

/// Create a server with independent optional Ed25519 and ML-DSA-65 identity seeds.
///
/// Each null pointer or zero length selects an independently generated identity key. Each non-empty seed must contain exactly 32 readable secret bytes.
///
/// Returns an owned handle, or null when creation fails. Release a non-null handle with `beaconcrypt_server_free`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_new_from_seed(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
	mldsa_seed_ptr: *const u8,
	mldsa_seed_len: usize,
) -> *mut Server {
	let (Ok(seed), Ok(mldsa_seed)) = (unsafe {
		(
			seed_input(seed_ptr, seed_len),
			seed_input(mldsa_seed_ptr, mldsa_seed_len),
		)
	}) else {
		return std::ptr::null_mut();
	};
	server_result(
		PersistentServer::create(
			server_kid,
			seed,
			mldsa_seed,
			Box::<BindingSnapshotStore>::default(),
		),
		std::ptr::null_mut(),
	)
}

/// Create a server whose results are released only after the store's durable compare-and-swap succeeds.
///
/// The callbacks take ownership of their context even when construction fails. Each null seed or zero seed length selects an independently generated identity. `status_out` may be null; otherwise it receives a `beaconcrypt_STATUS_*` code. Returns null on failure.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_create_with_store(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
	mldsa_seed_ptr: *const u8,
	mldsa_seed_len: usize,
	callbacks: SnapshotStoreCallbacks,
	status_out: *mut u32,
) -> *mut Server {
	beaconcrypt_server_create_with_store_v2(
		server_kid,
		seed_ptr,
		seed_len,
		mldsa_seed_ptr,
		mldsa_seed_len,
		SnapshotStoreCallbacksV2 {
			callbacks,
			last_error: None,
		},
		status_out,
	)
}

/// Versioned durable constructor with explicit callback storage-error reporting.
///
/// Context ownership and callback lifetime rules match the corresponding legacy constructor.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_create_with_store_v2(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
	mldsa_seed_ptr: *const u8,
	mldsa_seed_len: usize,
	callbacks: SnapshotStoreCallbacksV2,
	status_out: *mut u32,
) -> *mut Server {
	let Some(store) = callback_store(callbacks, status_out) else {
		return std::ptr::null_mut();
	};
	let (Ok(seed), Ok(mldsa_seed)) = (unsafe {
		(
			seed_input(seed_ptr, seed_len),
			seed_input(mldsa_seed_ptr, mldsa_seed_len),
		)
	}) else {
		set_status_out(status_out, STATUS_INVALID_ARGUMENT);
		return std::ptr::null_mut();
	};
	server_result(
		PersistentServer::create(server_kid, seed, mldsa_seed, store),
		status_out,
	)
}

/// Create a durable server under a caller-provisioned 32-byte lineage.
///
/// Allocate each lineage to exactly one rollback-resistant authoritative store head. Callback context ownership and `status_out` follow `beaconcrypt_server_create_with_store`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_create_with_store_and_lineage(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
	mldsa_seed_ptr: *const u8,
	mldsa_seed_len: usize,
	callbacks: SnapshotStoreCallbacks,
	lineage_ptr: *const u8,
	lineage_len: usize,
	status_out: *mut u32,
) -> *mut Server {
	beaconcrypt_server_create_with_store_and_lineage_v2(
		server_kid,
		seed_ptr,
		seed_len,
		mldsa_seed_ptr,
		mldsa_seed_len,
		SnapshotStoreCallbacksV2 {
			callbacks,
			last_error: None,
		},
		lineage_ptr,
		lineage_len,
		status_out,
	)
}

/// Versioned durable constructor with explicit callback storage-error reporting.
///
/// Context ownership and callback lifetime rules match the corresponding legacy constructor.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_create_with_store_and_lineage_v2(
	server_kid: u64,
	seed_ptr: *const u8,
	seed_len: usize,
	mldsa_seed_ptr: *const u8,
	mldsa_seed_len: usize,
	callbacks: SnapshotStoreCallbacksV2,
	lineage_ptr: *const u8,
	lineage_len: usize,
	status_out: *mut u32,
) -> *mut Server {
	let Some(store) = callback_store(callbacks, status_out) else {
		return std::ptr::null_mut();
	};
	let Some(lineage) = (unsafe { input(lineage_ptr, lineage_len) })
		.and_then(|bytes| <[u8; 32]>::try_from(bytes).ok())
	else {
		set_status_out(status_out, STATUS_INVALID_ARGUMENT);
		return std::ptr::null_mut();
	};
	let (Ok(seed), Ok(mldsa_seed)) = (unsafe {
		(
			seed_input(seed_ptr, seed_len),
			seed_input(mldsa_seed_ptr, mldsa_seed_len),
		)
	}) else {
		set_status_out(status_out, STATUS_INVALID_ARGUMENT);
		return std::ptr::null_mut();
	};
	server_result(
		PersistentServer::create_with_lineage(
			server_kid,
			seed,
			mldsa_seed,
			store,
			SnapshotLineage::from_bytes(lineage),
		),
		status_out,
	)
}

/// Restore the trusted current snapshot and durably claim its next generation before returning a live owner.
///
/// Callback context ownership and `status_out` follow `beaconcrypt_server_create_with_store`. The store must protect snapshot integrity, provenance and freshness and coordinate concurrent owners.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_restore_with_store(
	callbacks: SnapshotStoreCallbacks,
	status_out: *mut u32,
) -> *mut Server {
	beaconcrypt_server_restore_with_store_v2(
		SnapshotStoreCallbacksV2 {
			callbacks,
			last_error: None,
		},
		status_out,
	)
}

/// Versioned durable constructor with explicit callback storage-error reporting.
///
/// Context ownership and callback lifetime rules match the corresponding legacy constructor.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_restore_with_store_v2(
	callbacks: SnapshotStoreCallbacksV2,
	status_out: *mut u32,
) -> *mut Server {
	let Some(store) = callback_store(callbacks, status_out) else {
		return std::ptr::null_mut();
	};
	server_result(PersistentServer::restore(store), status_out)
}

/// Read the owner's current non-secret snapshot head. Returns a status code without changing the last operation's status.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_head(
	handle: *const Server,
	out: *mut SnapshotHeadInfo,
) -> u32 {
	if handle.is_null() || out.is_null() {
		return STATUS_INVALID_ARGUMENT;
	}
	let Some(owner) = (unsafe { &*handle }).0.enter() else {
		return STATUS_INVALID_ARGUMENT;
	};
	unsafe { *out = owner.head().into() };
	STATUS_OK
}

/// Query whether a failed commit has fenced this owner. Returns false for null, true while a reentrant callback queries an in-progress operation, and preserves the last operation's status.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_is_poisoned(handle: *const Server) -> bool {
	if handle.is_null() {
		return false;
	}
	// An in-progress operation has already fenced the owner until its commit succeeds.
	(unsafe { &*handle })
		.0
		.enter()
		.is_none_or(|owner| owner.is_poisoned())
}

/// Return the last server operation's status, or `beaconcrypt_STATUS_INVALID_ARGUMENT` for null.
/// Head, identity and poison-state queries preserve this value; checkpoint export records its own status.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_last_status(handle: *const Server) -> u32 {
	if handle.is_null() {
		return STATUS_INVALID_ARGUMENT;
	}
	unsafe { (&*handle).1.get() }
}

/// Parse a snapshot envelope and compute its exact-byte head. This does not authenticate bytes or establish freshness.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_snapshot_head(
	bytes: *const u8,
	len: usize,
	out: *mut SnapshotHeadInfo,
) -> u32 {
	snapshot_head_result(bytes, len, out, |snapshot| snapshot.head())
}

/// Check a snapshot's lineage, next generation and exact parent digest against `expected` (null for an empty store).
///
/// This does not authenticate bytes or make the store atomic. A store must perform this check together with comparison against its trusted current head inside its durable compare-and-swap transaction.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_snapshot_validate_successor(
	bytes: *const u8,
	len: usize,
	expected: *const SnapshotHeadInfo,
	out: *mut SnapshotHeadInfo,
) -> u32 {
	let expected = if expected.is_null() {
		None
	} else {
		Some(SnapshotHead::from(unsafe { *expected }))
	};
	snapshot_head_result(bytes, len, out, |snapshot| {
		snapshot.validate_successor(expected.as_ref())
	})
}

fn snapshot_head_result(
	bytes: *const u8,
	len: usize,
	out: *mut SnapshotHeadInfo,
	operation: impl FnOnce(&ServerSnapshot) -> Result<SnapshotHead, PersistenceError>,
) -> u32 {
	if out.is_null() {
		return STATUS_INVALID_ARGUMENT;
	}
	let Some(bytes) = (unsafe { input(bytes, len) }) else {
		return STATUS_INVALID_ARGUMENT;
	};
	match operation(&ServerSnapshot::from_bytes(bytes.to_vec())) {
		Ok(head) => {
			unsafe { *out = head.into() };
			STATUS_OK
		}
		Err(error) => error_status(error),
	}
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
	let Ok(store) = BindingSnapshotStore::from_bytes(state.to_vec()) else {
		return std::ptr::null_mut();
	};
	server_result(
		PersistentServer::restore(Box::new(store) as Box<dyn SnapshotStore>),
		std::ptr::null_mut(),
	)
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
	let Some(owner) = provider.0.enter() else {
		provider.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	complete(&provider.1, owner.snapshot())
		.map(|snapshot| into_buffer(snapshot.as_bytes().to_vec()))
		.unwrap_or_else(empty_buffer)
}

/// Create a beacon bound to both server identity public keys.
///
/// `server_pk_ptr` must point to an Ed25519 public key, and `server_mldsa_pk_ptr` must point to an ML-DSA-65 public key of `beaconcrypt_MLDSA_PUBLIC_KEY_LEN` bytes. Both pins are mandatory.
///
/// Returns an owned handle, or null for absent or incorrectly sized input or a reported initialization/key-generation failure. Release a non-null handle with `beaconcrypt_beacon_free`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_beacon_new(
	server_kid: u64,
	server_pk_ptr: *const u8,
	server_pk_len: usize,
	server_mldsa_pk_ptr: *const u8,
	server_mldsa_pk_len: usize,
) -> *mut Beacon {
	let Some(server_pk) = (unsafe { input(server_pk_ptr, server_pk_len) }) else {
		return std::ptr::null_mut();
	};
	let Some(server_mldsa_pk) = (unsafe { input(server_mldsa_pk_ptr, server_mldsa_pk_len) }) else {
		return std::ptr::null_mut();
	};
	Beacon::try_new(server_kid, server_pk, server_mldsa_pk)
		.map(|beacon| Box::into_raw(Box::new(beacon)))
		.unwrap_or(std::ptr::null_mut())
}

/// Release a server handle created by this API.
///
/// Passing null is allowed. The handle must not be used after this call. A call made from one of the handle's own callbacks is ignored, because the active operation still owns the server.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_free(handle: *mut Server) {
	if !handle.is_null() && !(unsafe { &*handle }).0.is_busy() {
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
	let Some(owner) = (unsafe { &*handle }).0.enter() else {
		return empty_buffer();
	};
	into_buffer(owner.identity_pk().as_ref().to_vec())
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

/// Copy the server's ML-DSA-65 public key into a caller-owned buffer.
/// Returns an empty buffer for a null handle and preserves the last operation's status.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_server_mldsa_public_key(handle: *const Server) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let Some(owner) = (unsafe { &*handle }).0.enter() else {
		return empty_buffer();
	};
	into_buffer(owner.mldsa_public_key().to_vec())
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
/// A null `msg_ptr` with zero length omits the initial message. A non-null pointer with zero length explicitly supplies an empty message: acceptance consumes its replay marker, then response construction rejects it. A null pointer with nonzero length is invalid before acceptance. On failure, returns an empty response with key identifier zero.
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Some(registration) = (unsafe { input(reg_ptr, reg_len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Ok(message) = (unsafe { optional_input(msg_ptr, msg_len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Some(secret) = complete_operation(&server.1, owner.get_shared_secret(registration)) else {
		return RegistrationResponse {
			response: empty_buffer(),
			key_id: 0,
		};
	};
	let Some(response) = complete_operation(
		&server.1,
		owner.build_registration_response(secret, message),
	) else {
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

/// Encrypt a server-to-beacon message and report its exact send effect. Empty plaintext is an unchanged rejection. Invalid pointers or handles report STATUS_INVALID_ARGUMENT. A storage error reports no outcome; confirmed persistent outcomes are released only after commit.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_to_beacon_outcome(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> SendResult {
	let Some(server) = (unsafe { handle.as_ref() }) else {
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(data) = (unsafe { send_input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	match owner.encrypt_message_outcome(data, key_id) {
		Ok(outcome) => {
			server.1.set(STATUS_OK);
			send_result(outcome, encrypted_state)
		}
		Err(error) => {
			let status = error_status(error);
			server.1.set(status);
			failed_send_result(status)
		}
	}
}

/// Encrypt a server-to-beacon message with observational metadata and an explicit send effect. Empty plaintext is an unchanged rejection. Free both successful buffers with `beaconcrypt_free_buffer`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_and_update_outcome(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> SendResult {
	let Some(server) = (unsafe { handle.as_ref() }) else {
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(data) = (unsafe { send_input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	match owner.encrypt_and_update_outcome(data, key_id) {
		Ok(outcome) => {
			server.1.set(STATUS_OK);
			send_result(outcome, outcome_update)
		}
		Err(error) => {
			let status = error_status(error);
			server.1.set(status);
			failed_send_result(status)
		}
	}
}

/// Encrypt with an explicit send effect and successful JSON in message.data. message.state is empty; metadata is valid only for SEND_OUTCOME_SENT. Free successful data with `beaconcrypt_free_buffer`.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_and_update_json_outcome(
	handle: *mut Server,
	key_id: u64,
	ptr: *const u8,
	len: usize,
) -> SendResult {
	let Some(server) = (unsafe { handle.as_ref() }) else {
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(data) = (unsafe { send_input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	match owner.encrypt_and_update_json_outcome(data, key_id) {
		Ok(outcome) => {
			server.1.set(STATUS_OK);
			let sequence = owner
				.ratchet_status(key_id)
				.map_or(0, |status| status.send_sequence());
			send_result(outcome, |json| EncryptState {
				data: into_buffer(json.into_bytes()),
				state: empty_buffer(),
				key_id,
				seq: sequence,
			})
		}
		Err(error) => {
			let status = error_status(error);
			server.1.set(status);
			failed_send_result(status)
		}
	}
}

/// Encrypt a beacon-to-server message with an explicit send effect. Empty plaintext is an unchanged rejection; invalid pointers or handles report STATUS_INVALID_ARGUMENT. Only SEND_OUTCOME_SENT contains output and metadata.
#[unsafe(no_mangle)]
pub extern "C" fn beaconcrypt_encrypt_to_server_outcome(
	handle: *mut Beacon,
	ptr: *const u8,
	len: usize,
) -> SendResult {
	let Some(beacon) = (unsafe { handle.as_mut() }) else {
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	let Some(data) = (unsafe { send_input(ptr, len) }) else {
		return failed_send_result(STATUS_INVALID_ARGUMENT);
	};
	send_result(beacon.encrypt_message_outcome(data), encrypted_state)
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_encrypt_state();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_encrypt_state();
	};
	complete_operation(&server.1, owner.encrypt_and_update(data, key_id))
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	complete_operation(&server.1, owner.encrypt_and_update_json(data, key_id))
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_encrypt_state();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_encrypt_state();
	};
	complete_operation(&server.1, owner.decrypt_and_update(data))
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	complete_operation(&server.1, owner.decrypt_and_update_json(data))
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
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	complete_operation(&server.1, owner.encrypt_message(data, key_id))
		.map(|encrypted| into_buffer(encrypted.ciphertext))
		.unwrap_or_else(empty_buffer)
}

fn decrypt(handle: *mut Server, ptr: *const u8, len: usize) -> Buffer {
	if handle.is_null() {
		return empty_buffer();
	}
	let server = unsafe { &*handle };
	let Some(mut owner) = server.0.enter() else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	let Some(data) = (unsafe { input(ptr, len) }) else {
		server.1.set(STATUS_INVALID_ARGUMENT);
		return empty_buffer();
	};
	complete_operation(&server.1, owner.decrypt_message(data))
		.map(|decrypted| into_buffer(decrypted.plaintext))
		.unwrap_or_else(empty_buffer)
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::sync::{
		Arc, Barrier, Mutex,
		atomic::{AtomicUsize, Ordering},
	};

	#[derive(Default)]
	struct StoreState {
		bytes: Option<Vec<u8>>,
		head: Option<SnapshotHeadInfo>,
		attempts: usize,
		fail_next: bool,
		error_status: u32,
		post_commit_status: u32,
		// Address of a handle that the CAS callback reenters, and the refusals it observed.
		reenter: usize,
		refused_reentries: Vec<bool>,
	}

	// Every entry point must refuse a call made from its own handle's callback without touching it.
	fn reenter_own_handle(handle: *mut Server) -> bool {
		let mut head = SnapshotHeadInfo {
			lineage: [0; 32],
			generation: 0,
			digest: [0; 32],
		};
		let head_refused = beaconcrypt_server_head(handle, &mut head) == STATUS_INVALID_ARGUMENT;
		let poisoned = beaconcrypt_server_is_poisoned(handle);
		let identity_refused = beaconcrypt_server_identity_pk(handle).ptr.is_null()
			&& beaconcrypt_server_mldsa_public_key(handle).ptr.is_null()
			&& beaconcrypt_server_export_state(handle).ptr.is_null();
		let send_refused = beaconcrypt_encrypt_to_beacon(handle, 20, b"x".as_ptr(), 1)
			.ptr
			.is_null()
			&& beaconcrypt_server_last_status(handle) == STATUS_INVALID_ARGUMENT;
		let outcome = beaconcrypt_encrypt_to_beacon_outcome(handle, 20, b"x".as_ptr(), 1);
		let registration =
			beaconcrypt_register_beacon(handle, b"x".as_ptr(), 1, std::ptr::null(), 0);
		// A reentrant free is ignored; the outer call below must still find its server.
		beaconcrypt_server_free(handle);
		head_refused
			&& poisoned
			&& identity_refused
			&& send_refused
			&& outcome.status == STATUS_INVALID_ARGUMENT
			&& registration.response.ptr.is_null()
	}

	#[derive(Clone, Copy, Default)]
	enum LoadMode {
		#[default]
		Normal,
		MissingSink,
		Null,
		Empty,
		Multiple,
		FalseAfterSink,
		Oversized,
	}

	struct StoreContext {
		state: Arc<Mutex<StoreState>>,
		destroyed: Arc<AtomicUsize>,
		mode: LoadMode,
		load_barrier: Option<Arc<Barrier>>,
	}

	unsafe extern "C" fn load_callback(
		context: *mut c_void,
		sink_context: *mut c_void,
		sink: unsafe extern "C" fn(*mut c_void, *const u8, usize),
	) -> bool {
		let context = unsafe { &*context.cast::<StoreContext>() };
		if context.state.lock().unwrap().error_status != STATUS_OK {
			return false;
		}
		let bytes = context.state.lock().unwrap().bytes.clone();
		if let Some(barrier) = &context.load_barrier {
			barrier.wait();
		}
		let Some(bytes) = bytes else {
			return false;
		};
		unsafe {
			match context.mode {
				LoadMode::Normal => sink(sink_context, bytes.as_ptr(), bytes.len()),
				LoadMode::MissingSink => {}
				LoadMode::Null => sink(sink_context, std::ptr::null(), bytes.len()),
				LoadMode::Empty => sink(sink_context, bytes.as_ptr(), 0),
				LoadMode::Multiple => {
					sink(sink_context, bytes.as_ptr(), bytes.len());
					sink(sink_context, bytes.as_ptr(), bytes.len());
				}
				LoadMode::FalseAfterSink => {
					sink(sink_context, bytes.as_ptr(), bytes.len());
					return false;
				}
				LoadMode::Oversized => sink(sink_context, bytes.as_ptr(), isize::MAX as usize + 1),
			}
		}
		true
	}

	unsafe extern "C" fn cas_callback(
		context: *mut c_void,
		expected: *const SnapshotHeadInfo,
		bytes: *const u8,
		len: usize,
	) -> bool {
		let context = unsafe { &*context.cast::<StoreContext>() };
		let reenter = context.state.lock().unwrap().reenter;
		if reenter != 0 {
			let refused = reenter_own_handle(std::ptr::with_exposed_provenance_mut(reenter));
			context
				.state
				.lock()
				.unwrap()
				.refused_reentries
				.push(refused);
		}
		let mut store = context.state.lock().unwrap();
		store.attempts += 1;
		if store.error_status != STATUS_OK {
			return false;
		}
		if store.fail_next {
			store.fail_next = false;
			return false;
		}
		let expected_value = if expected.is_null() {
			None
		} else {
			Some(unsafe { *expected })
		};
		if store.head != expected_value {
			return false;
		}
		let mut head = SnapshotHeadInfo {
			lineage: [0; 32],
			generation: 0,
			digest: [0; 32],
		};
		if beaconcrypt_snapshot_validate_successor(bytes, len, expected, &mut head) != STATUS_OK {
			return false;
		}
		store.bytes = Some(unsafe { slice::from_raw_parts(bytes, len) }.to_vec());
		store.head = Some(head);
		if store.post_commit_status != STATUS_OK {
			store.error_status = mem::take(&mut store.post_commit_status);
			return false;
		}
		true
	}

	unsafe extern "C" fn destroy_callback(context: *mut c_void) {
		let context = unsafe { Box::from_raw(context.cast::<StoreContext>()) };
		context.destroyed.fetch_add(1, Ordering::SeqCst);
	}

	unsafe extern "C" fn last_error_callback(context: *mut c_void) -> u32 {
		let context = unsafe { &*context.cast::<StoreContext>() };
		context.state.lock().unwrap().error_status
	}

	fn callbacks(
		state: &Arc<Mutex<StoreState>>,
		destroyed: &Arc<AtomicUsize>,
		mode: LoadMode,
	) -> SnapshotStoreCallbacks {
		context_callbacks(StoreContext {
			state: Arc::clone(state),
			destroyed: Arc::clone(destroyed),
			mode,
			load_barrier: None,
		})
	}

	fn context_callbacks(context: StoreContext) -> SnapshotStoreCallbacks {
		SnapshotStoreCallbacks {
			context: Box::into_raw(Box::new(context)).cast(),
			load: Some(load_callback),
			compare_and_swap: Some(cas_callback),
			destroy: Some(destroy_callback),
		}
	}

	fn callbacks_v2(
		state: &Arc<Mutex<StoreState>>,
		destroyed: &Arc<AtomicUsize>,
	) -> SnapshotStoreCallbacksV2 {
		SnapshotStoreCallbacksV2 {
			callbacks: callbacks(state, destroyed, LoadMode::Normal),
			last_error: Some(last_error_callback),
		}
	}

	#[test]
	fn legacy_snapshot_callback_layout_remains_four_pointers() {
		let pointer = mem::size_of::<*mut c_void>();
		assert_eq!(mem::size_of::<SnapshotStoreCallbacks>(), pointer * 4);
		assert_eq!(
			mem::align_of::<SnapshotStoreCallbacks>(),
			mem::align_of::<*mut c_void>()
		);
		assert_eq!(mem::offset_of!(SnapshotStoreCallbacks, context), 0);
		assert_eq!(mem::offset_of!(SnapshotStoreCallbacks, load), pointer);
		assert_eq!(
			mem::offset_of!(SnapshotStoreCallbacks, compare_and_swap),
			pointer * 2
		);
		assert_eq!(
			mem::offset_of!(SnapshotStoreCallbacks, destroy),
			pointer * 3
		);
		assert_eq!(mem::offset_of!(SnapshotStoreCallbacksV2, callbacks), 0);
		assert_eq!(
			mem::offset_of!(SnapshotStoreCallbacksV2, last_error),
			pointer * 4
		);
	}

	#[test]
	fn versioned_callbacks_report_constructor_errors_and_release_contexts() {
		for error in [STATUS_STORAGE, STATUS_COMMIT_UNKNOWN] {
			let state = Arc::new(Mutex::new(StoreState {
				error_status: error,
				..StoreState::default()
			}));
			let destroyed = Arc::new(AtomicUsize::new(0));
			let mut status = u32::MAX;
			let server = beaconcrypt_server_create_with_store_v2(
				19,
				[7; 32].as_ptr(),
				32,
				[8; 32].as_ptr(),
				32,
				callbacks_v2(&state, &destroyed),
				&mut status,
			);
			assert!(server.is_null());
			assert_eq!(status, error);
			assert_eq!(destroyed.load(Ordering::SeqCst), 1);
			let server = beaconcrypt_server_create_with_store_and_lineage_v2(
				19,
				[7; 32].as_ptr(),
				32,
				[8; 32].as_ptr(),
				32,
				callbacks_v2(&state, &destroyed),
				[9; 32].as_ptr(),
				32,
				&mut status,
			);
			assert!(server.is_null());
			assert_eq!(status, error);
			assert_eq!(destroyed.load(Ordering::SeqCst), 2);
			let server = beaconcrypt_server_restore_with_store_v2(
				callbacks_v2(&state, &destroyed),
				&mut status,
			);
			assert!(server.is_null());
			assert_eq!(status, error);
			assert_eq!(destroyed.load(Ordering::SeqCst), 3);
		}
	}

	#[test]
	fn callback_errors_are_distinct_from_absence_and_conflict() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let callbacks = callbacks(&state, &destroyed, LoadMode::Normal);
		let mut store = CallbackStore {
			callbacks,
			last_error: Some(last_error_callback),
		};
		assert!(store.load().unwrap().is_none());
		let invalid = ServerSnapshot::from_bytes(Vec::new());
		assert!(!store.compare_and_swap(None, &invalid).unwrap());
		state.lock().unwrap().error_status = STATUS_STORAGE;
		assert!(matches!(store.load(), Err(PersistenceError::Storage)));
		assert_eq!(
			store.compare_and_swap(None, &invalid),
			Err(PersistenceError::Storage)
		);
		state.lock().unwrap().error_status = STATUS_COMMIT_UNKNOWN;
		assert_eq!(
			store.compare_and_swap(None, &invalid),
			Err(PersistenceError::CommitUnknown)
		);
		state.lock().unwrap().error_status = STATUS_OK;
		assert!(store.load().unwrap().is_none());
		drop(store);
		assert_eq!(destroyed.load(Ordering::SeqCst), 1);
	}

	struct OwnedServer(*mut Server);

	impl Drop for OwnedServer {
		fn drop(&mut self) {
			beaconcrypt_server_free(self.0);
		}
	}

	impl OwnedServer {
		fn head(&self) -> SnapshotHeadInfo {
			let mut head = SnapshotHeadInfo {
				lineage: [0; 32],
				generation: 0,
				digest: [0; 32],
			};
			assert_eq!(beaconcrypt_server_head(self.0, &mut head), STATUS_OK);
			head
		}
	}

	fn create_durable(state: &Arc<Mutex<StoreState>>, destroyed: &Arc<AtomicUsize>) -> OwnedServer {
		let mut status = u32::MAX;
		let server = beaconcrypt_server_create_with_store_and_lineage(
			19,
			[7; 32].as_ptr(),
			32,
			[8; 32].as_ptr(),
			32,
			callbacks(state, destroyed, LoadMode::Normal),
			[9; 32].as_ptr(),
			32,
			&mut status,
		);
		assert_eq!(status, STATUS_OK);
		assert!(!server.is_null());
		OwnedServer(server)
	}

	fn copy_buffer(buffer: Buffer) -> Vec<u8> {
		assert!(!buffer.ptr.is_null());
		let bytes = unsafe { slice::from_raw_parts(buffer.ptr, buffer.len) }.to_vec();
		beaconcrypt_free_buffer(buffer);
		bytes
	}

	fn register(server: &OwnedServer) -> (Beacon, u64) {
		let public_key = copy_buffer(beaconcrypt_server_identity_pk(server.0));
		let mldsa_key = copy_buffer(beaconcrypt_server_mldsa_public_key(server.0));
		let mut beacon = Beacon::new(19, &public_key, &mldsa_key);
		let registration = beacon.get_registration_bundle().unwrap();
		let response = beaconcrypt_register_beacon(
			server.0,
			registration.as_ptr(),
			registration.len(),
			b"hello".as_ptr(),
			5,
		);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_OK);
		let bytes = copy_buffer(response.response);
		assert_eq!(beacon.finish_registration(&bytes).unwrap(), b"hello");
		(beacon, response.key_id)
	}

	fn assert_no_send_output(result: &SendResult, status: u32, outcome: u32) {
		assert_eq!(result.status, status);
		assert_eq!(result.outcome, outcome);
		assert!(result.message.data.ptr.is_null());
		assert_eq!(result.message.data.len, 0);
		assert_eq!(result.message.data.cap, 0);
		assert!(result.message.state.ptr.is_null());
		assert_eq!(result.message.state.len, 0);
		assert_eq!(result.message.state.cap, 0);
		assert_eq!(result.message.key_id, 0);
		assert_eq!(result.message.seq, 0);
	}

	#[test]
	fn registration_preserves_optional_presence_and_validates_before_acceptance() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let public_key = copy_buffer(beaconcrypt_server_identity_pk(server.0));
		let mldsa_key = copy_buffer(beaconcrypt_server_mldsa_public_key(server.0));
		let mut beacon = Beacon::new(19, &public_key, &mldsa_key);
		let bundle = beacon.get_registration_bundle().unwrap();
		let before = server.head();
		for (ptr, len) in [
			(std::ptr::null(), 1),
			(b"".as_ptr(), isize::MAX as usize + 1),
		] {
			let response =
				beaconcrypt_register_beacon(server.0, bundle.as_ptr(), bundle.len(), ptr, len);
			assert!(response.response.ptr.is_null());
			assert_eq!(
				beaconcrypt_server_last_status(server.0),
				STATUS_INVALID_ARGUMENT
			);
			assert_eq!(server.head(), before);
		}
		let response = beaconcrypt_register_beacon(
			server.0,
			bundle.as_ptr(),
			bundle.len(),
			std::ptr::null(),
			0,
		);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_OK);
		assert_eq!(
			beacon
				.finish_registration(&copy_buffer(response.response))
				.unwrap(),
			[0xff]
		);
		assert_eq!(server.head().generation, before.generation + 2);

		let mut empty_beacon = Beacon::new(19, &public_key, &mldsa_key);
		let bundle = empty_beacon.get_registration_bundle().unwrap();
		let before = server.head();
		let response =
			beaconcrypt_register_beacon(server.0, bundle.as_ptr(), bundle.len(), b"".as_ptr(), 0);
		assert!(response.response.ptr.is_null());
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_REJECTED);
		assert_eq!(server.head().generation, before.generation + 1);
		let accepted = server.head();
		let response = beaconcrypt_register_beacon(
			server.0,
			bundle.as_ptr(),
			bundle.len(),
			b"retry".as_ptr(),
			5,
		);
		assert!(response.response.ptr.is_null());
		assert_eq!(server.head(), accepted);
	}

	#[test]
	fn send_outcome_abi_preserves_effects_metadata_and_storage_fencing() {
		type Send = extern "C" fn(*mut Server, u64, *const u8, usize) -> SendResult;
		let consumed =
			send_result::<()>(SendOutcome::ConsumedWithoutOutput, |_| panic!("no output"));
		assert_no_send_output(&consumed, STATUS_OK, SEND_OUTCOME_CONSUMED_WITHOUT_OUTPUT);
		for (mode, send) in [
			beaconcrypt_encrypt_to_beacon_outcome as Send,
			beaconcrypt_encrypt_and_update_outcome,
			beaconcrypt_encrypt_and_update_json_outcome,
		]
		.into_iter()
		.enumerate()
		{
			let state = Arc::new(Mutex::new(StoreState::default()));
			let destroyed = Arc::new(AtomicUsize::new(0));
			let server = create_durable(&state, &destroyed);
			let (mut beacon, kid) = register(&server);
			assert_no_send_output(
				&send(std::ptr::null_mut(), kid, b"x".as_ptr(), 1),
				STATUS_INVALID_ARGUMENT,
				SEND_OUTCOME_REJECTED,
			);
			assert_no_send_output(
				&send(server.0, kid, std::ptr::null(), 1),
				STATUS_INVALID_ARGUMENT,
				SEND_OUTCOME_REJECTED,
			);
			assert_eq!(
				beaconcrypt_server_last_status(server.0),
				STATUS_INVALID_ARGUMENT
			);
			let before = server.head();
			for (ptr, len, peer) in [
				(std::ptr::null(), 0, kid),
				(b"".as_ptr(), 0, kid),
				(b"x".as_ptr(), 1, u64::MAX),
			] {
				assert_no_send_output(
					&send(server.0, peer, ptr, len),
					STATUS_OK,
					SEND_OUTCOME_REJECTED,
				);
				assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_OK);
				assert_eq!(server.head(), before);
			}
			let result = send(server.0, kid, b"sent".as_ptr(), 4);
			assert_eq!(result.status, STATUS_OK);
			assert_eq!(result.outcome, SEND_OUTCOME_SENT);
			assert_eq!(result.message.key_id, kid);
			assert_eq!(result.message.seq, 2);
			assert_eq!(server.head().generation, before.generation + 1);
			let data = copy_buffer(result.message.data);
			let ciphertext = if mode == 2 {
				let json: serde_json::Value = serde_json::from_slice(&data).unwrap();
				assert_eq!(json["kid"], kid);
				assert_eq!(json["seq"], result.message.seq);
				serde_json::from_value::<Vec<u8>>(json["data"].clone()).unwrap()
			} else {
				data
			};
			assert_eq!(
				beacon.decrypt_message(&ciphertext).unwrap().plaintext,
				b"sent"
			);
			if mode == 1 {
				let state: serde_json::Value =
					serde_json::from_slice(&copy_buffer(result.message.state)).unwrap();
				assert!(state.get("send_key").is_some());
			} else {
				assert!(result.message.state.ptr.is_null());
			}
			state.lock().unwrap().fail_next = true;
			assert_no_send_output(
				&send(server.0, kid, b"withheld".as_ptr(), 8),
				STATUS_STALE_GENERATION,
				SEND_OUTCOME_REJECTED,
			);
			assert_eq!(
				beaconcrypt_server_last_status(server.0),
				STATUS_STALE_GENERATION
			);
			assert!(beaconcrypt_server_is_poisoned(server.0));
			assert_no_send_output(
				&send(server.0, kid, b"again".as_ptr(), 5),
				STATUS_POISONED,
				SEND_OUTCOME_REJECTED,
			);
			assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_POISONED);
		}
	}

	#[test]
	fn beacon_send_outcome_abi_reports_rejection_and_success() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let (mut beacon, _) = register(&server);
		assert_no_send_output(
			&beaconcrypt_encrypt_to_server_outcome(std::ptr::null_mut(), b"x".as_ptr(), 1),
			STATUS_INVALID_ARGUMENT,
			SEND_OUTCOME_REJECTED,
		);
		assert_no_send_output(
			&beaconcrypt_encrypt_to_server_outcome(&mut beacon, std::ptr::null(), 1),
			STATUS_INVALID_ARGUMENT,
			SEND_OUTCOME_REJECTED,
		);
		assert_no_send_output(
			&beaconcrypt_encrypt_to_server_outcome(&mut beacon, std::ptr::null(), 0),
			STATUS_OK,
			SEND_OUTCOME_REJECTED,
		);
		let result = beaconcrypt_encrypt_to_server_outcome(&mut beacon, b"beacon".as_ptr(), 6);
		assert_eq!(result.status, STATUS_OK);
		assert_eq!(result.outcome, SEND_OUTCOME_SENT);
		assert_eq!(result.message.key_id, 19);
		assert_eq!(result.message.seq, 1);
		assert!(result.message.state.ptr.is_null());
		let frame = copy_buffer(result.message.data);
		let plaintext = copy_buffer(beaconcrypt_decrypt_beacon_message(
			server.0,
			frame.as_ptr(),
			frame.len(),
		));
		assert_eq!(plaintext, b"beacon");
	}

	#[test]
	fn versioned_callbacks_fence_failed_receives_and_restore_confirmed_consumption() {
		for (error, published) in [
			(STATUS_STORAGE, false),
			(STATUS_COMMIT_UNKNOWN, false),
			(STATUS_COMMIT_UNKNOWN, true),
		] {
			let state = Arc::new(Mutex::new(StoreState::default()));
			let destroyed = Arc::new(AtomicUsize::new(0));
			let mut status = u32::MAX;
			let handle = beaconcrypt_server_create_with_store_and_lineage_v2(
				19,
				[7; 32].as_ptr(),
				32,
				[8; 32].as_ptr(),
				32,
				callbacks_v2(&state, &destroyed),
				[9; 32].as_ptr(),
				32,
				&mut status,
			);
			assert_eq!(status, STATUS_OK);
			assert!(!handle.is_null());
			let server = OwnedServer(handle);
			let (mut beacon, _) = register(&server);
			let before = server.head();
			let frame = beacon.encrypt_message(b"withheld plaintext").unwrap();
			{
				let mut stored = state.lock().unwrap();
				if published {
					stored.post_commit_status = error;
				} else {
					stored.error_status = error;
				}
			}
			let output = beaconcrypt_decrypt_beacon_message(server.0, frame.as_ptr(), frame.len());
			assert!(output.ptr.is_null());
			assert_eq!(output.len, 0);
			assert_eq!(beaconcrypt_server_last_status(server.0), error);
			assert!(beaconcrypt_server_is_poisoned(server.0));
			assert_eq!(server.head(), before);
			assert_eq!(
				state.lock().unwrap().head.unwrap().generation,
				before.generation + u64::from(published)
			);
			drop(server);
			assert_eq!(destroyed.load(Ordering::SeqCst), 1);
			state.lock().unwrap().error_status = STATUS_OK;
			let restored = beaconcrypt_server_restore_with_store_v2(
				callbacks_v2(&state, &destroyed),
				&mut status,
			);
			assert_eq!(status, STATUS_OK);
			assert!(!restored.is_null());
			let restored = OwnedServer(restored);
			let output =
				beaconcrypt_decrypt_beacon_message(restored.0, frame.as_ptr(), frame.len());
			if published {
				assert!(output.ptr.is_null());
				assert_eq!(beaconcrypt_server_last_status(restored.0), STATUS_REJECTED);
			} else {
				assert_eq!(copy_buffer(output), b"withheld plaintext");
				assert_eq!(beaconcrypt_server_last_status(restored.0), STATUS_OK);
			}
			drop(restored);
			assert_eq!(destroyed.load(Ordering::SeqCst), 2);
		}
	}

	#[test]
	fn c_durable_callbacks_commit_outputs_before_return_and_restore() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		assert_eq!(server.head().lineage, [9; 32]);
		assert_eq!(server.head().generation, 0);
		assert_eq!(state.lock().unwrap().head, Some(server.head()));
		assert_eq!(
			copy_buffer(beaconcrypt_server_mldsa_public_key(server.0)),
			crate::MldsaIdentity::from_seed([8; 32]).public_key()
		);
		let (mut beacon, kid) = register(&server);
		assert_eq!(server.head().generation, 2);
		assert_eq!(state.lock().unwrap().head, Some(server.head()));
		let ciphertext = copy_buffer(beaconcrypt_encrypt_to_beacon(
			server.0,
			kid,
			b"task".as_ptr(),
			4,
		));
		assert_eq!(server.head().generation, 3);
		assert_eq!(state.lock().unwrap().head, Some(server.head()));
		assert_eq!(
			beacon.decrypt_message(&ciphertext).unwrap().plaintext,
			b"task"
		);
		let inbound = beacon.encrypt_message(b"result").unwrap();
		let plaintext = copy_buffer(beaconcrypt_decrypt_beacon_message(
			server.0,
			inbound.as_ptr(),
			inbound.len(),
		));
		assert_eq!(plaintext, b"result");
		assert_eq!(server.head().generation, 4);
		assert_eq!(state.lock().unwrap().head, Some(server.head()));
		assert_eq!(
			copy_buffer(beaconcrypt_server_export_state(server.0)),
			state.lock().unwrap().bytes.clone().unwrap()
		);
		drop(server);
		assert_eq!(destroyed.load(Ordering::SeqCst), 1);
		let mut status = u32::MAX;
		let restored = OwnedServer(beaconcrypt_server_restore_with_store(
			callbacks(&state, &destroyed, LoadMode::Normal),
			&mut status,
		));
		assert_eq!(status, STATUS_OK);
		assert!(!restored.0.is_null());
		assert_eq!(restored.head().generation, 5);
		assert_eq!(state.lock().unwrap().head, Some(restored.head()));
		let inbound = beacon.encrypt_message(b"after restart").unwrap();
		assert_eq!(
			copy_buffer(beaconcrypt_decrypt_beacon_message(
				restored.0,
				inbound.as_ptr(),
				inbound.len()
			)),
			b"after restart"
		);
		drop(restored);
		assert_eq!(destroyed.load(Ordering::SeqCst), 2);
	}

	#[test]
	fn c_failed_send_and_receive_cas_suppress_outputs_and_poison() {
		for receive in [false, true] {
			let state = Arc::new(Mutex::new(StoreState::default()));
			let destroyed = Arc::new(AtomicUsize::new(0));
			let server = create_durable(&state, &destroyed);
			let (mut beacon, kid) = register(&server);
			let before = state.lock().unwrap().bytes.clone();
			state.lock().unwrap().fail_next = true;
			let result = if receive {
				let inbound = beacon.encrypt_message(b"suppressed receive").unwrap();
				beaconcrypt_decrypt_beacon_message(server.0, inbound.as_ptr(), inbound.len())
			} else {
				beaconcrypt_encrypt_to_beacon(server.0, kid, b"suppressed send".as_ptr(), 15)
			};
			assert!(result.ptr.is_null());
			assert_eq!(
				beaconcrypt_server_last_status(server.0),
				STATUS_STALE_GENERATION
			);
			assert!(beaconcrypt_server_is_poisoned(server.0));
			assert_eq!(server.head().generation, 2);
			beaconcrypt_free_buffer(beaconcrypt_server_identity_pk(server.0));
			beaconcrypt_free_buffer(beaconcrypt_server_mldsa_public_key(server.0));
			assert_eq!(
				beaconcrypt_server_last_status(server.0),
				STATUS_STALE_GENERATION
			);
			assert_eq!(state.lock().unwrap().bytes, before);
			assert!(
				beaconcrypt_encrypt_to_beacon(server.0, kid, b"retry".as_ptr(), 5)
					.ptr
					.is_null()
			);
			assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_POISONED);
		}
	}

	#[test]
	fn c_rejected_receive_skips_store_and_preserves_retry() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let (mut beacon, _) = register(&server);
		let inbound = beacon.encrypt_message(b"authentic").unwrap();
		let original = beaconcrypt_parse::decode_frame(inbound.as_ref()).unwrap();
		let mut payload = original.cipher_text.to_vec();
		*payload.last_mut().unwrap() ^= 1;
		let corrupted = crate::wire::encode_frame(beaconcrypt_parse::CryptoFrame {
			seq: original.seq,
			key_id: original.key_id,
			cipher_text: &payload,
		})
		.unwrap();
		let before = state.lock().unwrap().bytes.clone();
		let attempts = state.lock().unwrap().attempts;
		assert!(
			beaconcrypt_decrypt_beacon_message(server.0, corrupted.as_ptr(), corrupted.len())
				.ptr
				.is_null()
		);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_REJECTED);
		assert!(!beaconcrypt_server_is_poisoned(server.0));
		assert_eq!(server.head().generation, 2);
		assert_eq!(state.lock().unwrap().attempts, attempts);
		assert_eq!(state.lock().unwrap().bytes, before);
		assert_eq!(
			copy_buffer(beaconcrypt_decrypt_beacon_message(
				server.0,
				inbound.as_ptr(),
				inbound.len()
			)),
			b"authentic"
		);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_OK);
		assert!(
			beaconcrypt_decrypt_beacon_message(server.0, inbound.as_ptr(), inbound.len())
				.ptr
				.is_null()
		);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_REJECTED);
	}

	#[test]
	fn c_stale_owner_is_fenced_after_other_owner_restores() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let original = create_durable(&state, &destroyed);
		let (_, kid) = register(&original);
		let mut status = u32::MAX;
		let restored = OwnedServer(beaconcrypt_server_restore_with_store(
			callbacks(&state, &destroyed, LoadMode::Normal),
			&mut status,
		));
		assert_eq!(status, STATUS_OK);
		assert!(
			beaconcrypt_encrypt_to_beacon(original.0, kid, b"stale".as_ptr(), 5)
				.ptr
				.is_null()
		);
		assert_eq!(
			beaconcrypt_server_last_status(original.0),
			STATUS_STALE_GENERATION
		);
		assert!(beaconcrypt_server_is_poisoned(original.0));
		beaconcrypt_free_buffer(beaconcrypt_encrypt_to_beacon(
			restored.0,
			kid,
			b"current".as_ptr(),
			7,
		));
		assert_eq!(beaconcrypt_server_last_status(restored.0), STATUS_OK);
	}

	#[test]
	fn c_concurrent_restore_claims_one_authoritative_head() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		drop(create_durable(&state, &destroyed));
		let barrier = Arc::new(Barrier::new(2));
		let workers: Vec<_> = (0..2)
			.map(|_| {
				let state = Arc::clone(&state);
				let destroyed = Arc::clone(&destroyed);
				let barrier = Arc::clone(&barrier);
				std::thread::spawn(move || {
					let mut status = u32::MAX;
					let callbacks = context_callbacks(StoreContext {
						state,
						destroyed,
						mode: LoadMode::Normal,
						load_barrier: Some(barrier),
					});
					let server = OwnedServer(beaconcrypt_server_restore_with_store(
						callbacks,
						&mut status,
					));
					assert_eq!(server.0.is_null(), status != STATUS_OK);
					status
				})
			})
			.collect();
		let mut statuses: Vec<_> = workers
			.into_iter()
			.map(|worker| worker.join().unwrap())
			.collect();
		statuses.sort_unstable();
		assert_eq!(statuses, [STATUS_OK, STATUS_STALE_GENERATION]);
		assert_eq!(destroyed.load(Ordering::SeqCst), 3);
	}

	#[test]
	fn c_malformed_loads_and_constructor_failures_destroy_context_once() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let mut status = u32::MAX;
		assert!(
			beaconcrypt_server_restore_with_store(
				callbacks(&state, &destroyed, LoadMode::Normal),
				&mut status
			)
			.is_null()
		);
		assert_eq!(status, STATUS_MISSING_SNAPSHOT);
		assert_eq!(destroyed.load(Ordering::SeqCst), 1);
		drop(create_durable(&state, &destroyed));
		for (index, mode) in [
			LoadMode::MissingSink,
			LoadMode::Null,
			LoadMode::Empty,
			LoadMode::Multiple,
			LoadMode::FalseAfterSink,
			LoadMode::Oversized,
		]
		.into_iter()
		.enumerate()
		{
			assert!(
				beaconcrypt_server_restore_with_store(
					callbacks(&state, &destroyed, mode),
					&mut status
				)
				.is_null()
			);
			assert_eq!(status, STATUS_INVALID_SNAPSHOT);
			assert_eq!(destroyed.load(Ordering::SeqCst), 3 + index);
		}
		let mut invalid = callbacks(&state, &destroyed, LoadMode::Normal);
		invalid.load = None;
		assert!(beaconcrypt_server_restore_with_store(invalid, &mut status).is_null());
		assert_eq!(status, STATUS_INVALID_ARGUMENT);
		assert_eq!(destroyed.load(Ordering::SeqCst), 9);
		let invalid = callbacks(&state, &destroyed, LoadMode::Normal);
		assert!(
			beaconcrypt_server_create_with_store_and_lineage(
				19,
				std::ptr::null(),
				0,
				std::ptr::null(),
				0,
				invalid,
				[9; 31].as_ptr(),
				31,
				&mut status
			)
			.is_null()
		);
		assert_eq!(status, STATUS_INVALID_ARGUMENT);
		assert_eq!(destroyed.load(Ordering::SeqCst), 10);
		assert!(
			beaconcrypt_server_create_with_store(
				19,
				[7; 31].as_ptr(),
				31,
				std::ptr::null(),
				0,
				callbacks(&state, &destroyed, LoadMode::Normal),
				&mut status
			)
			.is_null()
		);
		assert_eq!(status, STATUS_INITIALIZATION);
		assert_eq!(destroyed.load(Ordering::SeqCst), 11);
	}

	#[test]
	fn c_store_owns_context_on_initial_cas_failure_and_optional_destroy() {
		let state = Arc::new(Mutex::new(StoreState {
			fail_next: true,
			..StoreState::default()
		}));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let mut status = u32::MAX;
		assert!(
			beaconcrypt_server_create_with_store(
				19,
				std::ptr::null(),
				0,
				std::ptr::null(),
				0,
				callbacks(&state, &destroyed, LoadMode::Normal),
				&mut status
			)
			.is_null()
		);
		assert_eq!(status, STATUS_STALE_GENERATION);
		assert_eq!(destroyed.load(Ordering::SeqCst), 1);
		assert!(state.lock().unwrap().bytes.is_none());
		let mut invalid = callbacks(&state, &destroyed, LoadMode::Normal);
		invalid.compare_and_swap = None;
		assert!(
			beaconcrypt_server_create_with_store(
				19,
				std::ptr::null(),
				0,
				std::ptr::null(),
				0,
				invalid,
				&mut status
			)
			.is_null()
		);
		assert_eq!(status, STATUS_INVALID_ARGUMENT);
		assert_eq!(destroyed.load(Ordering::SeqCst), 2);
		let mut borrowed = callbacks(&state, &destroyed, LoadMode::Normal);
		let context = borrowed.context;
		borrowed.destroy = None;
		let server = OwnedServer(beaconcrypt_server_create_with_store(
			19,
			std::ptr::null(),
			0,
			std::ptr::null(),
			0,
			borrowed,
			std::ptr::null_mut(),
		));
		assert!(!server.0.is_null());
		drop(server);
		assert_eq!(destroyed.load(Ordering::SeqCst), 2);
		unsafe { destroy_callback(context) };
		assert_eq!(destroyed.load(Ordering::SeqCst), 3);
	}

	#[test]
	fn c_snapshot_helpers_validate_parent_and_queries_preserve_status() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let initial = server.head();
		let bytes = state.lock().unwrap().bytes.clone().unwrap();
		let mut output = initial;
		assert_eq!(
			beaconcrypt_snapshot_head(bytes.as_ptr(), bytes.len(), &mut output),
			STATUS_OK
		);
		assert_eq!(output, initial);
		assert_eq!(
			beaconcrypt_snapshot_validate_successor(
				bytes.as_ptr(),
				bytes.len(),
				std::ptr::null(),
				&mut output
			),
			STATUS_OK
		);
		assert_eq!(
			beaconcrypt_snapshot_validate_successor(
				bytes.as_ptr(),
				bytes.len(),
				&initial,
				&mut output
			),
			STATUS_STALE_GENERATION
		);
		assert_eq!(
			beaconcrypt_snapshot_head(std::ptr::null(), 0, &mut output),
			STATUS_INVALID_ARGUMENT
		);
		assert_eq!(
			beaconcrypt_snapshot_head(b"bad".as_ptr(), 3, &mut output),
			STATUS_INVALID_SNAPSHOT
		);
		assert_eq!(
			beaconcrypt_snapshot_head(bytes.as_ptr(), bytes.len(), std::ptr::null_mut()),
			STATUS_INVALID_ARGUMENT
		);
		assert_eq!(
			beaconcrypt_server_head(std::ptr::null(), &mut output),
			STATUS_INVALID_ARGUMENT
		);
		assert_eq!(
			beaconcrypt_server_last_status(std::ptr::null()),
			STATUS_INVALID_ARGUMENT
		);
		assert!(!beaconcrypt_server_is_poisoned(std::ptr::null()));
		assert!(
			beaconcrypt_decrypt_beacon_message(server.0, std::ptr::null(), 0)
				.ptr
				.is_null()
		);
		assert_eq!(
			beaconcrypt_server_last_status(server.0),
			STATUS_INVALID_ARGUMENT
		);
		assert!(!beaconcrypt_server_is_poisoned(server.0));
		assert_eq!(server.head(), initial);
		assert_eq!(
			beaconcrypt_server_last_status(server.0),
			STATUS_INVALID_ARGUMENT
		);
		let _ = register(&server);
		let bytes = state.lock().unwrap().bytes.clone().unwrap();
		let mut previous = server.head();
		previous.generation -= 1;
		assert_eq!(
			beaconcrypt_snapshot_validate_successor(
				bytes.as_ptr(),
				bytes.len(),
				&previous,
				&mut output
			),
			STATUS_STALE_GENERATION
		);
	}

	#[test]
	fn c_seeded_mldsa_identity_and_public_key_getters() {
		let server = OwnedServer(beaconcrypt_server_new_from_seed(
			19,
			[7; 32].as_ptr(),
			32,
			[8; 32].as_ptr(),
			32,
		));
		assert!(!server.0.is_null());
		let public_key = copy_buffer(beaconcrypt_server_identity_pk(server.0));
		let mldsa_key = copy_buffer(beaconcrypt_server_mldsa_public_key(server.0));
		assert_eq!(
			mldsa_key,
			crate::MldsaIdentity::from_seed([8; 32]).public_key()
		);
		let beacon = beaconcrypt_beacon_new(
			19,
			public_key.as_ptr(),
			public_key.len(),
			mldsa_key.as_ptr(),
			mldsa_key.len(),
		);
		assert!(!beacon.is_null());
		beaconcrypt_beacon_free(beacon);
	}

	#[test]
	fn reentrant_calls_from_store_callbacks_are_refused() {
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let (mut beacon, kid) = register(&server);
		state.lock().unwrap().reenter = server.0.expose_provenance();
		let before = server.head();
		let sent = beaconcrypt_encrypt_to_beacon(server.0, kid, b"outer".as_ptr(), 5);
		assert_eq!(beaconcrypt_server_last_status(server.0), STATUS_OK);
		let frame = copy_buffer(sent);
		assert_eq!(beacon.decrypt_message(&frame).unwrap().plaintext, b"outer");
		state.lock().unwrap().reenter = 0;
		assert_eq!(server.head().generation, before.generation + 1);
		assert_eq!(state.lock().unwrap().refused_reentries, [true]);
		assert!(!beaconcrypt_server_is_poisoned(server.0));
	}

	#[test]
	fn required_inputs_and_seeds_reject_lengths_beyond_isize_max() {
		// No Rust slice can be this long; building one would be undefined behaviour.
		let oversized = isize::MAX as usize + 1;
		let state = Arc::new(Mutex::new(StoreState::default()));
		let destroyed = Arc::new(AtomicUsize::new(0));
		let server = create_durable(&state, &destroyed);
		let (_beacon, _kid) = register(&server);
		let before = server.head();
		let response =
			beaconcrypt_register_beacon(server.0, b"x".as_ptr(), oversized, std::ptr::null(), 0);
		assert!(response.response.ptr.is_null());
		assert_eq!(
			beaconcrypt_server_last_status(server.0),
			STATUS_INVALID_ARGUMENT
		);
		let output = beaconcrypt_decrypt_beacon_message(server.0, b"x".as_ptr(), oversized);
		assert!(output.ptr.is_null());
		assert_eq!(
			beaconcrypt_server_last_status(server.0),
			STATUS_INVALID_ARGUMENT
		);
		assert_eq!(server.head(), before);

		let public_key = copy_buffer(beaconcrypt_server_identity_pk(server.0));
		let mldsa_key = copy_buffer(beaconcrypt_server_mldsa_public_key(server.0));
		assert!(
			beaconcrypt_beacon_new(19, public_key.as_ptr(), oversized, mldsa_key.as_ptr(), 32)
				.is_null()
		);
		for (seed, mldsa) in [(oversized, 0), (0, oversized)] {
			let (seed_ptr, mldsa_ptr) = ([7u8; 32].as_ptr(), [8u8; 32].as_ptr());
			assert!(
				beaconcrypt_server_new_from_seed(19, seed_ptr, seed, mldsa_ptr, mldsa).is_null()
			);
			let mut status = u32::MAX;
			let before = destroyed.load(Ordering::SeqCst);
			let created = beaconcrypt_server_create_with_store_v2(
				19,
				seed_ptr,
				seed,
				mldsa_ptr,
				mldsa,
				SnapshotStoreCallbacksV2 {
					callbacks: callbacks(&state, &destroyed, LoadMode::Normal),
					last_error: Some(last_error_callback),
				},
				&mut status,
			);
			assert!(created.is_null());
			assert_eq!(status, STATUS_INVALID_ARGUMENT);
			assert_eq!(destroyed.load(Ordering::SeqCst), before + 1);
		}
	}

	#[test]
	fn c_constructors_reject_malformed_lengths() {
		let server = OwnedServer(beaconcrypt_server_new(19));
		assert!(!server.0.is_null());
		let public_key = copy_buffer(beaconcrypt_server_identity_pk(server.0));
		let mldsa_key = copy_buffer(beaconcrypt_server_mldsa_public_key(server.0));
		assert_eq!(mldsa_key.len(), crate::MLDSA_PUBLIC_KEY_LEN);
		for length in [1, 31, 33, 64] {
			let bytes = vec![7; length];
			assert!(
				beaconcrypt_beacon_new(
					19,
					bytes.as_ptr(),
					bytes.len(),
					mldsa_key.as_ptr(),
					mldsa_key.len()
				)
				.is_null()
			);
			assert!(
				beaconcrypt_server_new_from_seed(
					19,
					bytes.as_ptr(),
					bytes.len(),
					std::ptr::null(),
					0
				)
				.is_null()
			);
			assert!(
				beaconcrypt_server_new_from_seed(
					19,
					std::ptr::null(),
					0,
					bytes.as_ptr(),
					bytes.len()
				)
				.is_null()
			);
		}
		for length in [
			0,
			32,
			crate::MLDSA_PUBLIC_KEY_LEN - 1,
			crate::MLDSA_PUBLIC_KEY_LEN + 1,
		] {
			let bytes = vec![7; length];
			assert!(
				beaconcrypt_beacon_new(
					19,
					public_key.as_ptr(),
					public_key.len(),
					bytes.as_ptr(),
					bytes.len()
				)
				.is_null()
			);
		}
		assert!(
			beaconcrypt_beacon_new(
				19,
				public_key.as_ptr(),
				public_key.len(),
				std::ptr::null(),
				0
			)
			.is_null()
		);
		assert!(
			beaconcrypt_beacon_new(19, std::ptr::null(), 0, mldsa_key.as_ptr(), mldsa_key.len())
				.is_null()
		);
		assert!(
			beaconcrypt_server_mldsa_public_key(std::ptr::null())
				.ptr
				.is_null()
		);
		beaconcrypt_free_buffer(empty_buffer());
		beaconcrypt_free_buffer(into_buffer(Vec::with_capacity(32)));
		beaconcrypt_free_buffer(into_buffer(vec![7; 48]));
	}
}
