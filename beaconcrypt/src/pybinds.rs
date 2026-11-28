// SPDX-License-Identifier: 0BSD

use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Arc, Mutex};

use crate::persistence::BindingSnapshotStore;
use crate::server::{RecvState, SendState};
use crate::{
	Beacon as PqxdhBeacon, PersistenceError as NativePersistenceError, PersistentServer,
	ProviderBeacon, RegResponse, SendOutcome, ServerSnapshot, SnapshotHead, SnapshotLineage,
	SnapshotStore,
};
use pyo3::class::{PyTraverseError, PyVisit};
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyString};
use zeroize::Zeroizing;

pyo3::create_exception!(beaconcrypt, PersistenceError, PyValueError);

type CallbackError = Arc<Mutex<Option<PyErr>>>;
type StoreObject = Arc<Mutex<Option<Py<PyAny>>>>;
type PythonServer = PersistentServer<Box<dyn SnapshotStore + Send + Sync>>;

fn persistence_error(py: Python<'_>, error: NativePersistenceError, cause: Option<PyErr>) -> PyErr {
	let code = match error {
		NativePersistenceError::MissingSnapshot => "missing_snapshot",
		NativePersistenceError::InvalidSnapshot => "invalid_snapshot",
		NativePersistenceError::NonCanonicalSnapshot => "non_canonical_snapshot",
		NativePersistenceError::StaleGeneration => "stale_generation",
		NativePersistenceError::GenerationExhausted => "generation_exhausted",
		NativePersistenceError::Encoding => "encoding",
		NativePersistenceError::OutputEncoding => "output_encoding",
		NativePersistenceError::Initialization => "initialization",
		NativePersistenceError::Digest => "digest",
		NativePersistenceError::Poisoned => "poisoned",
		NativePersistenceError::Storage => "storage",
		NativePersistenceError::CommitUnknown => "commit_unknown",
		NativePersistenceError::CapacityExceeded => "capacity_exceeded",
	};
	let exception = PersistenceError::new_err(error.to_string());
	if let Err(attribute_error) = exception.value(py).setattr("code", code) {
		return attribute_error;
	}
	exception.set_cause(py, cause);
	exception
}

fn take_callback_error(errors: &CallbackError) -> Option<PyErr> {
	errors
		.lock()
		.unwrap_or_else(|error| error.into_inner())
		.take()
}

fn persistence_result<T>(
	py: Python<'_>,
	result: Result<T, NativePersistenceError>,
	errors: &CallbackError,
) -> PyResult<T> {
	let cause = take_callback_error(errors);
	result.map_err(|error| persistence_error(py, error, cause))
}

/// Immutable comparison token obtained from authoritative snapshot storage.
#[pyclass(name = "SnapshotHead", frozen, eq)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SnapshotHeadPy {
	inner: SnapshotHead,
}

#[pymethods]
impl SnapshotHeadPy {
	#[new]
	fn new(lineage: &[u8], generation: u64, digest: &[u8]) -> PyResult<Self> {
		let lineage = lineage
			.try_into()
			.map_err(|_| PyValueError::new_err("lineage must contain 32 bytes"))?;
		let digest = digest
			.try_into()
			.map_err(|_| PyValueError::new_err("digest must contain 32 bytes"))?;
		Ok(Self {
			inner: SnapshotHead::from_parts(
				SnapshotLineage::from_bytes(lineage),
				generation,
				digest,
			),
		})
	}

	#[getter]
	fn lineage(&self) -> Vec<u8> {
		self.inner.lineage().as_bytes().to_vec()
	}

	#[getter]
	fn generation(&self) -> u64 {
		self.inner.generation()
	}

	#[getter]
	fn digest(&self) -> Vec<u8> {
		self.inner.digest().to_vec()
	}

	fn __hash__(&self) -> u64 {
		let mut hasher = DefaultHasher::new();
		self.inner.lineage().as_bytes().hash(&mut hasher);
		self.inner.generation().hash(&mut hasher);
		self.inner.digest().hash(&mut hasher);
		hasher.finish()
	}
}

/// Parse an envelope comparison token; this does not authenticate its bytes.
#[pyfunction]
pub fn snapshot_head(py: Python<'_>, data: Vec<u8>) -> PyResult<SnapshotHeadPy> {
	ServerSnapshot::from_bytes(data)
		.head()
		.map(|inner| SnapshotHeadPy { inner })
		.map_err(|error| persistence_error(py, error, None))
}

/// Validate envelope succession inside the store's atomic comparison transaction.
#[pyfunction]
#[pyo3(signature = (data, expected=None))]
pub fn validate_snapshot_successor(
	py: Python<'_>,
	data: Vec<u8>,
	expected: Option<PyRef<'_, SnapshotHeadPy>>,
) -> PyResult<SnapshotHeadPy> {
	ServerSnapshot::from_bytes(data)
		.validate_successor(expected.as_ref().map(|head| &head.inner))
		.map(|inner| SnapshotHeadPy { inner })
		.map_err(|error| persistence_error(py, error, None))
}

struct PySnapshotStore {
	object: StoreObject,
	errors: CallbackError,
}

impl PySnapshotStore {
	fn object(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
		self.object
			.lock()
			.unwrap_or_else(|error| error.into_inner())
			.as_ref()
			.map(|object| object.clone_ref(py))
			.ok_or_else(|| PyRuntimeError::new_err("snapshot store has been released"))
	}

	fn capture<T>(&self, operation: impl for<'py> FnOnce(Python<'py>) -> PyResult<T>) -> Option<T> {
		Python::attach(|py| match operation(py) {
			Ok(value) => Some(value),
			Err(error) => {
				let mut errors = self
					.errors
					.lock()
					.unwrap_or_else(|error| error.into_inner());
				if errors.is_none() {
					*errors = Some(error);
				}
				None
			}
		})
	}
}

impl SnapshotStore for PySnapshotStore {
	fn load(&self) -> Result<Option<ServerSnapshot>, NativePersistenceError> {
		self.capture(|py| {
			let result = self.object(py)?.bind(py).call_method0("load")?;
			if result.is_none() {
				Ok(None)
			} else {
				Ok(Some(ServerSnapshot::from_bytes(
					result.cast::<PyBytes>()?.as_bytes().to_vec(),
				)))
			}
		})
		.ok_or(NativePersistenceError::Storage)
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> Result<bool, NativePersistenceError> {
		self.capture(|py| {
			let expected = expected
				.map(|inner| Py::new(py, SnapshotHeadPy { inner: *inner }))
				.transpose()?;
			self.object(py)?
				.bind(py)
				.call_method1(
					"compare_and_swap",
					(expected, PyBytes::new(py, replacement.as_bytes())),
				)?
				.extract::<bool>()
		})
		.ok_or(NativePersistenceError::CommitUnknown)
	}
}

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

#[pyclass(name = "EncryptState")]
pub struct EncryptStatePy {
	data: Zeroizing<Vec<u8>>,
	state: Zeroizing<String>,
	kid: u64,
	seq: u64,
}

#[pymethods]
impl EncryptStatePy {
	pub fn data(&self) -> &Vec<u8> {
		&self.data
	}

	/// Return inert plaintext ratchet JSON for observation only.
	/// It is secret-bearing, unauthenticated, and not restorable.
	pub fn state(&self) -> &str {
		&self.state
	}

	pub fn key_id(&self) -> u64 {
		self.kid
	}

	pub fn seq(&self) -> u64 {
		self.seq
	}
}

impl From<SendState> for EncryptStatePy {
	fn from(value: SendState) -> Self {
		let state = Zeroizing::new(value.state.as_str().to_owned());
		Self {
			data: Zeroizing::new(value.data),
			state,
			kid: value.kid,
			seq: value.seq,
		}
	}
}

impl From<RecvState> for EncryptStatePy {
	fn from(value: RecvState) -> Self {
		let state = Zeroizing::new(value.state.as_str().to_owned());
		Self {
			data: Zeroizing::new(value.data),
			state,
			kid: value.kid,
			seq: value.seq,
		}
	}
}

enum SendValue {
	Bytes(Zeroizing<Vec<u8>>),
	Update(EncryptStatePy),
	Json(Zeroizing<String>),
}

struct SentValue {
	value: SendValue,
	key_id: u64,
	seq: u64,
}

/// Exact send effect. Values copied into Python remain owned by the caller; the library's retained buffers are erased when this object is dropped.
#[pyclass(name = "SendResult", frozen)]
pub struct SendResultPy {
	inner: SendOutcome<SentValue>,
}

impl SendResultPy {
	pub(crate) fn encrypted(outcome: SendOutcome<crate::Encrypted>) -> Self {
		Self {
			inner: outcome.map(|value| SentValue {
				key_id: value.key_id,
				seq: value.seq,
				value: SendValue::Bytes(Zeroizing::new(value.ciphertext)),
			}),
		}
	}

	fn update(outcome: SendOutcome<SendState>) -> Self {
		Self {
			inner: outcome.map(|value| SentValue {
				key_id: value.kid,
				seq: value.seq,
				value: SendValue::Update(EncryptStatePy::from(value)),
			}),
		}
	}

	fn json(outcome: SendOutcome<String>, key_id: u64, seq: u64) -> Self {
		Self {
			inner: outcome.map(|value| SentValue {
				key_id,
				seq,
				value: SendValue::Json(Zeroizing::new(value)),
			}),
		}
	}
}

#[pymethods]
impl SendResultPy {
	#[getter]
	fn outcome(&self) -> &'static str {
		match self.inner {
			SendOutcome::Rejected => "rejected",
			SendOutcome::Sent(_) => "sent",
			SendOutcome::ConsumedWithoutOutput => "consumed_without_output",
		}
	}

	#[getter]
	fn changed(&self) -> bool {
		self.inner.changed()
	}

	#[getter]
	fn key_id(&self) -> Option<u64> {
		match &self.inner {
			SendOutcome::Sent(value) => Some(value.key_id),
			_ => None,
		}
	}

	#[getter]
	fn seq(&self) -> Option<u64> {
		match &self.inner {
			SendOutcome::Sent(value) => Some(value.seq),
			_ => None,
		}
	}

	#[getter]
	fn value(&self, py: Python<'_>) -> PyResult<Py<PyAny>> {
		let SendOutcome::Sent(value) = &self.inner else {
			return Ok(py.None());
		};
		match &value.value {
			SendValue::Bytes(bytes) => Ok(PyBytes::new(py, bytes).into_any().unbind()),
			SendValue::Json(json) => Ok(PyString::new(py, json).into_any().unbind()),
			SendValue::Update(value) => Py::new(
				py,
				EncryptStatePy {
					data: value.data.clone(),
					state: value.state.clone(),
					kid: value.kid,
					seq: value.seq,
				},
			)
			.map(|value| value.into_any()),
		}
	}
}

/// Server backed by trusted snapshot storage. Store callbacks must not reenter this server.
#[pyclass(name = "BeaconCryptServer")]
pub struct Server {
	_0: PythonServer,
	callback_error: CallbackError,
	store_object: Option<StoreObject>,
}

impl Server {
	fn create(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		store: Box<dyn SnapshotStore + Send + Sync>,
		lineage: Option<&[u8]>,
		callback_error: CallbackError,
	) -> PyResult<Self> {
		let server = match lineage {
			Some(bytes) => {
				let bytes = bytes
					.try_into()
					.map_err(|_| PyValueError::new_err("lineage must contain 32 bytes"))?;
				PythonServer::create_with_lineage(
					kid,
					id_seed,
					mldsa_seed,
					store,
					SnapshotLineage::from_bytes(bytes),
				)
			}
			None => PythonServer::create(kid, id_seed, mldsa_seed, store),
		};
		let server = persistence_result(py, server, &callback_error)?;
		Ok(Self {
			_0: server,
			callback_error,
			store_object: None,
		})
	}

	fn restored(
		py: Python<'_>,
		store: Box<dyn SnapshotStore + Send + Sync>,
		callback_error: CallbackError,
	) -> PyResult<Self> {
		let server = persistence_result(py, PythonServer::restore(store), &callback_error)?;
		Ok(Self {
			_0: server,
			callback_error,
			store_object: None,
		})
	}
}

#[pymethods]
impl Server {
	fn __traverse__(&self, visit: PyVisit<'_>) -> Result<(), PyTraverseError> {
		if let Some(store) = &self.store_object {
			let object = store.lock().unwrap_or_else(|error| error.into_inner());
			visit.call(object.as_ref())?;
		}
		Ok(())
	}

	fn __clear__(&mut self) {
		if let Some(store) = self.store_object.take() {
			let object = store
				.lock()
				.unwrap_or_else(|error| error.into_inner())
				.take();
			drop(object);
		}
	}

	#[new]
	#[pyo3(signature = (kid, id_seed, mldsa_seed))]
	fn new(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
	) -> PyResult<Self> {
		Self::create(
			py,
			kid,
			id_seed,
			mldsa_seed,
			Box::<BindingSnapshotStore>::default(),
			None,
			CallbackError::default(),
		)
	}

	/// Create a server whose results are released only after the store durably commits them.
	/// The store supplies load() -> bytes | None and compare_and_swap(expected, replacement) -> bool.
	/// Read exceptions produce `storage`; commit exceptions produce `commit_unknown` because the store may already have committed. The original exception remains the cause.
	/// Callbacks must atomically validate and compare the complete trusted head, preserve rollback resistance, and never reenter this server.
	#[staticmethod]
	#[pyo3(signature = (kid, id_seed, mldsa_seed, store, lineage=None))]
	fn create_with_store(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		store: Py<PyAny>,
		lineage: Option<&[u8]>,
	) -> PyResult<Self> {
		let errors = CallbackError::default();
		let object = Arc::new(Mutex::new(Some(store)));
		let store = Box::new(PySnapshotStore {
			object: object.clone(),
			errors: errors.clone(),
		});
		let mut server = Self::create(py, kid, id_seed, mldsa_seed, store, lineage, errors)?;
		server.store_object = Some(object);
		Ok(server)
	}

	/// Activate the current trusted snapshot by compare-and-swap before returning a server.
	/// Store callbacks must not reenter this server.
	#[staticmethod]
	fn restore(py: Python<'_>, store: Py<PyAny>) -> PyResult<Self> {
		let errors = CallbackError::default();
		let object = Arc::new(Mutex::new(Some(store)));
		let store = Box::new(PySnapshotStore {
			object: object.clone(),
			errors: errors.clone(),
		});
		let mut server = Self::restored(py, store, errors)?;
		server.store_object = Some(object);
		Ok(server)
	}

	/// Restore trusted checkpoint bytes. Save the advanced checkpoint before using the server.
	/// Standalone bytes contain plaintext secrets and cannot authenticate themselves or detect rollback.
	#[staticmethod]
	fn from_state(py: Python<'_>, state: Vec<u8>) -> PyResult<Self> {
		let store = BindingSnapshotStore::from_bytes(state)
			.map_err(|error| persistence_error(py, error, None))?;
		Self::restored(py, Box::new(store), CallbackError::default())
	}

	/// Read this owner's committed plaintext checkpoint from the trusted store.
	/// For the default in-memory store, save after every potentially mutating call, including failures; rejected receives leave the checkpoint unchanged.
	fn export_state(&self, py: Python<'_>) -> PyResult<Py<PyBytes>> {
		// Copy straight from the zeroizing snapshot so no unwiped native copy remains.
		persistence_result(py, self._0.snapshot(), &self.callback_error)
			.map(|snapshot| PyBytes::new(py, snapshot.as_bytes()).unbind())
	}

	fn head(&self) -> SnapshotHeadPy {
		SnapshotHeadPy {
			inner: self._0.head(),
		}
	}

	fn is_poisoned(&self) -> bool {
		self._0.is_poisoned()
	}

	fn register_beacon(
		&mut self,
		py: Python<'_>,
		reg_buffer: &[u8],
		initial_message: Option<&[u8]>,
	) -> PyResult<Option<RegResponsePy>> {
		let secrets = persistence_result(
			py,
			self._0.get_shared_secret(reg_buffer),
			&self.callback_error,
		)?;
		let Some(secrets) = secrets else {
			return Ok(None);
		};
		persistence_result(
			py,
			self._0
				.build_registration_response(secrets, initial_message),
			&self.callback_error,
		)
		.map(|response| response.map(RegResponsePy::from))
	}

	fn decrypt_beacon_message(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<Py<PyBytes>>> {
		persistence_result(py, self._0.decrypt_message(&data), &self.callback_error)
			.map(|decrypted| decrypted.map(|decrypted| secret_bytes(py, decrypted.plaintext)))
	}

	fn encrypt_to_beacon(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<Vec<u8>>> {
		let data = Zeroizing::new(data);
		persistence_result(
			py,
			self._0.encrypt_message(&data, kid),
			&self.callback_error,
		)
		.map(|encrypted| encrypted.map(|encrypted| encrypted.ciphertext))
	}

	fn encrypt_and_update(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<EncryptStatePy>> {
		let data = Zeroizing::new(data);
		persistence_result(
			py,
			self._0.encrypt_and_update(&data, kid),
			&self.callback_error,
		)
		.map(|state| state.map(EncryptStatePy::from))
	}

	fn encrypt_and_update_json(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<Py<PyString>>> {
		let data = Zeroizing::new(data);
		persistence_result(
			py,
			self._0.encrypt_and_update_json(&data, kid),
			&self.callback_error,
		)
		.map(|json| json.map(|json| secret_string(py, json)))
	}

	/// Return an explicit committed send effect instead of an ambiguous optional message.
	fn encrypt_to_beacon_outcome(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<SendResultPy> {
		let data = Zeroizing::new(data);
		persistence_result(
			py,
			self._0.encrypt_message_outcome(&data, kid),
			&self.callback_error,
		)
		.map(SendResultPy::encrypted)
	}

	fn encrypt_and_update_outcome(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<SendResultPy> {
		let data = Zeroizing::new(data);
		persistence_result(
			py,
			self._0.encrypt_and_update_outcome(&data, kid),
			&self.callback_error,
		)
		.map(SendResultPy::update)
	}

	fn encrypt_and_update_json_outcome(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<SendResultPy> {
		let data = Zeroizing::new(data);
		let outcome = persistence_result(
			py,
			self._0.encrypt_and_update_json_outcome(&data, kid),
			&self.callback_error,
		)?;
		let sequence = self
			._0
			.ratchet_status(kid)
			.map_or(0, |status| status.send_sequence());
		Ok(SendResultPy::json(outcome, kid, sequence))
	}

	fn decrypt_and_update(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<EncryptStatePy>> {
		persistence_result(py, self._0.decrypt_and_update(&data), &self.callback_error)
			.map(|state| state.map(EncryptStatePy::from))
	}

	fn decrypt_and_update_json(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<Py<PyString>>> {
		persistence_result(
			py,
			self._0.decrypt_and_update_json(&data),
			&self.callback_error,
		)
		.map(|json| json.map(|json| secret_string(py, json)))
	}

	fn id_pk(&self) -> &[u8] {
		self._0.identity_pk().as_bytes()
	}

	fn mldsa_public_key(&self) -> Vec<u8> {
		self._0.mldsa_public_key().to_vec()
	}

	/// Retire an established peer and durably commit the removal. Its frames and sends are then refused; its replay marker is kept and its key ID is never reassigned. Returns whether a peer was removed.
	fn retire_peer(&mut self, py: Python<'_>, kid: u64) -> PyResult<bool> {
		persistence_result(py, self._0.retire_peer(kid), &self.callback_error)
	}

	/// Return the number of established peers. Raises PersistenceError while poisoned.
	fn peer_count(&self, py: Python<'_>) -> PyResult<usize> {
		self._0
			.peer_count()
			.ok_or_else(|| persistence_error(py, NativePersistenceError::Poisoned, None))
	}

	/// Return the number of retained registration replay markers, which are never removed. Raises PersistenceError while poisoned.
	fn registration_marker_count(&self, py: Python<'_>) -> PyResult<usize> {
		self._0
			.registration_marker_count()
			.ok_or_else(|| persistence_error(py, NativePersistenceError::Poisoned, None))
	}

	/// Limit established peers, or remove the limit with None. Registration at the limit raises PersistenceError with code capacity_exceeded; acceptance is refused before it consumes the replay marker. The limit is not saved in snapshots.
	#[pyo3(signature = (max_peers))]
	fn set_max_peers(&mut self, max_peers: Option<usize>) {
		self._0
			.set_max_peers(max_peers.and_then(core::num::NonZeroUsize::new));
	}
}

/// Copy secret bytes into Python; the native buffer is wiped when it is dropped here.
pub(crate) fn secret_bytes(py: Python<'_>, bytes: Vec<u8>) -> Py<PyBytes> {
	let bytes = Zeroizing::new(bytes);
	PyBytes::new(py, &bytes).unbind()
}

/// Copy secret-bearing JSON into Python; the native string is wiped when it is dropped here.
fn secret_string(py: Python<'_>, text: String) -> Py<PyString> {
	let text = Zeroizing::new(text);
	PyString::new(py, &text).unbind()
}

#[pyclass(name = "BeaconCryptBeacon")]
pub struct Beacon {
	_0: PqxdhBeacon,
}
#[pymethods]
impl Beacon {
	#[new]
	fn new(server_kid: u64, server_id_pk: &[u8], server_mldsa_pk: &[u8]) -> PyResult<Self> {
		PqxdhBeacon::try_new(server_kid, server_id_pk, server_mldsa_pk)
			.map(|beacon| Self { _0: beacon })
			.map_err(|error| PyValueError::new_err(error.to_string()))
	}

	/// Begin the beacon registration process. The output buffer should be sent as-is over the network.
	fn generate_registration(&mut self) -> Option<Vec<u8>> {
		self._0.get_registration_bundle()
	}

	/// Process the registration response and optional initial data. The raw buffer sent by the server must be passed as-is as `data`.
	/// The response contains the contents of the initial message, or `0xFF` if there was none. Once this function returns, the beacon is registered
	fn process_initial_message(&mut self, py: Python<'_>, data: Vec<u8>) -> Option<Py<PyBytes>> {
		self._0
			.finish_registration(data.as_slice())
			.map(|plaintext| secret_bytes(py, plaintext))
	}

	fn decrypt_server_message(&mut self, py: Python<'_>, data: Vec<u8>) -> Option<Py<PyBytes>> {
		self._0
			.decrypt_message(&data)
			.map(|decrypted| secret_bytes(py, decrypted.plaintext))
	}

	fn encrypt_message_to_server_outcome(&mut self, data: Vec<u8>) -> SendResultPy {
		let data = Zeroizing::new(data);
		SendResultPy::encrypted(self._0.encrypt_message_outcome(&data))
	}

	fn encrypt_message_to_server(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		let data = Zeroizing::new(data);
		self._0
			.encrypt_message(&data)
			.map(|encrypted| encrypted.ciphertext)
	}
}

#[cfg(test)]
mod send_result_tests {
	use super::*;

	#[test]
	fn explicit_failure_results_preserve_effect_and_withhold_success_metadata() {
		for (inner, outcome, changed) in [
			(SendOutcome::Rejected, "rejected", false),
			(
				SendOutcome::ConsumedWithoutOutput,
				"consumed_without_output",
				true,
			),
		] {
			let result = SendResultPy::encrypted(inner);
			assert_eq!(result.outcome(), outcome);
			assert_eq!(result.changed(), changed);
			assert_eq!(result.key_id(), None);
			assert_eq!(result.seq(), None);
		}
	}
}
