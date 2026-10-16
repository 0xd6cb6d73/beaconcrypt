// SPDX-License-Identifier: 0BSD

use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Arc, Mutex};

use crate::persistence::BindingSnapshotStore;
use crate::server::{RecvState, SendState};
use crate::{
	Beacon as PqxdhBeacon, PersistenceError as NativePersistenceError, PersistentServer,
	ProviderBeacon, RegResponse, ServerSnapshot, SnapshotHead, SnapshotLineage, SnapshotStore,
};
use pyo3::class::{PyTraverseError, PyVisit};
use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyBytes;

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
#[pyclass(name = "SnapshotHead", frozen, eq, skip_from_py_object)]
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
	fn load(&self) -> Option<ServerSnapshot> {
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
		.flatten()
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
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
		.unwrap_or(false)
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
	data: Vec<u8>,
	state: String,
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
		let state = value.state.as_str().to_owned();
		Self {
			data: value.data,
			state,
			kid: value.kid,
			seq: value.seq,
		}
	}
}

impl From<RecvState> for EncryptStatePy {
	fn from(value: RecvState) -> Self {
		let state = value.state.as_str().to_owned();
		Self {
			data: value.data,
			state,
			kid: value.kid,
			seq: value.seq,
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
					store,
					SnapshotLineage::from_bytes(bytes),
				)
			}
			None => PythonServer::create(kid, id_seed, store),
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
	fn new(py: Python<'_>, kid: u64, id_seed: Option<&[u8]>) -> PyResult<Self> {
		Self::create(
			py,
			kid,
			id_seed,
			Box::<BindingSnapshotStore>::default(),
			None,
			CallbackError::default(),
		)
	}

	/// Create a server whose results are released only after the store durably commits them.
	/// The store supplies load() -> bytes | None and compare_and_swap(expected, replacement) -> bool.
	/// Callbacks must atomically validate and compare the complete trusted head, preserve rollback resistance, and never reenter this server.
	#[staticmethod]
	#[pyo3(signature = (kid, id_seed, store, lineage=None))]
	fn create_with_store(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		store: Py<PyAny>,
		lineage: Option<&[u8]>,
	) -> PyResult<Self> {
		let errors = CallbackError::default();
		let object = Arc::new(Mutex::new(Some(store)));
		let store = Box::new(PySnapshotStore {
			object: object.clone(),
			errors: errors.clone(),
		});
		let mut server = Self::create(py, kid, id_seed, store, lineage, errors)?;
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
	fn export_state(&self, py: Python<'_>) -> PyResult<Vec<u8>> {
		persistence_result(py, self._0.snapshot(), &self.callback_error)
			.map(|snapshot| snapshot.as_bytes().to_vec())
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
	) -> PyResult<Option<Vec<u8>>> {
		persistence_result(py, self._0.decrypt_message(&data), &self.callback_error)
			.map(|decrypted| decrypted.map(|decrypted| decrypted.plaintext))
	}

	fn encrypt_to_beacon(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<Vec<u8>>> {
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
	) -> PyResult<Option<String>> {
		persistence_result(
			py,
			self._0.encrypt_and_update_json(&data, kid),
			&self.callback_error,
		)
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
	) -> PyResult<Option<String>> {
		persistence_result(
			py,
			self._0.decrypt_and_update_json(&data),
			&self.callback_error,
		)
	}

	fn id_pk(&self) -> &[u8] {
		self._0.identity_pk().as_bytes()
	}
}

#[pyclass(name = "BeaconCryptBeacon")]
pub struct Beacon {
	_0: PqxdhBeacon,
}
#[pymethods]
impl Beacon {
	#[new]
	fn new(server_kid: u64, server_id_pk: &[u8]) -> PyResult<Self> {
		PqxdhBeacon::try_new(server_kid, server_id_pk)
			.map(|beacon| Self { _0: beacon })
			.map_err(|error| PyValueError::new_err(error.to_string()))
	}

	/// Begin the beacon registration process. The output buffer should be sent as-is over the network.
	fn generate_registration(&mut self) -> Option<Vec<u8>> {
		self._0.get_registration_bundle()
	}

	/// Process the registration response and optional initial data. The raw buffer sent by the server must be passed as-is as `data`.
	/// The response contains the contents of the initial message, or `0xFF` if there was none. Once this function returns, the beacon is registered
	fn process_initial_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		self._0.finish_registration(data.as_slice())
	}

	fn decrypt_server_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		self._0
			.decrypt_message(&data)
			.map(|decrypted| decrypted.plaintext)
	}

	fn encrypt_message_to_server(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		self._0
			.encrypt_message(&data)
			.map(|encrypted| encrypted.ciphertext)
	}
}
