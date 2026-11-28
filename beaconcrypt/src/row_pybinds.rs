// SPDX-License-Identifier: 0BSD

use std::{
	ptr,
	sync::{
		Arc, Mutex,
		atomic::{AtomicBool, Ordering},
	},
	thread::{self, ThreadId},
};

use pyo3::{
	class::{PyTraverseError, PyVisit},
	exceptions::{PyRuntimeError, PyValueError},
	prelude::*,
	types::PyBytes,
};

use crate::pybinds::{RegResponsePy, SendResultPy};
use crate::row_binding_server::BindingRowServer;
use crate::{
	CachedRowServer, Decrypted, Encrypted, RowError, RowRegistrationDecision, RowRegistrationPhase,
	RowServer, RowSession, RowStore, RowTransaction, RowTransition, SnapshotLineage,
};
use zeroize::Zeroizing;

pyo3::create_exception!(beaconcrypt, RowPersistenceError, PyValueError);
pyo3::create_exception!(beaconcrypt, RowRegistrationError, RowPersistenceError);

type Object = Arc<Mutex<Option<Py<PyAny>>>>;
type Errors = Arc<Mutex<Option<PyErr>>>;
type NativeServer = BindingRowServer<Box<dyn RowStore + Send + Sync>>;

/// Message bytes and authenticated peer/sequence metadata, without ratchet state. Session callbacks receive pending messages and must not publish them before the outer call succeeds.
#[pyclass(name = "RowMessage", frozen)]
pub struct RowMessagePy {
	data: Zeroizing<Vec<u8>>,
	#[pyo3(get)]
	key_id: u64,
	#[pyo3(get)]
	seq: u64,
}

#[pymethods]
impl RowMessagePy {
	#[getter]
	fn data<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
		PyBytes::new(py, &self.data)
	}
}

impl From<Encrypted> for RowMessagePy {
	fn from(value: Encrypted) -> Self {
		Self {
			data: Zeroizing::new(value.ciphertext),
			key_id: value.key_id,
			seq: value.seq,
		}
	}
}

impl From<Decrypted> for RowMessagePy {
	fn from(value: Decrypted) -> Self {
		Self {
			data: Zeroizing::new(value.plaintext),
			key_id: value.key_id,
			seq: value.seq,
		}
	}
}

struct PythonStore {
	object: Object,
	errors: Errors,
}

impl PythonStore {
	fn call<T>(
		&self,
		callback: impl for<'py> FnOnce(Python<'py>, Bound<'py, PyAny>) -> PyResult<T>,
	) -> Result<T, RowError> {
		Python::attach(|py| {
			let object = self
				.object
				.lock()
				.unwrap_or_else(|error| error.into_inner())
				.as_ref()
				.map(|object| object.clone_ref(py));
			let result = object
				.ok_or_else(|| PyRuntimeError::new_err("row store has been released"))
				.and_then(|object| callback(py, object.into_bound(py)));
			result.map_err(|error| {
				let mut errors = self
					.errors
					.lock()
					.unwrap_or_else(|error| error.into_inner());
				if errors.is_none() {
					*errors = Some(error);
				}
				RowError::Storage("database callback failed".into())
			})
		})
	}
}

impl RowTransaction for PythonStore {
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.call(|py, object| {
			let value = object.call_method1("load", (PyBytes::new(py, key),))?;
			if value.is_none() {
				Ok(None)
			} else {
				Ok(Some(value.cast::<PyBytes>()?.as_bytes().to_vec()))
			}
		})
	}

	fn expect(&mut self, key: &[u8], expected: Option<&[u8]>) -> Result<(), RowError> {
		let matched = self.call(|py, object| {
			if object.hasattr("expect")? {
				let value = expected.map(|bytes| PyBytes::new(py, bytes));
				let output = object.call_method1("expect", (PyBytes::new(py, key), value))?;
				if output.is_none() {
					Ok(true)
				} else {
					output.extract::<bool>()
				}
			} else {
				let actual = object.call_method1("load", (PyBytes::new(py, key),))?;
				if actual.is_none() {
					Ok(expected.is_none())
				} else {
					Ok(Some(actual.cast::<PyBytes>()?.as_bytes()) == expected)
				}
			}
		})?;
		if matched {
			Ok(())
		} else {
			Err(RowError::Conflict)
		}
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.call(|py, object| {
			object
				.call_method1("store", (PyBytes::new(py, key), PyBytes::new(py, value)))
				.map(|_| ())
		})
	}
}

impl RowStore for PythonStore {
	fn transaction(
		&mut self,
		operation: &mut dyn FnMut(&mut dyn RowTransaction) -> Result<(), RowError>,
	) -> Result<(), RowError> {
		if let Err(error) = self.call(|_, object| object.call_method0("begin").map(|_| ())) {
			let _ = self.call(|_, object| object.call_method0("rollback").map(|_| ()));
			return Err(error);
		}
		let result = operation(self)
			.and_then(|()| self.call(|_, object| object.call_method0("commit").map(|_| ())));
		if result.is_err() {
			let _ = self.call(|_, object| object.call_method0("rollback").map(|_| ()));
		}
		result
	}
}

fn result<T>(py: Python<'_>, value: Result<T, RowError>, errors: &Errors) -> PyResult<T> {
	let cause = errors
		.lock()
		.unwrap_or_else(|error| error.into_inner())
		.take();
	value.map_err(|error| exception(py, error, cause))
}

fn exception(py: Python<'_>, error: RowError, cause: Option<PyErr>) -> PyErr {
	let code = match &error {
		RowError::Storage(_) => "storage",
		RowError::Conflict => "conflict",
		RowError::MissingIdentity => "missing_identity",
		RowError::InvalidRow => "invalid_row",
		RowError::GenerationExhausted => "generation_exhausted",
		RowError::Initialization => "initialization",
		RowError::OutputEncoding => "encoding",
		RowError::InvalidSession => "invalid_session",
	};
	let exception = RowPersistenceError::new_err(error.to_string());
	if let Err(error) = exception.value(py).setattr("code", code) {
		return error;
	}
	exception.set_cause(py, cause);
	exception
}

fn lineage(bytes: &[u8]) -> PyResult<SnapshotLineage> {
	Ok(SnapshotLineage::from_bytes(bytes.try_into().map_err(
		|_| PyValueError::new_err("lineage must contain 32 bytes"),
	)?))
}

/// A database-backed server that loads and commits only the selected peer. Store callbacks must implement a serializable durable transaction and raise exceptions on failure. Callbacks cannot reenter their server.
#[pyclass(name = "BeaconCryptRowServer", subclass)]
pub struct RowServerPy {
	server: Option<NativeServer>,
	object: Object,
	errors: Errors,
}

impl RowServerPy {
	fn native(&mut self) -> PyResult<&mut NativeServer> {
		self.server
			.as_mut()
			.ok_or_else(|| PyRuntimeError::new_err("row server is closed"))
	}

	fn construct(
		py: Python<'_>,
		store: Py<PyAny>,
		create: impl FnOnce(Box<dyn RowStore + Send + Sync>) -> Result<NativeServer, RowError>,
	) -> PyResult<Self> {
		let object = Arc::new(Mutex::new(Some(store)));
		let errors = Errors::default();
		let database = Box::new(PythonStore {
			object: Arc::clone(&object),
			errors: Arc::clone(&errors),
		});
		let server = result(py, create(database), &errors)?;
		Ok(Self {
			server: Some(server),
			object,
			errors,
		})
	}
}

#[pymethods]
impl RowServerPy {
	#[staticmethod]
	#[pyo3(signature = (kid, id_seed, mldsa_seed, store, lineage_bytes))]
	fn create(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		store: Py<PyAny>,
		lineage_bytes: &[u8],
	) -> PyResult<Self> {
		let lineage = lineage(lineage_bytes)?;
		Self::construct(py, store, |store| {
			RowServer::create(kid, id_seed, mldsa_seed, store, lineage).map(BindingRowServer::Rows)
		})
	}

	#[staticmethod]
	fn open(py: Python<'_>, store: Py<PyAny>, lineage_bytes: &[u8]) -> PyResult<Self> {
		let lineage = lineage(lineage_bytes)?;
		Self::construct(py, store, |store| {
			RowServer::open(store, lineage).map(BindingRowServer::Rows)
		})
	}

	fn cache_capacity(&mut self) -> PyResult<usize> {
		Ok(self.native()?.cache_capacity())
	}
	fn cached_peer_count(&mut self) -> PyResult<usize> {
		Ok(self.native()?.cached_peer_count())
	}
	fn clear_cache(&mut self) -> PyResult<()> {
		self.native()?.clear_cache();
		Ok(())
	}

	fn close(&mut self) {
		self.server = None;
		self.object
			.lock()
			.unwrap_or_else(|error| error.into_inner())
			.take();
	}

	fn __traverse__(&self, visit: PyVisit<'_>) -> Result<(), PyTraverseError> {
		visit.call(
			self.object
				.lock()
				.unwrap_or_else(|error| error.into_inner())
				.as_ref(),
		)
	}

	fn __clear__(&mut self) {
		self.close();
	}

	fn id_pk(&mut self) -> PyResult<Vec<u8>> {
		Ok(self.native()?.identity_pk().as_bytes().to_vec())
	}

	fn mldsa_public_key(&mut self) -> PyResult<Vec<u8>> {
		Ok(self.native()?.mldsa_public_key().to_vec())
	}

	fn lineage(&mut self) -> PyResult<Vec<u8>> {
		Ok(self.native()?.lineage().as_bytes().to_vec())
	}

	#[pyo3(signature = (reg_buffer, initial_message=None))]
	fn register_beacon(
		&mut self,
		py: Python<'_>,
		reg_buffer: &[u8],
		initial_message: Option<&[u8]>,
	) -> PyResult<Option<RegResponsePy>> {
		let output = self.native()?.register_beacon(reg_buffer, initial_message);
		result(py, output, &self.errors).map(|output| output.map(RegResponsePy::from))
	}

	/// Commit application rows and at most one native message transition, then return the callback's opaque bytes.
	fn transaction(&mut self, py: Python<'_>, callback: Py<PyAny>) -> PyResult<Py<PyBytes>> {
		let errors = Arc::clone(&self.errors);
		let output = self.native()?.transaction(|session| {
			application_callback(py, session, &errors, |temporary| {
				let output = callback.call1(py, (temporary,))?;
				Ok(Zeroizing::new(
					output.bind(py).cast::<PyBytes>()?.as_bytes().to_vec(),
				))
			})
		});
		result(py, output, &errors).map(|output| PyBytes::new(py, &output).unbind())
	}

	/// Compose acceptance and completion as separate durable transactions. Completion runs only after acceptance commits. Callback errors expose a phase attribute; an uncertain commit requires authoritative application-row lookup.
	fn registration_transaction(
		&mut self,
		py: Python<'_>,
		accept: Py<PyAny>,
		complete: Py<PyAny>,
	) -> PyResult<Py<PyBytes>> {
		let errors = Arc::clone(&self.errors);
		let output = self.native()?.registration_transaction(
			|session| {
				application_callback(py, session, &errors, |temporary| {
					let output = accept.call1(py, (temporary,))?;
					let decision = output.extract::<PyRef<RowRegistrationDecisionPy>>(py)?;
					let data = Zeroizing::new(decision.data.to_vec());
					Ok(if decision.continued {
						RowRegistrationDecision::Continue(data)
					} else {
						RowRegistrationDecision::Return(data)
					})
				})
			},
			|session, accepted: Zeroizing<Vec<u8>>| {
				application_callback(py, session, &errors, |temporary| {
					let output = complete.call1(py, (temporary, PyBytes::new(py, &accepted)))?;
					Ok(Zeroizing::new(
						output.bind(py).cast::<PyBytes>()?.as_bytes().to_vec(),
					))
				})
			},
		);
		let cause = errors
			.lock()
			.unwrap_or_else(|error| error.into_inner())
			.take();
		output
			.map(|output| PyBytes::new(py, &output).unbind())
			.map_err(|error| {
				let phase = match error.phase {
					RowRegistrationPhase::Acceptance => "acceptance",
					RowRegistrationPhase::Completion => "completion",
				};
				let message = error.source.to_string();
				let base = exception(py, error.source, None);
				let error = RowRegistrationError::new_err(format!(
					"registration {phase} failed: {message}"
				));
				if let Err(error) = error.value(py).setattr("phase", phase).and_then(|_| {
					error
						.value(py)
						.setattr("code", base.value(py).getattr("code")?)
				}) {
					return error;
				}
				error.set_cause(py, cause);
				error
			})
	}

	fn encrypt_to_beacon(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<Vec<u8>>> {
		self.encrypt_to_beacon_with_metadata(py, data, kid)
			.map(|output| output.map(|mut output| std::mem::take(&mut *output.data)))
	}

	fn encrypt_to_beacon_with_metadata(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<RowMessagePy>> {
		let output = self.native()?.encrypt_message(&data, kid);
		result(py, output, &self.errors).map(|output| output.map(RowMessagePy::from))
	}

	fn encrypt_to_beacon_outcome(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<SendResultPy> {
		let output = self.native()?.encrypt_message_outcome(&data, kid);
		result(py, output, &self.errors)
			.map(|outcome| SendResultPy::encrypted(outcome.map(crate::RowMessage::into_encrypted)))
	}

	fn decrypt_beacon_message(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<Vec<u8>>> {
		self.decrypt_beacon_message_with_metadata(py, data)
			.map(|output| output.map(|mut output| std::mem::take(&mut *output.data)))
	}

	fn decrypt_beacon_message_with_metadata(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<RowMessagePy>> {
		let output = self.native()?.decrypt_message(&data);
		result(py, output, &self.errors).map(|output| output.map(RowMessagePy::from))
	}
}

/// Pending effect within a trusted transaction callback. Message bytes must not be published until the outer call succeeds.
#[pyclass(name = "RowTransition", frozen)]
pub struct RowTransitionPy {
	#[pyo3(get)]
	message: Option<Py<RowMessagePy>>,
	#[pyo3(get)]
	changed: bool,
}

impl RowTransitionPy {
	fn from_native(py: Python<'_>, value: RowTransition) -> PyResult<Self> {
		Ok(Self {
			message: value
				.message
				.map(|message| {
					Py::new(
						py,
						RowMessagePy {
							data: Zeroizing::new(message.data().to_vec()),
							key_id: message.key_id(),
							seq: message.sequence(),
						},
					)
				})
				.transpose()?,
			changed: value.changed,
		})
	}
}

/// Return an opaque result from acceptance, or continue with opaque context after a confirmed acceptance commit.
#[pyclass(name = "RowRegistrationDecision", frozen)]
pub struct RowRegistrationDecisionPy {
	continued: bool,
	data: Zeroizing<Vec<u8>>,
}

#[pymethods]
impl RowRegistrationDecisionPy {
	#[staticmethod]
	fn return_result(data: &[u8]) -> Self {
		Self {
			continued: false,
			data: Zeroizing::new(data.to_vec()),
		}
	}
	#[staticmethod]
	fn continue_registration(data: &[u8]) -> Self {
		Self {
			continued: true,
			data: Zeroizing::new(data.to_vec()),
		}
	}
}

/// A trusted callback-scoped session. Methods reject use after callback return. Pending native outputs must not be published before the outer call succeeds. Native operations are limited to one attempted operation, including rejection; method failures abort the active transaction even if caught. Do not reenter the owning server.
#[pyclass(name = "RowSession", frozen)]
pub struct RowSessionPy {
	// Accessible only while the enclosing native callback holds the original mutable borrow.
	session: Mutex<Option<SessionAccess>>,
	// Set by any rejected concurrent, reentrant or cross-thread use; it aborts the transaction.
	misused: AtomicBool,
	errors: Errors,
}

// The callback's session, usable only on the thread running that callback. The exposed address
// keeps the class Send and Sync without an unsafe impl; it is dereferenced only after the thread
// check, while the native callback that owns the borrow is still on the stack.
struct SessionAccess {
	owner: ThreadId,
	address: usize,
}

impl RowSessionPy {
	fn with_native<T>(
		&self,
		py: Python<'_>,
		operation: impl FnOnce(&mut RowSession<'static>) -> Result<T, RowError>,
	) -> PyResult<T> {
		let Ok(slot) = self.session.try_lock() else {
			// Another call is active (reentry from a store callback) or one panicked.
			self.misused.store(true, Ordering::Relaxed);
			return Err(PyRuntimeError::new_err("row session is already in use"));
		};
		let access = slot
			.as_ref()
			.ok_or_else(|| PyRuntimeError::new_err("row session callback has ended"))?;
		if access.owner != thread::current().id() {
			self.misused.store(true, Ordering::Relaxed);
			return Err(PyRuntimeError::new_err(
				"row session used outside its callback thread",
			));
		}
		let session = ptr::with_exposed_provenance_mut::<RowSession<'static>>(access.address);
		let output = operation(unsafe { &mut *session });
		drop(slot);
		self.result(py, output)
	}

	fn result<T>(&self, py: Python<'_>, output: Result<T, RowError>) -> PyResult<T> {
		output.map_err(|error| {
			let cause = self
				.errors
				.lock()
				.unwrap_or_else(|e| e.into_inner())
				.as_ref()
				.map(|error| error.clone_ref(py));
			exception(py, error, cause)
		})
	}
}

#[pymethods]
impl RowSessionPy {
	fn load(&self, py: Python<'_>, key: &[u8]) -> PyResult<Option<Py<PyBytes>>> {
		self.with_native(py, |session| session.load_application(key))
			.map(|value| value.map(|bytes| PyBytes::new(py, &bytes).unbind()))
	}
	fn store(&self, py: Python<'_>, key: &[u8], value: &[u8]) -> PyResult<()> {
		self.with_native(py, |session| session.store_application(key, value))
	}
	fn encrypt_to_beacon(
		&self,
		py: Python<'_>,
		data: &[u8],
		kid: u64,
	) -> PyResult<RowTransitionPy> {
		let output = self.with_native(py, |session| session.encrypt_message(data, kid))?;
		RowTransitionPy::from_native(py, output)
	}
	fn decrypt_beacon_message(&self, py: Python<'_>, data: &[u8]) -> PyResult<RowTransitionPy> {
		let output = self.with_native(py, |session| session.decrypt_message(data))?;
		RowTransitionPy::from_native(py, output)
	}
	fn accept_registration(&self, py: Python<'_>, data: &[u8]) -> PyResult<bool> {
		self.with_native(py, |session| session.accept_registration(data))
	}
	#[pyo3(signature = (initial_message=None))]
	fn complete_registration(
		&self,
		py: Python<'_>,
		initial_message: Option<&[u8]>,
	) -> PyResult<RowTransitionPy> {
		let output =
			self.with_native(py, |session| session.complete_registration(initial_message))?;
		RowTransitionPy::from_native(py, output)
	}
}

fn application_callback<T>(
	py: Python<'_>,
	session: &mut RowSession<'_>,
	errors: &Errors,
	callback: impl FnOnce(Py<RowSessionPy>) -> PyResult<T>,
) -> Result<T, RowError> {
	let output = (|| {
		let address = (session as *mut RowSession<'_>)
			.cast::<RowSession<'static>>()
			.expose_provenance();
		let temporary = Py::new(
			py,
			RowSessionPy {
				session: Mutex::new(Some(SessionAccess {
					owner: thread::current().id(),
					address,
				})),
				misused: AtomicBool::new(false),
				errors: Arc::clone(errors),
			},
		)?;
		let output = callback(temporary.clone_ref(py));
		// Only this thread's calls can hold the slot while Python code runs, and they have all
		// returned; other threads hold it only briefly under the GIL, which this thread holds.
		// Invalidating the retained wrapper prevents stale access.
		let wrapper = temporary.get();
		*wrapper
			.session
			.lock()
			.unwrap_or_else(|error| error.into_inner()) = None;
		if wrapper.misused.load(Ordering::Relaxed) && output.is_ok() {
			return Err(PyRuntimeError::new_err(
				"row session was used concurrently, reentrantly or outside its callback thread",
			));
		}
		output
	})();
	output.map_err(|error| {
		let mut cause = errors.lock().unwrap_or_else(|error| error.into_inner());
		if cause.is_none() {
			*cause = Some(error);
		}
		RowError::Storage("application callback failed".into())
	})
}

/// An optional bounded decoded-peer cache backed by the authoritative database. An optional store.expect(key, expected) callback can stage exact-value conditions instead of loading warm peers. A capacity of zero disables caching.
#[pyclass(name = "BeaconCryptCachedRowServer", extends = RowServerPy)]
pub struct CachedRowServerPy;

#[pymethods]
impl CachedRowServerPy {
	#[staticmethod]
	#[pyo3(signature = (kid, id_seed, mldsa_seed, store, lineage_bytes, cache_capacity))]
	fn create(
		py: Python<'_>,
		kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		store: Py<PyAny>,
		lineage_bytes: &[u8],
		cache_capacity: usize,
	) -> PyResult<Py<Self>> {
		let lineage = lineage(lineage_bytes)?;
		let base = RowServerPy::construct(py, store, |store| {
			CachedRowServer::create(kid, id_seed, mldsa_seed, store, lineage, cache_capacity)
				.map(BindingRowServer::Cached)
		})?;
		Py::new(py, (Self, base))
	}
	#[staticmethod]
	fn open(
		py: Python<'_>,
		store: Py<PyAny>,
		lineage_bytes: &[u8],
		cache_capacity: usize,
	) -> PyResult<Py<Self>> {
		let lineage = lineage(lineage_bytes)?;
		let base = RowServerPy::construct(py, store, |store| {
			CachedRowServer::open(store, lineage, cache_capacity).map(BindingRowServer::Cached)
		})?;
		Py::new(py, (Self, base))
	}
}
