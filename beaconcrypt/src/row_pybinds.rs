// SPDX-License-Identifier: 0BSD

use std::sync::{Arc, Mutex};

use pyo3::{
	class::{PyTraverseError, PyVisit},
	exceptions::{PyRuntimeError, PyValueError},
	prelude::*,
	types::PyBytes,
};

use crate::pybinds::RegResponsePy;
use crate::{RowError, RowServer, RowStore, RowTransaction, SnapshotLineage};

pyo3::create_exception!(beaconcrypt, RowPersistenceError, PyValueError);

type Object = Arc<Mutex<Option<Py<PyAny>>>>;
type Errors = Arc<Mutex<Option<PyErr>>>;
type NativeServer = RowServer<Box<dyn RowStore + Send + Sync>>;

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
	value.map_err(|error| {
		let code = match &error {
			RowError::Storage(_) => "storage",
			RowError::Conflict => "conflict",
			RowError::MissingIdentity => "missing_identity",
			RowError::InvalidRow => "invalid_row",
			RowError::GenerationExhausted => "generation_exhausted",
			RowError::Initialization => "initialization",
			RowError::OutputEncoding => "encoding",
		};
		let exception = RowPersistenceError::new_err(error.to_string());
		if let Err(error) = exception.value(py).setattr("code", code) {
			return error;
		}
		exception.set_cause(py, cause);
		exception
	})
}

fn lineage(bytes: &[u8]) -> PyResult<SnapshotLineage> {
	Ok(SnapshotLineage::from_bytes(bytes.try_into().map_err(
		|_| PyValueError::new_err("lineage must contain 32 bytes"),
	)?))
}

/// A database-backed server that loads and commits only the selected peer. Store callbacks must implement a serializable durable transaction and raise exceptions on failure. Callbacks cannot reenter their server.
#[pyclass(name = "BeaconCryptRowServer")]
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
			RowServer::create(kid, id_seed, mldsa_seed, store, lineage)
		})
	}

	#[staticmethod]
	fn open(py: Python<'_>, store: Py<PyAny>, lineage_bytes: &[u8]) -> PyResult<Self> {
		let lineage = lineage(lineage_bytes)?;
		Self::construct(py, store, |store| RowServer::open(store, lineage))
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

	fn encrypt_to_beacon(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
		kid: u64,
	) -> PyResult<Option<Vec<u8>>> {
		let output = self.native()?.encrypt_message(&data, kid);
		result(py, output, &self.errors).map(|output| output.map(|output| output.ciphertext))
	}

	fn decrypt_beacon_message(
		&mut self,
		py: Python<'_>,
		data: Vec<u8>,
	) -> PyResult<Option<Vec<u8>>> {
		let output = self.native()?.decrypt_message(&data);
		result(py, output, &self.errors).map(|output| output.map(|output| output.plaintext))
	}
}
