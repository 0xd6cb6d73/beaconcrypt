// SPDX-License-Identifier: 0BSD

use crate::persistence::BindingServer;
use crate::server::{RecvState, SendState};
use crate::{Beacon as PqxdhBeacon, ProviderBeacon, RegResponse};
use pyo3::exceptions::PyValueError;
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

#[pyclass(name = "BeaconCryptServer")]
pub struct Server {
	_0: BindingServer,
}

#[pymethods]
impl Server {
	#[new]
	fn new(kid: u64, id_seed: Option<&[u8]>) -> PyResult<Self> {
		BindingServer::create_binding(kid, id_seed)
			.map(|server| Self { _0: server })
			.map_err(|error| PyValueError::new_err(error.to_string()))
	}

	/// Restore a server from trusted plaintext checkpoint bytes.
	///
	/// The caller must reject stale or untrusted checkpoints. Exported bytes do not authenticate
	/// themselves and cannot detect rollback to an older export. Restoration advances the
	/// generation, so export and save the returned server immediately before using it.
	#[staticmethod]
	fn from_state(state: Vec<u8>) -> PyResult<Self> {
		BindingServer::restore_binding(state)
			.map(|server| Self { _0: server })
			.map_err(|error| PyValueError::new_err(error.to_string()))
	}

	/// Export the current plaintext checkpoint.
	///
	/// Save it immediately after every state-changing call and before using that call's output.
	fn export_state(&self) -> PyResult<Vec<u8>> {
		self._0
			.export_binding_state()
			.map_err(|error| PyValueError::new_err(error.to_string()))
	}

	fn register_beacon(
		&mut self,
		reg_buffer: &[u8],
		initial_message: Option<&[u8]>,
	) -> Option<RegResponsePy> {
		match self._0.get_shared_secret(reg_buffer).ok().flatten() {
			Some(secrets) => self
				._0
				.build_registration_response(secrets, initial_message)
				.ok()
				.flatten()
				.map(|response| response.into()),
			None => None,
		}
	}

	fn decrypt_beacon_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		self._0
			.decrypt_message(&data)
			.ok()
			.flatten()
			.map(|decrypted| decrypted.plaintext)
	}

	fn encrypt_to_beacon(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
		self._0
			.encrypt_message(&data, kid)
			.ok()
			.flatten()
			.map(|encrypted| encrypted.ciphertext)
	}

	fn encrypt_and_update(&mut self, data: Vec<u8>, kid: u64) -> Option<EncryptStatePy> {
		self._0
			.encrypt_and_update(&data, kid)
			.ok()
			.flatten()
			.map(EncryptStatePy::from)
	}

	fn encrypt_and_update_json(&mut self, data: Vec<u8>, kid: u64) -> Option<String> {
		self._0.encrypt_and_update_json(&data, kid).ok().flatten()
	}

	fn decrypt_and_update(&mut self, data: Vec<u8>) -> Option<EncryptStatePy> {
		self._0
			.decrypt_and_update(&data)
			.ok()
			.flatten()
			.map(EncryptStatePy::from)
	}

	fn decrypt_and_update_json(&mut self, data: Vec<u8>) -> Option<String> {
		self._0.decrypt_and_update_json(&data).ok().flatten()
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
	fn new(server_kid: u64, server_id_pk: &[u8]) -> Self {
		Self {
			_0: PqxdhBeacon::new(server_kid, server_id_pk),
		}
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
