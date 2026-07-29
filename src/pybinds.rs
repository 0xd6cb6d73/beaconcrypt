// SPDX-License-Identifier: 0BSD

use crate::server::{RecvState, SendState};
use crate::{BeaconCryptPqxdh, CryptoProvider, ProviderBeacon, ProviderServer, RegResponse};
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

	/// Return the complete ratchet state as JSON.
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

impl TryFrom<SendState> for EncryptStatePy {
	type Error = serde_json::Error;

	fn try_from(value: SendState) -> Result<Self, Self::Error> {
		let state = serde_json::to_string(&value.state)?;
		Ok(Self {
			data: value.data,
			state,
			kid: value.kid,
			seq: value.seq,
		})
	}
}

impl TryFrom<RecvState> for EncryptStatePy {
	type Error = serde_json::Error;

	fn try_from(value: RecvState) -> Result<Self, Self::Error> {
		let state = serde_json::to_string(&value.state)?;
		Ok(Self {
			data: value.data,
			state,
			kid: value.kid,
			seq: value.seq,
		})
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

	#[staticmethod]
	fn from_state(kid: u64, id_seed: Option<&[u8]>, server_state: &str) -> PyResult<Self> {
		<BeaconCryptPqxdh as ProviderServer>::try_from_state(kid, id_seed, server_state)
			.map(|provider| Self { _0: provider })
			.ok_or_else(|| PyValueError::new_err("invalid server identity seed or state"))
	}

	fn register_beacon(
		&mut self,
		reg_buffer: &[u8],
		initial_message: Option<&[u8]>,
	) -> Option<RegResponsePy> {
		match self._0.get_shared_secret(reg_buffer) {
			Some(secrets) => self
				._0
				.build_registration_response(secrets, initial_message)
				.map(|response| response.into()),
			None => None,
		}
	}

	fn decrypt_beacon_message(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		self._0
			.decrypt_message(&data)
			.map(|decrypted| decrypted.plaintext)
	}

	fn encrypt_to_beacon(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
		self._0
			.encrypt_message(&data, kid)
			.map(|encrypted| encrypted.ciphertext)
	}

	fn encrypt_and_update(&mut self, data: Vec<u8>, kid: u64) -> Option<EncryptStatePy> {
		self._0
			.encrypt_and_update(&data, kid)
			.and_then(|state| state.try_into().ok())
	}

	fn encrypt_and_update_json(&mut self, data: Vec<u8>, kid: u64) -> Option<String> {
		self._0.encrypt_and_update_json(&data, kid)
	}

	fn decrypt_and_update(&mut self, data: Vec<u8>) -> Option<EncryptStatePy> {
		self._0
			.decrypt_and_update(&data)
			.and_then(|state| state.try_into().ok())
	}

	fn decrypt_and_update_json(&mut self, data: Vec<u8>) -> Option<String> {
		self._0.decrypt_and_update_json(&data)
	}

	fn export_state(&self) -> Option<String> {
		self._0.export_state()
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
	fn new(server_kid: u64, server_id_pk: &[u8]) -> Self {
		Self {
			_0: BeaconCryptPqxdh::new(true, server_kid, Some(server_id_pk), None),
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
		let srv_seq = self._0.server_kid();
		self._0
			.encrypt_message(&data, srv_seq)
			.map(|encrypted| encrypted.ciphertext)
	}
}
