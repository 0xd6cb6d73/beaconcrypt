// SPDX-License-Identifier: 0BSD

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
				.build_registration_response(secrets, initial_message)
				.map(|response| response.into()),
			None => None,
		}
	}

	fn decrypt_beacon_message(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
		self._0.decrypt_message(&data, kid)
	}

	fn decrypt_beacon_message_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		match self._0.verify_signature(&data) {
			Some(verified) => self.decrypt_beacon_message(verified.data, verified.key_id),
			None => None,
		}
	}

	fn encrypt_to_beacon(&mut self, data: Vec<u8>, kid: u64) -> Option<Vec<u8>> {
		self._0.encrypt_message(&data, kid)
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
	fn new(server_kid: u64, server_id_pk: &[u8]) -> Self {
		Self {
			_0: BeaconCryptPqxdh::new(true, server_kid, Some(server_id_pk), None),
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
		self._0.decrypt_message(&data, srv_seq)
	}

	fn decrypt_server_message_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		match self._0.verify_signature(&data) {
			Some(verified) => self.decrypt_server_message(verified.data),
			None => None,
		}
	}

	fn encrypt_message_to_server(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		let srv_seq = self._0.server_kid();
		self._0.encrypt_message(&data, srv_seq)
	}

	fn encrypt_to_server_signed(&mut self, data: Vec<u8>) -> Option<Vec<u8>> {
		match self.encrypt_message_to_server(data) {
			Some(ciphertext) => self._0.sign_message(ciphertext.as_slice()),
			None => None,
		}
	}
}
