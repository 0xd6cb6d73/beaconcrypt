// SPDX-License-Identifier: 0BSD

//! Shared dispatch for cached and uncached foreign-language row handles.

use crate::{
	CachedRowServer, Decrypted, Encrypted, RegResponse, RowError, RowRegistrationDecision,
	RowRegistrationError, RowServer, RowSession, RowStore,
};

pub(crate) enum BindingRowServer<S: RowStore> {
	Rows(RowServer<S>),
	Cached(CachedRowServer<S>),
}

macro_rules! dispatch {
	($owner:ident, $method:ident($($argument:expr),* $(,)?)) => {
		match $owner {
			Self::Rows(server) => server.$method($($argument),*),
			Self::Cached(server) => server.$method($($argument),*),
		}
	};
}

impl<S: RowStore> BindingRowServer<S> {
	pub(crate) fn identity_pk(&self) -> &libsodium_rs::crypto_sign::PublicKey {
		dispatch!(self, identity_pk())
	}
	pub(crate) fn mldsa_public_key(&self) -> [u8; crate::MLDSA_PUBLIC_KEY_LEN] {
		dispatch!(self, mldsa_public_key())
	}
	#[cfg(feature = "pybinds")]
	pub(crate) fn lineage(&self) -> crate::SnapshotLineage {
		dispatch!(self, lineage())
	}
	pub(crate) fn register_beacon(
		&mut self,
		bytes: &[u8],
		initial: Option<&[u8]>,
	) -> Result<Option<RegResponse>, RowError> {
		dispatch!(self, register_beacon(bytes, initial))
	}
	pub(crate) fn encrypt_message(
		&mut self,
		bytes: &[u8],
		kid: u64,
	) -> Result<Option<Encrypted>, RowError> {
		dispatch!(self, encrypt_message(bytes, kid))
	}
	pub(crate) fn decrypt_message(&mut self, bytes: &[u8]) -> Result<Option<Decrypted>, RowError> {
		dispatch!(self, decrypt_message(bytes))
	}
	pub(crate) fn transaction<T>(
		&mut self,
		operation: impl FnOnce(&mut RowSession<'_>) -> Result<T, RowError>,
	) -> Result<T, RowError> {
		dispatch!(self, transaction(operation))
	}
	pub(crate) fn registration_transaction<A, T>(
		&mut self,
		accept: impl FnOnce(&mut RowSession<'_>) -> Result<RowRegistrationDecision<A, T>, RowError>,
		complete: impl FnOnce(&mut RowSession<'_>, A) -> Result<T, RowError>,
	) -> Result<T, RowRegistrationError> {
		dispatch!(self, registration_transaction(accept, complete))
	}
	pub(crate) fn cache_capacity(&self) -> usize {
		match self {
			Self::Rows(_) => 0,
			Self::Cached(server) => server.cache_capacity(),
		}
	}
	pub(crate) fn cached_peer_count(&self) -> usize {
		match self {
			Self::Rows(_) => 0,
			Self::Cached(server) => server.cached_peer_count(),
		}
	}
	pub(crate) fn clear_cache(&mut self) {
		if let Self::Cached(server) = self {
			server.clear_cache();
		}
	}
}
