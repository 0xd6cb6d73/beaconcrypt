// SPDX-License-Identifier: 0BSD

//! Registration bindings retained by the production protocol roles.
//!
//! Hashing and signature verification remain interpreter obligations. Constructors
//! receive their results explicitly; these types preserve the selected pins, request
//! digest and ordered fingerprints rather than establishing primitive authenticity.

use crate::authentication::{MLDSA_PUBLIC_KEY_LEN, TRANSCRIPT_HASH_LEN, bind_associated_data};
use crate::pqxdh::{
	ASSOCIATED_DATA_SIZE, SIGN_PUBLIC_KEY_SIZE, ServerBinding, build_associated_data,
};

/// The complete server pin selected before a registration starts.
#[derive(Clone, Copy)]
pub struct ServerAuthenticationPin {
	binding: ServerBinding,
	public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
	fingerprint: [u8; TRANSCRIPT_HASH_LEN],
}

impl ServerAuthenticationPin {
	/// The interpreter must supply the hash of this exact ML-DSA public key.
	pub const fn new(
		binding: ServerBinding,
		public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
		fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	) -> Self {
		Self {
			binding,
			public_key,
			fingerprint,
		}
	}

	pub const fn binding(&self) -> ServerBinding {
		self.binding
	}

	pub const fn public_key(&self) -> &[u8; MLDSA_PUBLIC_KEY_LEN] {
		&self.public_key
	}

	pub const fn fingerprint(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.fingerprint
	}
}

/// One emitted or authenticated request, including its exact final record AD.
///
/// This phase is not `Clone` or `Copy`. Its request digest is discarded when it
/// becomes an established session, because subsequent records do not use it.
pub struct RegistrationBinding {
	server_pin: ServerAuthenticationPin,
	init_hash: [u8; TRANSCRIPT_HASH_LEN],
	beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
	beacon_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
}

impl RegistrationBinding {
	/// Digests and verified field provenance must come from the same request.
	pub fn new(
		server_pin: ServerAuthenticationPin,
		init_hash: [u8; TRANSCRIPT_HASH_LEN],
		beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
		beacon_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	) -> Self {
		let base = build_associated_data(
			server_pin.binding.identity_public_key,
			beacon_identity_public_key,
		);
		Self {
			associated_data: bind_associated_data(
				&base,
				&server_pin.fingerprint,
				&beacon_fingerprint,
			),
			server_pin,
			init_hash,
			beacon_identity_public_key,
			beacon_fingerprint,
		}
	}

	pub const fn init_hash(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.init_hash
	}

	pub const fn server_pin(&self) -> &ServerAuthenticationPin {
		&self.server_pin
	}

	pub const fn associated_data(&self) -> &[u8; ASSOCIATED_DATA_SIZE] {
		&self.associated_data
	}

	/// Reject a pending request presented to a differently pinned server.
	pub fn matches_server(&self, current: &ServerAuthenticationPin) -> bool {
		self.server_pin.binding.identity_key_id == current.binding.identity_key_id
			&& self.server_pin.binding.identity_public_key == current.binding.identity_public_key
			&& self.server_pin.public_key == current.public_key
			&& self.server_pin.fingerprint == current.fingerprint
	}

	/// Retain the exact registration AD without reconstructing it in the adapter.
	pub const fn finish(self, assigned_key_id: u64) -> SessionBinding {
		SessionBinding {
			server_binding: self.server_pin.binding,
			assigned_key_id,
			beacon_identity_public_key: self.beacon_identity_public_key,
			server_fingerprint: self.server_pin.fingerprint,
			beacon_fingerprint: self.beacon_fingerprint,
			associated_data: self.associated_data,
		}
	}
}

/// Immutable authenticated peer metadata and the final populated AD for records.
#[derive(Clone, Copy)]
pub struct SessionBinding {
	server_binding: ServerBinding,
	assigned_key_id: u64,
	beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
	server_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	beacon_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
}

impl SessionBinding {
	/// Reconstruct a binding from authenticated persistence metadata.
	///
	/// The caller establishes snapshot integrity and provenance. This constructor
	/// preserves the existing persistence representation and does not authenticate it.
	pub fn from_trusted_metadata(
		server_binding: ServerBinding,
		assigned_key_id: u64,
		beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
		server_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
		beacon_fingerprint: [u8; TRANSCRIPT_HASH_LEN],
	) -> Self {
		let base = build_associated_data(
			server_binding.identity_public_key,
			beacon_identity_public_key,
		);
		Self {
			server_binding,
			assigned_key_id,
			beacon_identity_public_key,
			server_fingerprint,
			beacon_fingerprint,
			associated_data: bind_associated_data(&base, &server_fingerprint, &beacon_fingerprint),
		}
	}

	pub const fn server_binding(&self) -> ServerBinding {
		self.server_binding
	}

	pub const fn assigned_key_id(&self) -> u64 {
		self.assigned_key_id
	}

	pub const fn beacon_identity_public_key(&self) -> &[u8; SIGN_PUBLIC_KEY_SIZE] {
		&self.beacon_identity_public_key
	}

	pub const fn server_fingerprint(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.server_fingerprint
	}

	pub const fn beacon_fingerprint(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.beacon_fingerprint
	}

	pub const fn associated_data(&self) -> &[u8; ASSOCIATED_DATA_SIZE] {
		&self.associated_data
	}
}
