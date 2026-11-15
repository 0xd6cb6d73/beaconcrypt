// SPDX-License-Identifier: 0BSD

//! Pending and completed registration bindings retained by the production roles.
//!
//! Primitive hashing and Server signature verification remain interpreter obligations.

use crate::authentication::{
	AdResponseFields, MLDSA_PUBLIC_KEY_LEN, OwnedInitFields, RECORD_AD_TRANSCRIPT_LEN,
	TRANSCRIPT_HASH_LEN, assemble_associated_data, build_record_ad_transcript,
};
use crate::pqxdh::{ASSOCIATED_DATA_SIZE, SIGN_PUBLIC_KEY_SIZE, ServerBinding};

/// The exact Server binding and ML-DSA pin selected before a registration starts.
#[derive(Clone, Copy)]
pub struct ServerAuthenticationPin {
	binding: ServerBinding,
	public_key: [u8; MLDSA_PUBLIC_KEY_LEN],
}

impl ServerAuthenticationPin {
	pub const fn new(binding: ServerBinding, public_key: [u8; MLDSA_PUBLIC_KEY_LEN]) -> Self {
		Self {
			binding,
			public_key,
		}
	}

	pub const fn binding(&self) -> ServerBinding {
		self.binding
	}

	pub const fn public_key(&self) -> &[u8; MLDSA_PUBLIC_KEY_LEN] {
		&self.public_key
	}
}

/// One emitted or validated request with its exact attached-signature field buffers.
///
/// This affine phase has no final AD: the response fields and assigned ID do not yet exist.
pub struct RegistrationBinding {
	server_pin: ServerAuthenticationPin,
	init_hash: [u8; TRANSCRIPT_HASH_LEN],
	init_fields: OwnedInitFields,
}

impl RegistrationBinding {
	pub fn new(
		server_pin: ServerAuthenticationPin,
		init_hash: [u8; TRANSCRIPT_HASH_LEN],
		init_fields: OwnedInitFields,
	) -> Self {
		Self {
			server_pin,
			init_hash,
			init_fields,
		}
	}

	pub const fn init_hash(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.init_hash
	}

	pub const fn server_pin(&self) -> &ServerAuthenticationPin {
		&self.server_pin
	}

	pub fn ad_transcript(&self, response: AdResponseFields<'_>) -> [u8; RECORD_AD_TRANSCRIPT_LEN] {
		build_record_ad_transcript(self.init_fields.fields(), response)
	}

	pub fn matches_server(&self, current: &ServerAuthenticationPin) -> bool {
		self.server_pin.binding.identity_key_id == current.binding.identity_key_id
			&& self.server_pin.binding.identity_public_key == current.binding.identity_public_key
			&& self.server_pin.public_key == current.public_key
	}

	/// Called only by the owned AD-hash continuation after its exact digest reply.
	pub(crate) fn complete(
		self,
		transcript_hash: [u8; TRANSCRIPT_HASH_LEN],
	) -> CompletedRegistrationBinding {
		CompletedRegistrationBinding {
			server_pin: self.server_pin,
			init_hash: self.init_hash,
			beacon_identity_public_key: self.init_fields.identity_public_key(),
			session_transcript_hash: transcript_hash,
			associated_data: assemble_associated_data(&transcript_hash),
		}
	}
}

/// Final AD retained after the exact transcript-hash effect; request field buffers are dropped.
pub struct CompletedRegistrationBinding {
	server_pin: ServerAuthenticationPin,
	init_hash: [u8; TRANSCRIPT_HASH_LEN],
	beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
	session_transcript_hash: [u8; TRANSCRIPT_HASH_LEN],
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
}

impl CompletedRegistrationBinding {
	pub const fn init_hash(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.init_hash
	}
	pub const fn server_pin(&self) -> &ServerAuthenticationPin {
		&self.server_pin
	}
	pub const fn associated_data(&self) -> &[u8; ASSOCIATED_DATA_SIZE] {
		&self.associated_data
	}

	pub const fn finish(self, assigned_key_id: u64) -> SessionBinding {
		SessionBinding {
			server_binding: self.server_pin.binding,
			assigned_key_id,
			beacon_identity_public_key: self.beacon_identity_public_key,
			session_transcript_hash: self.session_transcript_hash,
			associated_data: self.associated_data,
		}
	}
}

/// Immutable peer metadata and the identical complete AD used by every record.
#[derive(Clone, Copy)]
pub struct SessionBinding {
	server_binding: ServerBinding,
	assigned_key_id: u64,
	beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
	session_transcript_hash: [u8; TRANSCRIPT_HASH_LEN],
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
}

impl SessionBinding {
	/// Restore authenticated persistence metadata under the current incompatible state version.
	/// The caller establishes integrity and provenance; the fixed context is core-owned.
	pub fn from_trusted_metadata(
		server_binding: ServerBinding,
		assigned_key_id: u64,
		beacon_identity_public_key: [u8; SIGN_PUBLIC_KEY_SIZE],
		session_transcript_hash: [u8; TRANSCRIPT_HASH_LEN],
	) -> Self {
		Self {
			server_binding,
			assigned_key_id,
			beacon_identity_public_key,
			session_transcript_hash,
			associated_data: assemble_associated_data(&session_transcript_hash),
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
	pub const fn session_transcript_hash(&self) -> &[u8; TRANSCRIPT_HASH_LEN] {
		&self.session_transcript_hash
	}
	pub const fn associated_data(&self) -> &[u8; ASSOCIATED_DATA_SIZE] {
		&self.associated_data
	}
}
