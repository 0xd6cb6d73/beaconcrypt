// SPDX-License-Identifier: 0BSD

use std::marker::PhantomData;

#[cfg(feature = "pqxdh")]
use libsodium_rs::{crypto_kem, crypto_kx, crypto_sign};

use crate::shared::{KexDerivedSecret, RatchetManager, roles};

#[cfg(feature = "pqxdh")]
type KemCiphertext = crypto_kem::mlkem768::Ciphertext;
#[cfg(feature = "pqxdh")]
type SignVerificationKey = crypto_sign::PublicKey;
#[cfg(feature = "pqxdh")]
type EphemeralKexPubKey = crypto_kx::PublicKey;
pub struct RegResponse {
	pub serialized: Vec<u8>,
	pub kid: u64,
}

pub struct RegistrationOutput {
	pub kem_ciphertext: KemCiphertext,
	pub derived_secret: KexDerivedSecret,
	pub ephemeral: EphemeralKexPubKey,
	pub public_key: SignVerificationKey,
}

pub struct StateUpdate<Role: roles::ChainKey> {
	pub kid: u64,
	/// The sequence number of the key consumed by this operation.
	pub seq: u64,
	pub state: RatchetManager,
	pub data: Vec<u8>,
	pub(crate) _role: PhantomData<Role>,
}

pub type SendState = StateUpdate<roles::ChainSendKey>;
pub type RecvState = StateUpdate<roles::ChainRecvKey>;

pub trait ProviderServer {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput>;

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse>;

	/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
	/// and complete ratchet state for `kid`.
	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState>;
	/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
	/// and complete ratchet state for `kid` as a JSON string.
	fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`.
	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`
	/// as a JSON string.
	fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String>;
	/// Export the current ratchet state as JSON for all known principals
	fn export_state(&self) -> Option<String>;
	/// Restore a server from serialized state, returning `None` if the identity seed or state is invalid.
	fn try_from_state(server_kid: u64, id_seed: Option<&[u8]>, server_state: &str) -> Option<Self>
	where
		Self: Sized;
	/// Restore a server from serialized state.
	///
	/// # Panics
	///
	/// Panics if the identity seed or serialized state is invalid.
	fn from_state(server_kid: u64, id_seed: Option<&[u8]>, server_state: String) -> Self
	where
		Self: Sized,
	{
		Self::try_from_state(server_kid, id_seed, &server_state)
			.expect("failed to restore server state")
	}
}
