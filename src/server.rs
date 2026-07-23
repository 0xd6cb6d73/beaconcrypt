// SPDX-License-Identifier: 0BSD

#[cfg(feature = "pqxdh")]
use libsodium_rs::{crypto_kem, crypto_kx, crypto_sign};

use crate::shared::{KdfState, KexDerivedSecret};

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

pub struct EncryptState {
	pub kid: u64,
	pub key: KdfState,
	pub data: Vec<u8>,
}

pub trait ProviderServer {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput>;

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse>;

	/// Encrypt some bytes to `kid` and return the ciphertext, `kid` and new state of the send keychain for `kid`
	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<EncryptState>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid` and new state of the recv keychain for `kid`
	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<EncryptState>;
}
