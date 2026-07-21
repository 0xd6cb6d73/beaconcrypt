// SPDX-License-Identifier: 0BSD

#[cfg(feature = "server")]
use crate::error::DecodingError;
use crate::error::EncodingError;
#[cfg(feature = "pqxdh")]
use crate::pqxdh::AD_SIZE;
use crate::{cryptoframe_capnp, protogram_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::utils::memcmp;
use libsodium_rs::{crypto_aead, crypto_generichash, crypto_kdf};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::vec;
use zeroize::{Zeroize, Zeroizing};

pub const KEX_KDF_OUT_LEN: usize = 32usize;
pub const KDF_STATE_SIZE: usize = 32usize;
pub const SYM_RATCHET_INFO: &[u8; 41] = b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305";
/// crypto_aead::chacha20poly1305_ietf::KEYBYTES
pub const AEAD_KEY_LEN: usize = 32;
/// crypto_aead::chacha20poly1305_ietf::NPUBBYTES
pub const AEAD_NONCE_LEN: usize = 12;
pub const KDF_RATCHET_OUTPUT_LEN: usize = AEAD_KEY_LEN + KDF_STATE_SIZE + AEAD_NONCE_LEN;
/// crypto_scalarmult::BYTES
#[cfg(feature = "pqxdh")]
pub const DH_OUT_LEN: usize = 32;
// the maximum amounts of out-of-order messages we tolerate
pub const RATCHET_MAX_GAP: u64 = 50;
#[cfg(feature = "pqxdh")]
pub const ED25519_SEED_SIZE: usize = 32;
#[cfg(feature = "server")]
/// Byte sequence used to test successful keychain derivation during registration. Used only if the server doesn't provide an initial message
pub const REGISTRATION_WITNESS: &[u8; 1] = &[0xFF; 1];
pub const COMMITMENT_SIZE: usize = 64;

#[repr(u8)]
#[derive(PartialEq)]
pub enum SignType {
	Undefined = 0,
	Ed25519 = 1,
	MlDsa87 = 2,
}

impl From<SignType> for u8 {
	fn from(value: SignType) -> Self {
		match value {
			SignType::Undefined => 0,
			SignType::Ed25519 => 1,
			SignType::MlDsa87 => 2,
		}
	}
}

impl From<u8> for SignType {
	fn from(value: u8) -> Self {
		match value {
			1 => Self::Ed25519,
			2 => Self::MlDsa87,
			_ => Self::Undefined,
		}
	}
}

#[repr(u8)]
#[derive(PartialEq)]
pub enum KemType {
	Undefined = 0,
	MlKem768 = 1,
	X25519 = 2,
	MlKem1024 = 3,
}

impl From<KemType> for u8 {
	fn from(value: KemType) -> Self {
		match value {
			KemType::Undefined => 0,
			KemType::MlKem768 => 1,
			KemType::X25519 => 2,
			KemType::MlKem1024 => 3,
		}
	}
}

impl From<u8> for KemType {
	fn from(value: u8) -> Self {
		match value {
			1 => Self::MlKem768,
			2 => Self::X25519,
			3 => Self::MlKem1024,
			_ => Self::Undefined,
		}
	}
}

pub fn encode_sign(sign_type: SignType, pk_bytes: &[u8]) -> Result<Vec<u8>, EncodingError> {
	match sign_type {
		SignType::Undefined => Err(EncodingError),
		_ => {
			let mut byt = Vec::from(pk_bytes);
			byt.insert(0, sign_type.into());
			Ok(byt)
		}
	}
}

#[cfg(feature = "server")]
pub fn decode_sign(encoded_pk: &[u8], expected: SignType) -> Result<Vec<u8>, DecodingError> {
	if encoded_pk.len() < 33 {
		return Err(DecodingError);
	}
	match SignType::from(encoded_pk[0]) {
		SignType::Undefined => Err(DecodingError),
		sign => {
			if sign != expected {
				return Err(DecodingError);
			}
			let mut key = vec![0u8; encoded_pk.len()];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
	}
}

#[cfg(feature = "beacon")]
pub fn encode_kem(kem_type: KemType, pk_bytes: &[u8]) -> Result<Vec<u8>, EncodingError> {
	match kem_type {
		KemType::Undefined => Err(EncodingError),
		_ => {
			let mut byt = Vec::from(pk_bytes);
			byt.insert(0, kem_type.into());
			Ok(byt)
		}
	}
}

#[cfg(feature = "server")]
pub fn decode_kem(encoded_pk: &[u8], expected: KemType) -> Result<Vec<u8>, DecodingError> {
	if encoded_pk.len() < 33 {
		return Err(DecodingError);
	}
	match KemType::from(encoded_pk[0]) {
		KemType::Undefined => Err(DecodingError),
		kem => {
			if kem != expected {
				return Err(DecodingError);
			}
			let mut key = vec![0u8; encoded_pk.len()];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
	}
}

mod systems {
	#[cfg(feature = "pqxdh")]
	pub struct X25519;
	pub struct Hkdf;
	#[cfg(feature = "server")]
	pub struct Pqxdh;
}
mod roles {
	pub struct ChainKey;
	pub struct DerivedSecret;
}

pub struct VerifiedMessage {
	pub data: Vec<u8>,
	pub key_id: u64,
}

// this design is stolen from https://github.com/celabshq/libcrux/issues/1390
pub struct SecretArr<const S: usize, System, Role> {
	data: Zeroizing<[u8; S]>,
	// what cryptosystem this is used in (X25519, ML-KEM...)
	_system: PhantomData<System>,
	// what role does this play within the given cryptosystem (signing key, KDF state..)
	_role: PhantomData<Role>,
}

impl<const S: usize, System, Role> From<[u8; S]> for SecretArr<S, System, Role> {
	fn from(value: [u8; S]) -> Self {
		SecretArr {
			data: value.into(),
			_system: PhantomData,
			_role: PhantomData,
		}
	}
}

/// `value` MUST be exactly the size expected by the type
impl<const S: usize, System, Role> From<Vec<u8>> for SecretArr<S, System, Role> {
	fn from(value: Vec<u8>) -> Self {
		if value.len() == S {
			SecretArr {
				data: value.as_array::<S>().unwrap().to_owned().into(),
				_system: PhantomData,
				_role: PhantomData,
			}
		} else {
			SecretArr::default()
		}
	}
}

impl<const S: usize, System, Role> Default for SecretArr<S, System, Role> {
	fn default() -> Self {
		SecretArr {
			data: [0u8; S].into(),
			_system: PhantomData,
			_role: PhantomData,
		}
	}
}

impl<const S: usize, System, Role> SecretArr<S, System, Role> {
	pub fn as_slice(&self) -> &[u8] {
		self.data.as_slice()
	}

	pub fn copy_from_slice(&mut self, src: &[u8]) {
		self.data.copy_from_slice(src);
	}

	#[cfg(feature = "server")]
	pub fn inner(&self) -> &Zeroizing<[u8; S]> {
		&self.data
	}
}

impl<const S: usize, System, Role> Clone for SecretArr<S, System, Role> {
	fn clone(&self) -> Self {
		Self {
			data: self.data.clone(),
			_system: self._system,
			_role: self._role,
		}
	}
}

#[cfg(feature = "pqxdh")]
pub type DhSecret = SecretArr<DH_OUT_LEN, systems::X25519, roles::DerivedSecret>;
pub type KdfState = SecretArr<KDF_STATE_SIZE, systems::Hkdf, roles::ChainKey>;
#[cfg(feature = "server")]
pub type KexDerivedSecret = SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>;

pub struct KeyMaterial {
	key: AeadKey,
	nonce: AeadNonce,
}

impl KeyMaterial {
	fn key(&self) -> &AeadKey {
		&self.key
	}

	fn nonce(&self) -> &AeadNonce {
		&self.nonce
	}
}

pub type AeadKey = crypto_aead::chacha20poly1305_ietf::Key;
pub type AeadNonce = crypto_aead::chacha20poly1305_ietf::Nonce;

struct KdfOutput {
	aead_key: AeadKey,
	kdf_state: KdfState,
	aead_nonce: AeadNonce,
}

impl From<[u8; KDF_RATCHET_OUTPUT_LEN]> for KdfOutput {
	fn from(mut value: [u8; KDF_RATCHET_OUTPUT_LEN]) -> Self {
		let mut key = [0u8; AEAD_KEY_LEN];
		key.copy_from_slice(&value[0..AEAD_KEY_LEN]);
		let mut iter: usize = AEAD_KEY_LEN;
		let mut state = [0u8; KDF_STATE_SIZE];
		state.copy_from_slice(&value[AEAD_KEY_LEN..AEAD_KEY_LEN + KDF_STATE_SIZE]);
		iter += KDF_STATE_SIZE;
		let mut nonce = [0u8; AEAD_NONCE_LEN];
		nonce.copy_from_slice(&value[iter..iter + AEAD_NONCE_LEN]);
		value.zeroize();
		Self {
			aead_key: key.into(),
			kdf_state: state.into(),
			aead_nonce: nonce.into(),
		}
	}
}

pub trait Ratchetable {
	fn ratchet(&mut self, info: &[u8]) -> KeyMaterial;
}

pub struct RatchetRoleSend;
pub struct RatchetRoleRecv;

pub struct Ratchet<Role> {
	state: KdfState,
	_role: PhantomData<Role>,
}

impl<Role> From<[u8; KDF_STATE_SIZE]> for Ratchet<Role> {
	fn from(value: [u8; KDF_STATE_SIZE]) -> Self {
		Self {
			state: value.into(),
			_role: PhantomData,
		}
	}
}

impl<Role> Ratchetable for Ratchet<Role> {
	fn ratchet(&mut self, info: &[u8]) -> KeyMaterial {
		let prk = crypto_kdf::hkdf::sha512::extract(None, self.state.as_slice()).unwrap();
		let out: KdfOutput =
			(*crypto_kdf::hkdf::sha512::expand(KDF_RATCHET_OUTPUT_LEN, Some(info), &prk)
				.unwrap()
				.as_array::<KDF_RATCHET_OUTPUT_LEN>()
				.unwrap())
			.into();
		self.state = out.kdf_state;
		KeyMaterial {
			key: out.aead_key,
			nonce: out.aead_nonce,
		}
	}
}
impl<Role> Default for Ratchet<Role> {
	fn default() -> Self {
		Self {
			state: [0u8; KDF_STATE_SIZE].into(),
			_role: PhantomData,
		}
	}
}

type SendChain = Ratchet<RatchetRoleSend>;
type RecvChain = Ratchet<RatchetRoleRecv>;

pub struct RatchetManager {
	/// current state of the KDF on the send chain
	send_key: SendChain,
	/// current state of the KDF on the recv chain
	recv_key: RecvChain,
	send_past: HashMap<u64, KeyMaterial>,
	send_ctr: u64,
	recv_past: HashMap<u64, KeyMaterial>,
	recv_ctr: u64,
	// role: PhantomData,
}

impl RatchetManager {
	pub fn new() -> Self {
		Self {
			send_key: SendChain::default(),
			recv_key: RecvChain::default(),
			send_past: HashMap::new(),
			send_ctr: 0,
			recv_past: HashMap::new(),
			recv_ctr: 0,
		}
	}

	pub fn ratchet_send(&mut self, info: &[u8]) -> Option<u64> {
		self.send_ctr += 1;
		let current = self.send_ctr;
		let keys = self.send_key.ratchet(info);
		if self.send_past.contains_key(&current) {
			return None;
		}
		self.send_past.insert(current, keys);
		Some(current)
	}

	pub fn send_key(&self, seq: u64) -> Option<&KeyMaterial> {
		self.send_past.get(&seq)
	}

	pub fn recv_key(&self, seq: u64) -> Option<&KeyMaterial> {
		self.recv_past.get(&seq)
	}

	pub fn ratchet_recv(&mut self, info: &[u8]) -> Option<u64> {
		self.recv_ctr += 1;
		let current = self.recv_ctr;
		let keys = self.recv_key.ratchet(info);
		if self.recv_past.contains_key(&current) {
			return None;
		}
		self.recv_past.insert(current, keys);
		Some(current)
	}

	pub fn ratchet_recv_until(&mut self, info: &[u8], until: u64) -> Option<u64> {
		if until <= self.recv_ctr {
			Some(until)
		} else if until > self.recv_ctr + RATCHET_MAX_GAP {
			None
		} else {
			let diff = until - self.recv_ctr;
			for _ in 0..diff {
				self.ratchet_recv(info);
			}
			assert_eq!(until, self.recv_ctr);
			Some(self.recv_ctr)
		}
	}

	pub fn init_ratchets(&mut self, ikm: &[u8], info: &[u8], is_beacon: bool) {
		let first_start = if is_beacon { 0 } else { KDF_STATE_SIZE };
		let second_start = if is_beacon { KDF_STATE_SIZE } else { 0 };
		let prk = crypto_kdf::hkdf::sha512::extract(None, ikm).unwrap();
		let mut combined =
			crypto_kdf::hkdf::sha512::expand(KDF_STATE_SIZE * 2, Some(info), &prk).unwrap();
		self.recv_key
			.state
			.copy_from_slice(&combined[first_start..first_start + KDF_STATE_SIZE]);
		self.send_key
			.state
			.copy_from_slice(&combined[second_start..second_start + KDF_STATE_SIZE]);
		combined.zeroize();
	}

	pub fn delete_send_key(&mut self, seq: u64) {
		self.send_past.remove(&seq);
	}

	pub fn delete_recv_key(&mut self, seq: u64) {
		self.recv_past.remove(&seq);
	}

	pub fn reset(&mut self) {
		self.send_key = SendChain::default();
		self.recv_key = RecvChain::default();
		self.send_past = HashMap::new();
		self.send_ctr = 0;
		self.recv_past = HashMap::new();
		self.recv_ctr = 0;
	}

	pub fn send_state(&self) -> &KdfState {
		&self.send_key.state
	}

	pub fn recv_state(&self) -> &KdfState {
		&self.recv_key.state
	}
}

pub trait SignaturePk {}

pub struct RemotePrincipal<PkType: SignaturePk> {
	pk: PkType,
	ratchet: RatchetManager,
}

impl<PkType: SignaturePk> RemotePrincipal<PkType> {
	pub fn new(pk: PkType, ratchet: RatchetManager) -> Self {
		Self { pk, ratchet }
	}

	pub fn pk(&self) -> &PkType {
		&self.pk
	}

	pub fn ratchet(&self) -> &RatchetManager {
		&self.ratchet
	}

	pub fn ratchet_mut(&mut self) -> &mut RatchetManager {
		&mut self.ratchet
	}
}

pub trait CryptoProvider {
	type SignaturePublicKey;
	type SignatureSecretKey;
	type KemPublicKey;
	type KemSecretKey;

	fn default() -> Self;
	fn new(
		is_beacon: bool,
		server_kid: u64,
		server_id_pk: Option<&[u8]>,
		id_seed: Option<&[u8]>,
	) -> Self;
	fn set_associated_data(&mut self, data: [u8; AD_SIZE]);
	fn associated_data(&self, kid: u64) -> Option<[u8; AD_SIZE]>;
	fn is_beacon(&self) -> bool;
	/// ## Arguments
	/// * `data`   - Some a serialized `CryptoFrame` to be decrypted
	/// * `is_beacon` - Whether the caller is a beacon
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `cryptoframe_capnp::crypto_frame`
	fn decrypt_message(&mut self, data: &[u8], kid: u64) -> Option<Vec<u8>> {
		let associated_data = self.associated_data(kid)?;
		match capnp::serialize::read_message(data, ReaderOptions::new()) {
			Ok(reader) => {
				let typed_reader =
					TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
				match typed_reader.get() {
					Ok(frame) => {
						let key_seq =
							self.ratchet_recv_until(SYM_RATCHET_INFO, frame.get_seq(), kid)?;
						let key = self.recv_key(key_seq, kid)?;
						let ciphertext = frame.get_cipher_text().ok()?;
						let ct_len = ciphertext.len();
						let commitment = self.build_commitment(
							key,
							associated_data.as_slice(),
							&ciphertext[ct_len
								- COMMITMENT_SIZE
								- crypto_aead::chacha20poly1305_ietf::ABYTES
								..ct_len - COMMITMENT_SIZE],
						)?;
						if !memcmp(&commitment, &ciphertext[ct_len - COMMITMENT_SIZE..]) {
							return None;
						}
						let plaintext = crypto_aead::chacha20poly1305_ietf::decrypt(
							&ciphertext[..ct_len - COMMITMENT_SIZE],
							Some(associated_data.as_slice()),
							key.nonce(),
							key.key(),
						)
						.ok()?;
						self.delete_recv_key(key_seq, kid);
						Some(plaintext)
					}
					Err(_) => None,
				}
			}
			Err(_) => None,
		}
	}

	/// ## Arguments
	/// * `data`   - A serialized `ProtoGram` to be decrypted
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `VerifiedMessage` containing the plaintext and authenticated key ID
	fn decrypt_signed(&mut self, data: &[u8]) -> Option<VerifiedMessage> {
		match self.verify_signature(data) {
			Some(verified) => {
				let plaintext = self.decrypt_message(&verified.data, verified.key_id)?;
				Some(VerifiedMessage {
					data: plaintext,
					key_id: verified.key_id,
				})
			}
			None => None,
		}
	}

	/// ## Arguments
	/// * `data`   - Some arbitrary byte buffer to be encrypted
	/// * `kid` - The identifier for the remote to encrypt to
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `cryptoframe_capnp::crypto_frame`
	fn encrypt_message(&mut self, bytes: &[u8], kid: u64) -> Option<Vec<u8>> {
		let associated_data = self.associated_data(kid)?;
		let key_seq = self.ratchet_send(SYM_RATCHET_INFO, kid)?;
		let key = self.send_key(key_seq, kid)?;
		let plaintext = crypto_aead::chacha20poly1305_ietf::encrypt_detached(
			bytes,
			Some(associated_data.as_slice()),
			key.nonce(),
			key.key(),
		);
		match plaintext {
			Ok((mut plaintext, mut tag)) => {
				let mut commitment =
					self.build_commitment(key, &associated_data, tag.as_slice())?;
				plaintext.append(&mut tag);
				plaintext.append(&mut commitment);
				let mut t_builder =
					TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
				let mut builder: cryptoframe_capnp::crypto_frame::Builder<'_> =
					t_builder.init_root();
				builder.set_cipher_text(&plaintext);
				builder.set_seq(key_seq);
				let mut buffer = vec![];
				capnp::serialize::write_message(&mut buffer, t_builder.borrow_inner()).unwrap();
				self.delete_send_key(key_seq, kid);
				Some(buffer)
			}
			Err(_) => {
				self.delete_send_key(key_seq, kid);
				None
			}
		}
	}

	/// /// ## Arguments
	/// * `data`   - Some arbitrary byte buffer to be encrypted
	/// * `kid` - The identifier for the remote to encrypt to
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `protogram_capnp::proto_gram`
	fn encrypt_and_sign(&mut self, bytes: &[u8], kid: u64) -> Option<Vec<u8>> {
		match self.encrypt_message(bytes, kid) {
			Some(ciphertext) => self.sign_message(ciphertext.as_slice()),
			None => None,
		}
	}

	/// implementation of the Chan and Rogaway `CTX` scheme: <https://eprint.iacr.org/2022/1260.pdf>
	/// `CT, T = ENC(K, N, A, M)`
	///
	/// `T* = H(K, N, A, T)`
	///
	/// the paper omits the original tag from the output. It is included here so we can keep using the libsodium interface
	///
	/// `CT* = CT || T || T*`
	fn build_commitment(&self, secret: &KeyMaterial, ad: &[u8], tag: &[u8]) -> Option<Vec<u8>> {
		let key = secret.key().as_bytes();
		let nonce = secret.nonce().as_bytes();
		let mut input = vec![];
		input.extend_from_slice(key);
		input.extend_from_slice(nonce);
		input.extend_from_slice(ad);
		input.extend_from_slice(tag);
		input.zeroize();
		crypto_generichash::generichash(input.as_slice(), None, COMMITMENT_SIZE).ok()
	}
	fn sign_message(&self, data: &[u8]) -> Option<Vec<u8>>;
	fn verify_signature(&self, data: &[u8]) -> Option<VerifiedMessage>;
	fn set_identity_kid(&mut self, key_id: u64);
	fn new_remote_kid(&mut self) -> u64;
	fn add_known_kid(&mut self, key_id: u64, pk: Self::SignaturePublicKey);
	/// Delete a known identity from the state
	fn delete_known_kid(&mut self, key_id: u64);
	/// Reset an identity's ratchet state
	fn reset_known_kid(&mut self, key_id: u64);
	fn server_id(&self) -> Option<&Self::SignaturePublicKey>;
	fn server_kid(&self) -> u64;
	fn add_server_pk(&mut self, pk: Self::SignaturePublicKey) {
		self.add_known_kid(self.server_kid(), pk)
	}
	fn pk_by_kid(&self, kid: u64) -> Option<&Self::SignaturePublicKey>;
	fn identity_pk(&self) -> &Self::SignaturePublicKey;
	fn identity_sk(&self) -> &Self::SignatureSecretKey;
	fn pq_pk(&self) -> Option<&Self::KemPublicKey>;
	fn pq_sk(&self) -> Option<&Self::KemSecretKey>;
	fn ratchet_manager(&self, kid: u64) -> Option<&RatchetManager>;
	fn ratchet_manager_mut(&mut self, kid: u64) -> Option<&mut RatchetManager>;
	/// ## Arguments
	/// * `info` - The info buffer to use for the ratchet step(s)
	/// * `until` - The message sequence number to ratchet to
	/// * `kid` - The identity to ratchet for
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	fn ratchet_recv_until(&mut self, info: &[u8], until: u64, kid: u64) -> Option<u64> {
		let remote = self.ratchet_manager_mut(kid)?;
		remote.ratchet_recv_until(info, until)
	}

	fn ratchet_send(&mut self, info: &[u8], kid: u64) -> Option<u64> {
		let remote = self.ratchet_manager_mut(kid)?;
		remote.ratchet_send(info)
	}
	fn send_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.ratchet_manager(kid) {
			Some(remote) => remote.send_key(seq),
			None => None,
		}
	}

	fn recv_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.ratchet_manager(kid) {
			Some(remote) => remote.recv_key(seq),
			None => None,
		}
	}

	fn delete_send_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.ratchet_manager_mut(kid) {
			remote.delete_send_key(seq)
		}
	}

	fn delete_recv_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.ratchet_manager_mut(kid) {
			remote.delete_recv_key(seq)
		}
	}

	/// You must call `add_known_id` or `add_server_id` before this
	fn init_ratchets(&mut self, ikm: &[u8], info: &[u8], is_beacon: bool, kid: u64) -> bool {
		match self.ratchet_manager_mut(kid) {
			Some(remote) => {
				remote.init_ratchets(ikm, info, is_beacon);
				true
			}
			None => false,
		}
	}
}

pub fn create_protogram_reader(
	data: &[u8],
) -> Option<TypedReader<capnp::serialize::OwnedSegments, protogram_capnp::proto_gram::Owned>> {
	// protograms are always packed
	match capnp::serialize_packed::read_message(data, ReaderOptions::new()) {
		Ok(reader) => {
			let typed_reader: TypedReader<
				capnp::serialize::OwnedSegments,
				protogram_capnp::proto_gram::Owned,
			> = TypedReader::<_, protogram_capnp::proto_gram::Owned>::new(reader);
			match typed_reader.get() {
				Ok(_) => Some(typed_reader),
				Err(_) => None,
			}
		}
		Err(_) => None,
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn key_bytes(key: &AeadKey) -> &[u8] {
		key.as_ref()
	}

	fn nonce_bytes(nonce: &AeadNonce) -> &[u8] {
		nonce.as_ref()
	}

	fn assert_key_material_eq(left: &KeyMaterial, right: &KeyMaterial) {
		assert_eq!(key_bytes(left.key()), key_bytes(right.key()));
		assert_eq!(nonce_bytes(left.nonce()), nonce_bytes(right.nonce()));
	}

	#[test]
	fn sign_type_discriminants_round_trip() {
		assert_eq!(u8::from(SignType::Undefined), 0);
		assert_eq!(u8::from(SignType::Ed25519), 1);
		assert!(matches!(SignType::from(0), SignType::Undefined));
		assert!(matches!(SignType::from(1), SignType::Ed25519));
		assert!(matches!(SignType::from(u8::MAX), SignType::Undefined));
	}

	#[test]
	fn kem_type_discriminants_round_trip() {
		assert_eq!(u8::from(KemType::Undefined), 0);
		assert_eq!(u8::from(KemType::MlKem768), 1);
		assert_eq!(u8::from(KemType::X25519), 2);
		assert!(matches!(KemType::from(0), KemType::Undefined));
		assert!(matches!(KemType::from(1), KemType::MlKem768));
		assert!(matches!(KemType::from(2), KemType::X25519));
		assert!(matches!(KemType::from(u8::MAX), KemType::Undefined));
	}

	#[cfg(feature = "server")]
	#[test]
	fn signing_key_encoding_round_trips() {
		let key = [0xA5; 32];
		let encoded = encode_sign(SignType::Ed25519, &key).unwrap();

		assert_eq!(encoded.len(), key.len() + 1);
		assert_eq!(encoded[0], 1);
		assert_eq!(decode_sign(&encoded, SignType::Ed25519).unwrap(), key);
	}

	#[cfg(feature = "server")]
	#[test]
	fn signing_key_encoding_rejects_type_mismatch() {
		let key = [0xA5; 32];
		let encoded = encode_sign(SignType::Ed25519, &key).unwrap();

		assert_eq!(encoded.len(), key.len() + 1);
		assert_eq!(encoded[0], 1);
		assert!(decode_sign(&encoded, SignType::MlDsa87).is_err());
	}

	#[cfg(feature = "server")]
	#[test]
	fn signing_key_encoding_rejects_invalid_inputs() {
		assert!(encode_sign(SignType::Undefined, &[0; 32]).is_err());
		assert!(decode_sign(&[], SignType::Undefined).is_err());
		assert!(decode_sign(&[1; 32], SignType::Undefined).is_err());

		let mut unknown_type = vec![0xA5; 33];
		unknown_type[0] = u8::MAX;
		assert!(decode_sign(&unknown_type, SignType::Ed25519).is_err());
	}

	#[cfg(all(feature = "beacon", feature = "server"))]
	#[test]
	fn kem_key_encoding_round_trips() {
		let x25519_key = [0x5A; 32];
		let encoded_x25519 = encode_kem(KemType::X25519, &x25519_key).unwrap();
		assert_eq!(encoded_x25519[0], 2);
		assert_eq!(
			decode_kem(&encoded_x25519, KemType::X25519).unwrap(),
			x25519_key
		);

		let ml_kem_key = [0xC3; 64];
		let encoded_ml_kem = encode_kem(KemType::MlKem768, &ml_kem_key).unwrap();
		assert_eq!(encoded_ml_kem[0], 1);
		assert_eq!(
			decode_kem(&encoded_ml_kem, KemType::MlKem768).unwrap(),
			ml_kem_key
		);
	}

	#[cfg(all(feature = "beacon", feature = "server"))]
	#[test]
	fn kem_key_encoding_rejects_invalid_inputs() {
		assert!(encode_kem(KemType::Undefined, &[0; 32]).is_err());
		assert!(decode_kem(&[], KemType::Undefined).is_err());
		assert!(decode_kem(&[2; 32], KemType::Undefined).is_err());

		let mut unknown_type = vec![0xA5; 33];
		unknown_type[0] = u8::MAX;
		assert!(decode_kem(&unknown_type, KemType::Undefined).is_err());
	}

	#[cfg(all(feature = "beacon", feature = "server"))]
	#[test]
	fn kem_key_encoding_rejects_type_mismatch() {
		let x25519_key = [0x5A; 32];
		let encoded_x25519 = encode_kem(KemType::X25519, &x25519_key).unwrap();

		assert_eq!(encoded_x25519.len(), x25519_key.len() + 1);
		assert_eq!(encoded_x25519[0], 2);
		assert!(decode_kem(&encoded_x25519, KemType::MlKem768).is_err());
	}

	#[test]
	fn secret_array_conversions_preserve_only_exact_length_inputs() {
		let exact = KdfState::from(vec![0x11; KDF_STATE_SIZE]);
		let too_short = KdfState::from(vec![0x22; KDF_STATE_SIZE - 1]);
		let too_long = KdfState::from(vec![0x33; KDF_STATE_SIZE + 1]);

		assert_eq!(exact.as_slice(), &[0x11; KDF_STATE_SIZE]);
		assert_eq!(too_short.as_slice(), &[0; KDF_STATE_SIZE]);
		assert_eq!(too_long.as_slice(), &[0; KDF_STATE_SIZE]);
		assert_eq!(exact.clone().as_slice(), exact.as_slice());
	}

	#[test]
	fn kdf_output_is_split_into_key_state_and_nonce() {
		let mut bytes = [0u8; KDF_RATCHET_OUTPUT_LEN];
		bytes[..AEAD_KEY_LEN].fill(0x11);
		bytes[AEAD_KEY_LEN..AEAD_KEY_LEN + KDF_STATE_SIZE].fill(0x22);
		bytes[AEAD_KEY_LEN + KDF_STATE_SIZE..].fill(0x33);

		let output = KdfOutput::from(bytes);

		assert_eq!(key_bytes(&output.aead_key), &[0x11; AEAD_KEY_LEN]);
		assert_eq!(output.kdf_state.as_slice(), &[0x22; KDF_STATE_SIZE]);
		assert_eq!(nonce_bytes(&output.aead_nonce), &[0x33; AEAD_NONCE_LEN]);
	}

	#[test]
	fn opposite_ratchet_roles_derive_matching_keys() {
		let ikm = [0x42; KDF_STATE_SIZE];
		let mut beacon = RatchetManager::new();
		let mut server = RatchetManager::new();
		beacon.init_ratchets(&ikm, SYM_RATCHET_INFO, true);
		server.init_ratchets(&ikm, SYM_RATCHET_INFO, false);

		let beacon_send = beacon.ratchet_send(SYM_RATCHET_INFO).unwrap();
		let server_recv = server.ratchet_recv(SYM_RATCHET_INFO).unwrap();
		assert_eq!(beacon_send, server_recv);
		assert_key_material_eq(
			beacon.send_key(beacon_send).unwrap(),
			server.recv_key(server_recv).unwrap(),
		);

		let server_send = server.ratchet_send(SYM_RATCHET_INFO).unwrap();
		let beacon_recv = beacon.ratchet_recv(SYM_RATCHET_INFO).unwrap();
		assert_eq!(server_send, beacon_recv);
		assert_key_material_eq(
			server.send_key(server_send).unwrap(),
			beacon.recv_key(beacon_recv).unwrap(),
		);
	}

	#[test]
	fn ratchet_generates_distinct_keys_and_deletes_used_keys() {
		let mut ratchet = RatchetManager::new();
		ratchet.init_ratchets(&[0x24; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);

		let first = ratchet.ratchet_send(SYM_RATCHET_INFO).unwrap();
		let second = ratchet.ratchet_send(SYM_RATCHET_INFO).unwrap();
		assert_eq!((first, second), (1, 2));
		assert_ne!(
			key_bytes(ratchet.send_key(first).unwrap().key()),
			key_bytes(ratchet.send_key(second).unwrap().key()),
		);

		ratchet.delete_send_key(first);
		assert!(ratchet.send_key(first).is_none());
		assert!(ratchet.send_key(second).is_some());
	}

	#[test]
	fn receive_ratchet_caches_skipped_keys_within_the_gap() {
		let mut ratchet = RatchetManager::new();
		ratchet.init_ratchets(&[0x18; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);

		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, RATCHET_MAX_GAP),
			Some(RATCHET_MAX_GAP),
		);
		assert!(ratchet.recv_key(1).is_some());
		assert!(ratchet.recv_key(RATCHET_MAX_GAP).is_some());
		assert_eq!(ratchet.ratchet_recv_until(SYM_RATCHET_INFO, 1), Some(1),);
	}

	#[test]
	fn receive_ratchet_rejects_a_gap_over_the_limit_without_advancing() {
		let mut ratchet = RatchetManager::new();
		ratchet.init_ratchets(&[0x81; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);

		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, RATCHET_MAX_GAP + 1),
			None,
		);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(ratchet.ratchet_recv(SYM_RATCHET_INFO), Some(1));
	}

	#[test]
	fn remote_principal_exposes_its_key_and_ratchet() {
		struct TestPublicKey([u8; 4]);
		impl SignaturePk for TestPublicKey {}

		let mut principal =
			RemotePrincipal::new(TestPublicKey([1, 2, 3, 4]), RatchetManager::new());
		assert_eq!(principal.pk().0, [1, 2, 3, 4]);
		assert!(principal.ratchet().send_key(1).is_none());
		assert_eq!(
			principal.ratchet_mut().ratchet_send(SYM_RATCHET_INFO),
			Some(1),
		);
		assert!(principal.ratchet().send_key(1).is_some());
	}

	#[test]
	fn protogram_reader_accepts_packed_messages_and_rejects_garbage() {
		let mut message = TypedBuilder::<protogram_capnp::proto_gram::Owned>::new_default();
		let mut root = message.init_root();
		root.set_key_id(42);
		root.set_data(b"signed payload");
		let mut serialized = vec![];
		capnp::serialize_packed::write_message(&mut serialized, message.borrow_inner()).unwrap();

		let parsed = create_protogram_reader(&serialized).unwrap();
		let root = parsed.get().unwrap();
		assert_eq!(root.get_key_id(), 42);
		assert_eq!(root.get_data().unwrap(), b"signed payload");
		assert!(create_protogram_reader(b"not a packed capnp message").is_none());
	}
}
