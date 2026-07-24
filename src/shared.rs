// SPDX-License-Identifier: 0BSD

use crate::cryptoframe_capnp;
#[cfg(feature = "server")]
use crate::error::DecodingError;
use crate::error::EncodingError;
#[cfg(feature = "pqxdh")]
use crate::pqxdh::AD_SIZE;
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
/// crypto_aead::chacha20poly1305_ietf::ABYTES
pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE + 16;

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
	pub struct Pqxdh;
}
mod roles {
	pub struct ChainKey;
	pub struct DerivedSecret;
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
				data: (*value.as_array::<S>().unwrap()).into(),
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
		let current = self.send_ctr.checked_add(1)?;
		if self.send_past.contains_key(&current) {
			return None;
		}
		let keys = self.send_key.ratchet(info);
		self.send_ctr = current;
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
		let current = self.recv_ctr.checked_add(1)?;
		if self.recv_past.contains_key(&current) {
			return None;
		}
		let keys = self.recv_key.ratchet(info);
		self.recv_ctr = current;
		self.recv_past.insert(current, keys);
		Some(current)
	}

	pub fn ratchet_recv_until(&mut self, info: &[u8], until: u64) -> Option<u64> {
		if until <= self.recv_ctr {
			Some(until)
		} else {
			let diff = until - self.recv_ctr;
			if diff > RATCHET_MAX_GAP || self.recv_past.len() as u64 + diff > RATCHET_MAX_GAP {
				return None;
			}
			for _ in 0..diff {
				self.ratchet_recv(info)?;
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

#[derive(Debug, Eq, PartialEq)]
pub struct Decrypted {
	pub plaintext: Vec<u8>,
	pub key_id: u64,
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
	/// * `data`   - A serialized `CryptoFrame` to be decrypted
	///
	/// ## Returns
	/// * `None` if some error happens, decryptio or commitment fails
	/// * `Vec<u8>` containing the plaintext
	fn decrypt_message(&mut self, data: &[u8]) -> Option<Decrypted> {
		if data.is_empty() {
			return None;
		}
		match capnp::serialize::read_message(data, ReaderOptions::new()) {
			Ok(reader) => {
				let typed_reader =
					TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
				match typed_reader.get() {
					Ok(frame) => {
						let kid = frame.get_key_id();
						let associated_data = self.associated_data(kid)?;
						let ciphertext = frame.get_cipher_text().ok()?;
						let ct_len = ciphertext.len();
						if ct_len <= MESSAGE_OVERHEAD {
							return None;
						}
						let key_seq =
							self.ratchet_recv_until(SYM_RATCHET_INFO, frame.get_seq(), kid)?;
						let key = self.recv_key(key_seq, kid)?;
						let commitment = build_commitment(
							key,
							associated_data.as_slice(),
							&ciphertext[ct_len
								- COMMITMENT_SIZE
								- crypto_aead::chacha20poly1305_ietf::ABYTES
								..ct_len - COMMITMENT_SIZE],
							key_seq,
							kid,
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
						Some(Decrypted {
							plaintext,
							key_id: kid,
						})
					}
					Err(_) => None,
				}
			}
			Err(_) => None,
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
		if bytes.is_empty() {
			return None;
		}
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
				let self_kid = self.identity_key_kid();
				let mut commitment =
					build_commitment(key, &associated_data, tag.as_slice(), key_seq, self_kid)?;
				plaintext.append(&mut tag);
				plaintext.append(&mut commitment);
				let mut t_builder =
					TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
				let mut builder: cryptoframe_capnp::crypto_frame::Builder<'_> =
					t_builder.init_root();
				builder.set_cipher_text(&plaintext);
				builder.set_seq(key_seq);
				builder.set_key_id(self_kid);
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

	fn set_identity_kid(&mut self, key_id: u64);
	fn identity_key_kid(&self) -> u64;
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

/// implementation of the Chan and Rogaway `CTX` scheme: <https://eprint.iacr.org/2022/1260.pdf>
/// `CT, T = ENC(K, N, A, M)`
///
/// `T* = H(K, N, A, T)`
///
/// the paper omits the original tag from the output. It is included here so we can keep using the libsodium interface
///
/// `CT* = CT || T || T*`
/// This commitment scheme commits to:
/// * Message
/// * Key
/// * Nonce
/// * Associated data
/// * key `seq`
/// * sender key identifier `kid`
fn build_commitment(
	secret: &KeyMaterial,
	ad: &[u8],
	tag: &[u8],
	seq: u64,
	kid: u64,
) -> Option<Vec<u8>> {
	if tag.len() != crypto_aead::chacha20poly1305_ietf::ABYTES {
		return None;
	}
	let key = secret.key().as_bytes();
	let nonce = secret.nonce().as_bytes();
	let mut input = vec![];
	input.extend_from_slice(key);
	input.extend_from_slice(nonce);
	input.extend_from_slice(ad);
	input.extend_from_slice(tag);
	input.extend_from_slice(&seq.to_le_bytes());
	input.extend_from_slice(&kid.to_le_bytes());
	let hash = crypto_generichash::generichash(input.as_slice(), None, COMMITMENT_SIZE).ok();
	input.zeroize();
	hash
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

	fn commitment_for_test(
		key: [u8; AEAD_KEY_LEN],
		nonce: [u8; AEAD_NONCE_LEN],
		ad: &[u8],
		tag: &[u8],
		seq: u64,
		kid: u64,
	) -> Vec<u8> {
		let secret = KeyMaterial {
			key: key.into(),
			nonce: nonce.into(),
		};
		build_commitment(&secret, ad, tag, seq, kid).unwrap()
	}

	fn decode_hex<const N: usize>(hex: &str) -> [u8; N] {
		fn nibble(byte: u8) -> u8 {
			match byte {
				b'0'..=b'9' => byte - b'0',
				b'a'..=b'f' => byte - b'a' + 10,
				b'A'..=b'F' => byte - b'A' + 10,
				_ => panic!("invalid hexadecimal fixture"),
			}
		}

		assert_eq!(hex.len(), N * 2);
		let mut decoded = [0; N];
		for (index, output) in decoded.iter_mut().enumerate() {
			let offset = index * 2;
			*output = (nibble(hex.as_bytes()[offset]) << 4) | nibble(hex.as_bytes()[offset + 1]);
		}
		decoded
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
	fn ratchet_matches_hkdf_sha512_known_answer_over_two_steps() {
		// Reproduced independently by `python scripts/generate_kat_vectors.py` and
		// `go run scripts/generate_kat_vectors.go` (`[ratchet]`).
		let mut ratchet = SendChain::from([0x24; KDF_STATE_SIZE]);

		let first = ratchet.ratchet(SYM_RATCHET_INFO);
		assert_eq!(
			key_bytes(first.key()),
			decode_hex::<AEAD_KEY_LEN>(
				"f57007f1b1c7a62a7d6cdfa5df07538c43d83656906764d607e627401906e42a"
			)
		);
		assert_eq!(
			nonce_bytes(first.nonce()),
			decode_hex::<AEAD_NONCE_LEN>("43483e81091a393409afbf53")
		);
		assert_eq!(
			ratchet.state.as_slice(),
			decode_hex::<KDF_STATE_SIZE>(
				"5936897d8bd06b7daf70bd0d64b2f607a055fd843ddb779051cb975bbb02b1d3"
			)
		);

		let second = ratchet.ratchet(SYM_RATCHET_INFO);
		assert_eq!(
			key_bytes(second.key()),
			decode_hex::<AEAD_KEY_LEN>(
				"f30ee97ccdc39577bb1320268d7fc10d55c53649e879e98a9670d58b9a1539d0"
			)
		);
		assert_eq!(
			nonce_bytes(second.nonce()),
			decode_hex::<AEAD_NONCE_LEN>("d497a96123dfcbe5700b5cc0")
		);
		assert_eq!(
			ratchet.state.as_slice(),
			decode_hex::<KDF_STATE_SIZE>(
				"d11e3c43fa3bbfec95a41973521d7e1b4aacddfc96591fe40fa30e9581b5e4e2"
			)
		);
	}

	/// Reproduced independently by `python scripts/generate_kat_vectors.py` and
	/// `go run scripts/generate_kat_vectors.go` (`[commitment]`).
	///
	/// ```python
	/// import hashlib
	/// key = bytes([0x11]) * 32
	/// nonce = bytes([0x22]) * 12
	/// ad = b"beaconcrypt-test-associated-data"
	/// tag = bytes([0x33]) * 16
	/// seq = (0x44).to_bytes(8, "little")
	/// kid = (0x55).to_bytes(8, "little")
	/// print(hashlib.blake2b(key + nonce + ad + tag + seq + kid, digest_size=64).hexdigest())
	/// ```
	#[test]
	fn commitment_matches_blake2b_known_answer() {
		let secret = KeyMaterial {
			key: [0x11; AEAD_KEY_LEN].into(),
			nonce: [0x22; AEAD_NONCE_LEN].into(),
		};
		let associated_data = b"beaconcrypt-test-associated-data";
		let tag = [0x33; crypto_aead::chacha20poly1305_ietf::ABYTES];
		let expected = [
			0x79, 0xe9, 0x43, 0x04, 0x98, 0xeb, 0x1e, 0x76, 0x9e, 0xc1, 0xd5, 0x20, 0x33, 0x87,
			0x9d, 0x4a, 0xb3, 0x9c, 0xc7, 0xfe, 0xda, 0xe4, 0xaa, 0x12, 0x87, 0x62, 0x97, 0xcb,
			0x36, 0xd3, 0x1b, 0x98, 0x81, 0x93, 0x3d, 0x34, 0x54, 0xca, 0xf6, 0x96, 0x08, 0xf4,
			0xf8, 0xf0, 0x1e, 0x07, 0x44, 0xf6, 0xb9, 0xb5, 0x63, 0x0a, 0xb3, 0x03, 0xef, 0xea,
			0x88, 0xf5, 0x25, 0x5b, 0x97, 0xac, 0x2a, 0x6a,
		];
		let key_seq = 0x44u64;
		let key_id = 0x55u64;

		assert_eq!(
			build_commitment(&secret, associated_data, &tag, key_seq, key_id).unwrap(),
			expected
		);
	}

	#[test]
	fn commitment_rejects_non_chacha_tag_lengths() {
		let secret = KeyMaterial {
			key: [0x51; AEAD_KEY_LEN].into(),
			nonce: [0x52; AEAD_NONCE_LEN].into(),
		};

		for tag_len in 0..=32 {
			let result = build_commitment(&secret, b"associated data", &vec![0x53; tag_len], 1, 2);
			if tag_len == crypto_aead::chacha20poly1305_ietf::ABYTES {
				assert!(result.is_some());
			} else {
				assert!(result.is_none(), "accepted a {tag_len}-byte AEAD tag");
			}
		}
	}

	#[test]
	fn rfc8439_aead_and_commitment_known_answer() {
		// The AEAD inputs and expected ciphertext/tag are from RFC 8439 section 2.8.2.
		// Independent reproductions and outer commitment calculations are in the Python
		// and Go KAT generators (`[rfc8439-and-commitment]`).
		let key = decode_hex::<AEAD_KEY_LEN>(
			"808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f",
		);
		let nonce = decode_hex::<AEAD_NONCE_LEN>("070000004041424344454647");
		let associated_data = decode_hex::<12>("50515253c0c1c2c3c4c5c6c7");
		let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
		let expected_ciphertext = decode_hex::<114>(
			"d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6\
			 3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36\
			 92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc\
			 3ff4def08e4b7a9de576d26586cec64b6116",
		);
		let expected_tag = decode_hex::<16>("1ae10b594f09e26a7e902ecbd0600691");
		let expected_commitment = decode_hex::<COMMITMENT_SIZE>(
			"cccff653b25cf3c21703c6648f4388867be568d607148b026045306e9cc21b37\
			 acd3e91c883f0eb70adde401e33871ae8171f1fe81341938fb9d73afd76c91ba",
		);
		let aead_key: AeadKey = key.into();
		let aead_nonce: AeadNonce = nonce.into();
		let (ciphertext, tag) = crypto_aead::chacha20poly1305_ietf::encrypt_detached(
			plaintext,
			Some(&associated_data),
			&aead_nonce,
			&aead_key,
		)
		.unwrap();

		assert_eq!(ciphertext, expected_ciphertext);
		assert_eq!(tag, expected_tag);

		let commitment = commitment_for_test(
			key,
			nonce,
			&associated_data,
			&tag,
			0x0123_4567_89AB_CDEF,
			0xFEDC_BA98_7654_3210,
		);
		assert_eq!(commitment, expected_commitment);

		let mut wire_payload = ciphertext;
		wire_payload.extend_from_slice(&tag);
		wire_payload.extend_from_slice(&commitment);
		assert_eq!(wire_payload.len(), plaintext.len() + MESSAGE_OVERHEAD);
		assert_eq!(&wire_payload[..plaintext.len()], &expected_ciphertext);
		assert_eq!(
			&wire_payload[plaintext.len()..plaintext.len() + expected_tag.len()],
			&expected_tag
		);
		assert_eq!(
			&wire_payload[plaintext.len() + expected_tag.len()..],
			&expected_commitment
		);
	}

	#[cfg(feature = "pqxdh")]
	#[test]
	fn commitment_binds_every_context_bit() {
		let mut key = [0x11; AEAD_KEY_LEN];
		let mut nonce = [0x22; AEAD_NONCE_LEN];
		let mut associated_data = [0x33; AD_SIZE];
		let mut tag = [0x44; crypto_aead::chacha20poly1305_ietf::ABYTES];
		let seq = 0x0123_4567_89AB_CDEF;
		let kid = 0xFEDC_BA98_7654_3210;
		let expected = commitment_for_test(key, nonce, &associated_data, &tag, seq, kid);

		for byte in 0..key.len() {
			for bit in 0..u8::BITS {
				key[byte] ^= 1 << bit;
				assert_ne!(
					commitment_for_test(key, nonce, &associated_data, &tag, seq, kid),
					expected,
					"key byte {byte}, bit {bit} is not bound"
				);
				key[byte] ^= 1 << bit;
			}
		}

		for byte in 0..nonce.len() {
			for bit in 0..u8::BITS {
				nonce[byte] ^= 1 << bit;
				assert_ne!(
					commitment_for_test(key, nonce, &associated_data, &tag, seq, kid),
					expected,
					"nonce byte {byte}, bit {bit} is not bound"
				);
				nonce[byte] ^= 1 << bit;
			}
		}

		for byte in 0..associated_data.len() {
			for bit in 0..u8::BITS {
				associated_data[byte] ^= 1 << bit;
				assert_ne!(
					commitment_for_test(key, nonce, &associated_data, &tag, seq, kid),
					expected,
					"associated-data byte {byte}, bit {bit} is not bound"
				);
				associated_data[byte] ^= 1 << bit;
			}
		}

		for byte in 0..tag.len() {
			for bit in 0..u8::BITS {
				tag[byte] ^= 1 << bit;
				assert_ne!(
					commitment_for_test(key, nonce, &associated_data, &tag, seq, kid),
					expected,
					"AEAD-tag byte {byte}, bit {bit} is not bound"
				);
				tag[byte] ^= 1 << bit;
			}
		}

		for bit in 0..u64::BITS {
			assert_ne!(
				commitment_for_test(key, nonce, &associated_data, &tag, seq ^ (1 << bit), kid),
				expected,
				"sequence bit {bit} is not bound"
			);
			assert_ne!(
				commitment_for_test(key, nonce, &associated_data, &tag, seq, kid ^ (1 << bit)),
				expected,
				"key-id bit {bit} is not bound"
			);
		}
	}

	#[test]
	fn commitment_separates_real_chacha20poly1305_multi_opening() {
		// This fixed fixture has two keys and associated-data blocks under which the shared
		// ciphertext and tag authenticate distinct plaintext/context openings. Both
		// openings are independently verified by the Python and Go KAT generators.
		// Its construction source and Poly1305 derivation are in
		// `scripts/derive_multi_opening.py` and `doc/multi-opening-fixture.md`.
		let key_one = decode_hex::<AEAD_KEY_LEN>(
			"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
		);
		let key_two = decode_hex::<AEAD_KEY_LEN>(
			"967712731b5091e4e42b5fa6241e3b02108fedc55c561d80af04c2095d3edbe7",
		);
		let nonce = decode_hex::<AEAD_NONCE_LEN>("000102030405060708090a0b");
		let ad_one = decode_hex::<16>("f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff");
		let ad_two = decode_hex::<16>("3a09eec3daf672a00f13351df1986203");
		let ciphertext = decode_hex::<16>("00112233445566778899aabbccddeeff");
		let tag = decode_hex::<{ crypto_aead::chacha20poly1305_ietf::ABYTES }>(
			"8867608090128f8c1a4711d553773215",
		);
		let expected_plaintext_one = decode_hex::<16>("89ea2a336d42c3373f1a954854c0e09c");
		let expected_plaintext_two = decode_hex::<16>("3c6ab3eb035de373e2b5d4a81a3cd13f");
		let aead_key_one: AeadKey = key_one.into();
		let aead_key_two: AeadKey = key_two.into();
		let aead_nonce: AeadNonce = nonce.into();
		let mut ciphertext_and_tag = ciphertext.to_vec();
		ciphertext_and_tag.extend_from_slice(&tag);

		let plaintext_one = crypto_aead::chacha20poly1305_ietf::decrypt(
			&ciphertext_and_tag,
			Some(&ad_one),
			&aead_nonce,
			&aead_key_one,
		)
		.unwrap();
		let plaintext_two = crypto_aead::chacha20poly1305_ietf::decrypt(
			&ciphertext_and_tag,
			Some(&ad_two),
			&aead_nonce,
			&aead_key_two,
		)
		.unwrap();
		assert_eq!(plaintext_one, expected_plaintext_one);
		assert_eq!(plaintext_two, expected_plaintext_two);
		assert_ne!(plaintext_one, plaintext_two);

		let commitment_one = commitment_for_test(key_one, nonce, &ad_one, &tag, 1, 7);
		let commitment_two = commitment_for_test(key_two, nonce, &ad_two, &tag, 1, 7);
		let expected_commitment_one = decode_hex::<COMMITMENT_SIZE>(
			"0573b9e328176e47de0251b211aa5347c72a61abf8e095bc7ac854982711f135\
			 25c0741341ac59f7db41163fba77aadf8592df71b25a3b02099b6b4b00a3c403",
		);
		let expected_commitment_two = decode_hex::<COMMITMENT_SIZE>(
			"322268a07252f76c4e894cab1e124db622ecf299f5050ed23768dd79b9e804ad\
			 22c48e36ff3b0e3e1c6984ee81d96c9d2900672298c6350d8413dbb49b5dcdd1",
		);
		assert_eq!(commitment_one, expected_commitment_one);
		assert_eq!(commitment_two, expected_commitment_two);
		assert_ne!(
			commitment_one, commitment_two,
			"CTX commitment must separate the base AEAD's two valid openings"
		);
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
	fn ratchets_reject_counter_exhaustion_without_mutating_state() {
		let mut send = RatchetManager::new();
		send.init_ratchets(&[0xA1; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);
		send.send_ctr = u64::MAX - 1;
		assert_eq!(send.ratchet_send(SYM_RATCHET_INFO), Some(u64::MAX));
		let send_state = send.send_state().as_slice().to_vec();
		let send_cache_len = send.send_past.len();
		assert_eq!(send.ratchet_send(SYM_RATCHET_INFO), None);
		assert_eq!(send.send_ctr, u64::MAX);
		assert_eq!(send.send_state().as_slice(), send_state);
		assert_eq!(send.send_past.len(), send_cache_len);
		assert!(send.send_key(0).is_none());

		let mut recv = RatchetManager::new();
		recv.init_ratchets(&[0xA2; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);
		recv.recv_ctr = u64::MAX;
		let recv_state = recv.recv_state().as_slice().to_vec();
		assert_eq!(recv.ratchet_recv(SYM_RATCHET_INFO), None);
		assert_eq!(recv.recv_ctr, u64::MAX);
		assert_eq!(recv.recv_state().as_slice(), recv_state);
		assert!(recv.recv_past.is_empty());
		assert!(recv.recv_key(0).is_none());
	}

	#[test]
	fn receive_ratchet_handles_exact_gap_near_counter_exhaustion() {
		for distance in [RATCHET_MAX_GAP, RATCHET_MAX_GAP - 1] {
			let mut ratchet = RatchetManager::new();
			ratchet.init_ratchets(&[0xA3; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);
			ratchet.recv_ctr = u64::MAX - distance;

			assert_eq!(
				ratchet.ratchet_recv_until(SYM_RATCHET_INFO, u64::MAX),
				Some(u64::MAX)
			);
			assert_eq!(ratchet.recv_ctr, u64::MAX);
			assert_eq!(ratchet.recv_past.len(), distance as usize);
			assert!(ratchet.recv_key(u64::MAX - distance + 1).is_some());
			assert!(ratchet.recv_key(u64::MAX).is_some());

			let state_at_exhaustion = ratchet.recv_state().as_slice().to_vec();
			assert_eq!(ratchet.ratchet_recv(SYM_RATCHET_INFO), None);
			assert_eq!(ratchet.recv_state().as_slice(), state_at_exhaustion);
			assert_eq!(ratchet.recv_past.len(), distance as usize);
		}
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
	fn receive_ratchet_bounds_total_cached_skipped_keys() {
		let mut ratchet = RatchetManager::new();
		ratchet.init_ratchets(&[0x91; KDF_STATE_SIZE], SYM_RATCHET_INFO, true);

		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, RATCHET_MAX_GAP),
			Some(RATCHET_MAX_GAP),
		);
		ratchet.delete_recv_key(RATCHET_MAX_GAP);
		assert_eq!(ratchet.recv_past.len(), RATCHET_MAX_GAP as usize - 1);

		let denied_target = RATCHET_MAX_GAP * 2;
		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, denied_target),
			None,
		);
		assert_eq!(ratchet.recv_ctr, RATCHET_MAX_GAP);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(ratchet.recv_past.len(), RATCHET_MAX_GAP as usize - 1);
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
}
