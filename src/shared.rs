// SPDX-License-Identifier: 0BSD

use crate::cryptoframe_capnp;
#[cfg(feature = "server")]
use crate::error::DecodingError;
#[cfg(any(feature = "server", test))]
use crate::error::EncodingError;
use beaconcrypt_protocol_core::commitment::{
	AEAD_KEY_SIZE as CORE_AEAD_KEY_LEN, AEAD_NONCE_SIZE as CORE_AEAD_NONCE_LEN,
	AEAD_TAG_SIZE as CORE_AEAD_TAG_LEN, build_commitment_transcript,
};
use beaconcrypt_protocol_core::pqxdh::{
	ASSOCIATED_DATA_SIZE as AD_SIZE, RATCHET_CHAIN_SIZE, RatchetInitialization,
};
use beaconcrypt_protocol_core::ratchet as verified_ratchet;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::utils::memcmp;
use libsodium_rs::{crypto_aead, crypto_generichash, crypto_kdf};
use std::any::TypeId;
use std::collections::HashMap;
use std::marker::{PhantomData, PhantomPinned};
use std::vec;
use zeroize::{Zeroize, Zeroizing};

#[cfg(feature = "server")]
#[path = "deser.rs"]
mod deser;
#[cfg(feature = "server")]
#[path = "ser.rs"]
mod ser;
#[cfg(feature = "server")]
pub(crate) use deser::deserialize_server_state;
#[cfg(feature = "server")]
pub(crate) use ser::serialize_server_state;

pub const KEX_KDF_OUT_LEN: usize = 32usize;
pub const KDF_STATE_SIZE: usize = 32usize;
const _: () = assert!(KEX_KDF_OUT_LEN == RATCHET_CHAIN_SIZE);
const _: () = assert!(KDF_STATE_SIZE == RATCHET_CHAIN_SIZE);
pub const SYM_RATCHET_INFO: &[u8; 41] = beaconcrypt_protocol_core::pqxdh::SYM_RATCHET_INFO;
/// crypto_aead::chacha20poly1305_ietf::KEYBYTES
pub const AEAD_KEY_LEN: usize = 32;
/// crypto_aead::chacha20poly1305_ietf::NPUBBYTES
pub const AEAD_NONCE_LEN: usize = 12;
/// crypto_aead::chacha20poly1305_ietf::ABYTES
pub const AEAD_TAG_LEN: usize = 16;
const _: () = assert!(AEAD_KEY_LEN == CORE_AEAD_KEY_LEN);
const _: () = assert!(AEAD_NONCE_LEN == CORE_AEAD_NONCE_LEN);
const _: () = assert!(AEAD_TAG_LEN == CORE_AEAD_TAG_LEN);
pub const KDF_RATCHET_OUTPUT_LEN: usize = AEAD_KEY_LEN + KDF_STATE_SIZE + AEAD_NONCE_LEN;
/// crypto_scalarmult::BYTES
#[cfg(feature = "pqxdh")]
pub const DH_OUT_LEN: usize = 32;
// the maximum amounts of out-of-order messages we tolerate
// cbindgen requires a literal initializer for this public C constant. The
// compile-time assertion keeps it tied to the authoritative core value.
pub const RATCHET_MAX_GAP: u64 = 50;
const _: () = assert!(RATCHET_MAX_GAP == verified_ratchet::RATCHET_MAX_GAP);
#[cfg(feature = "pqxdh")]
pub const ED25519_SEED_SIZE: usize = 32;
#[cfg(feature = "server")]
/// Byte sequence used to test successful keychain derivation during registration. Used only if the server doesn't provide an initial message
pub const REGISTRATION_WITNESS: &[u8; 1] = &[0xFF; 1];
pub const COMMITMENT_SIZE: usize = 64;
pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE + AEAD_TAG_LEN;

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
	MlKem768 = 3,
	X25519 = 4,
	MlKem1024 = 5,
}

impl From<KemType> for u8 {
	fn from(value: KemType) -> Self {
		match value {
			KemType::Undefined => 0,
			KemType::MlKem768 => 3,
			KemType::X25519 => 4,
			KemType::MlKem1024 => 5,
		}
	}
}

impl From<u8> for KemType {
	fn from(value: u8) -> Self {
		match value {
			3 => Self::MlKem768,
			4 => Self::X25519,
			5 => Self::MlKem1024,
			_ => Self::Undefined,
		}
	}
}

#[cfg(any(feature = "server", test))]
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

#[cfg(test)]
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

#[cfg(test)]
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
	#[derive(PartialEq)]
	pub struct X25519;
	#[cfg(feature = "server")]
	#[derive(PartialEq)]
	pub struct Ed25519;
	#[derive(PartialEq)]
	pub struct HkdfSha512;
	#[derive(PartialEq)]
	pub struct Pqxdh;
	#[cfg(feature = "server")]
	#[derive(PartialEq)]
	pub struct Chacha20Poly1305Ietf;

	#[cfg(feature = "server")]
	#[repr(u8)]
	#[derive(Clone, Copy, Debug, Eq, PartialEq)]
	pub enum Identifier {
		Undefined = 0,
		Ed25519 = 1,
		HkdfSha512 = 6,
		Chacha20Poly1305Ietf = 7,
	}

	#[cfg(feature = "server")]
	impl From<Identifier> for u8 {
		fn from(value: Identifier) -> Self {
			match value {
				Identifier::Undefined => 0,
				Identifier::Ed25519 => 1,
				Identifier::HkdfSha512 => 6,
				Identifier::Chacha20Poly1305Ietf => 7,
			}
		}
	}

	#[cfg(feature = "server")]
	impl From<u8> for Identifier {
		fn from(value: u8) -> Self {
			match value {
				1 => Self::Ed25519,
				6 => Self::HkdfSha512,
				7 => Self::Chacha20Poly1305Ietf,
				_ => Self::Undefined,
			}
		}
	}

	#[cfg(feature = "server")]
	pub trait Identified {
		const IDENTIFIER: Identifier;
	}

	#[cfg(feature = "server")]
	impl Identified for Ed25519 {
		const IDENTIFIER: Identifier = Identifier::Ed25519;
	}

	#[cfg(feature = "server")]
	impl Identified for HkdfSha512 {
		const IDENTIFIER: Identifier = Identifier::HkdfSha512;
	}

	#[cfg(feature = "server")]
	impl Identified for Chacha20Poly1305Ietf {
		const IDENTIFIER: Identifier = Identifier::Chacha20Poly1305Ietf;
	}
}
pub mod roles {
	pub trait ChainKey {}
	#[derive(PartialEq)]
	pub struct DerivedSecret;
	pub struct ChainSendKey;
	impl ChainKey for ChainSendKey {}
	pub struct ChainRecvKey;
	impl ChainKey for ChainRecvKey {}
	#[cfg(feature = "server")]
	pub struct EncryptionSendKey;
	#[cfg(feature = "server")]
	pub struct EncryptionRecvKey;
	#[cfg(feature = "server")]
	pub struct SendNonce;
	#[cfg(feature = "server")]
	pub struct RecvNonce;
	#[cfg(feature = "server")]
	pub struct IdentityKey;

	#[cfg(feature = "server")]
	#[repr(u8)]
	#[derive(Clone, Copy, Debug, Eq, PartialEq)]
	pub enum Identifier {
		Undefined = 0,
		ChainSendKey = 8,
		ChainRecvKey = 9,
		EncryptionSendKey = 10,
		EncryptionRecvKey = 11,
		SendNonce = 12,
		RecvNonce = 13,
		IdentityKey = 14,
	}

	#[cfg(feature = "server")]
	impl From<Identifier> for u8 {
		fn from(value: Identifier) -> Self {
			match value {
				Identifier::Undefined => 0,
				Identifier::ChainSendKey => 8,
				Identifier::ChainRecvKey => 9,
				Identifier::EncryptionSendKey => 10,
				Identifier::EncryptionRecvKey => 11,
				Identifier::SendNonce => 12,
				Identifier::RecvNonce => 13,
				Identifier::IdentityKey => 14,
			}
		}
	}

	#[cfg(feature = "server")]
	impl From<u8> for Identifier {
		fn from(value: u8) -> Self {
			match value {
				8 => Self::ChainSendKey,
				9 => Self::ChainRecvKey,
				10 => Self::EncryptionSendKey,
				11 => Self::EncryptionRecvKey,
				12 => Self::SendNonce,
				13 => Self::RecvNonce,
				14 => Self::IdentityKey,
				_ => Self::Undefined,
			}
		}
	}

	#[cfg(feature = "server")]
	pub trait Identified {
		const IDENTIFIER: Identifier;
	}

	#[cfg(feature = "server")]
	impl Identified for ChainSendKey {
		const IDENTIFIER: Identifier = Identifier::ChainSendKey;
	}

	#[cfg(feature = "server")]
	impl Identified for ChainRecvKey {
		const IDENTIFIER: Identifier = Identifier::ChainRecvKey;
	}

	#[cfg(feature = "server")]
	impl Identified for EncryptionSendKey {
		const IDENTIFIER: Identifier = Identifier::EncryptionSendKey;
	}

	#[cfg(feature = "server")]
	impl Identified for EncryptionRecvKey {
		const IDENTIFIER: Identifier = Identifier::EncryptionRecvKey;
	}

	#[cfg(feature = "server")]
	impl Identified for SendNonce {
		const IDENTIFIER: Identifier = Identifier::SendNonce;
	}

	#[cfg(feature = "server")]
	impl Identified for RecvNonce {
		const IDENTIFIER: Identifier = Identifier::RecvNonce;
	}

	#[cfg(feature = "server")]
	impl Identified for IdentityKey {
		const IDENTIFIER: Identifier = Identifier::IdentityKey;
	}
}

// this design is stolen from https://github.com/celabshq/libcrux/issues/1390
pub struct SecretArr<const S: usize, System, Role> {
	data: Zeroizing<[u8; S]>,
	// what cryptosystem this is used in (X25519, ML-KEM...)
	_system: PhantomData<System>,
	// what role does this play within the given cryptosystem (signing key, KDF state..)
	_role: PhantomData<Role>,
	_pin: PhantomPinned,
}

impl<const S: usize, System: 'static, Role: 'static, OtherSystem: 'static, OtherRole: 'static>
	PartialEq<SecretArr<S, OtherSystem, OtherRole>> for SecretArr<S, System, Role>
{
	fn eq(&self, other: &SecretArr<S, OtherSystem, OtherRole>) -> bool {
		let mut eq: bool = true;
		eq &= memcmp(self.data.as_slice(), other.data.as_slice());
		eq &= TypeId::of::<System>() == TypeId::of::<OtherSystem>();
		eq &= TypeId::of::<Role>() == TypeId::of::<OtherRole>();
		eq
	}
}

impl<const S: usize, System, Role> From<[u8; S]> for SecretArr<S, System, Role> {
	fn from(value: [u8; S]) -> Self {
		SecretArr {
			data: value.into(),
			_system: PhantomData,
			_role: PhantomData,
			_pin: PhantomPinned,
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
				_pin: PhantomPinned,
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
			_pin: PhantomPinned,
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
			_pin: PhantomPinned,
		}
	}
}

#[cfg(feature = "pqxdh")]
pub type DhSecret = SecretArr<DH_OUT_LEN, systems::X25519, roles::DerivedSecret>;
/// Expected to be bound by [roles::ChainKey] but the compiler doesn't enforce it
pub type KdfState<Role> = SecretArr<KDF_STATE_SIZE, systems::HkdfSha512, Role>;
pub type KdfSendState = KdfState<roles::ChainSendKey>;
pub type KdfRecvState = KdfState<roles::ChainRecvKey>;
pub type KexDerivedSecret = SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>;

#[derive(Clone)]
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

#[derive(Clone)]
struct KdfOutput<Role: roles::ChainKey> {
	aead_key: AeadKey,
	kdf_state: KdfState<Role>,
	aead_nonce: AeadNonce,
}

impl<Role: roles::ChainKey> From<[u8; KDF_RATCHET_OUTPUT_LEN]> for KdfOutput<Role> {
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

pub struct Ratchet<Role: roles::ChainKey> {
	state: KdfState<Role>,
}

impl<Role: roles::ChainKey> From<[u8; KDF_STATE_SIZE]> for Ratchet<Role> {
	fn from(value: [u8; KDF_STATE_SIZE]) -> Self {
		Self {
			state: value.into(),
		}
	}
}

impl<Role: roles::ChainKey> Ratchetable for Ratchet<Role> {
	fn ratchet(&mut self, info: &[u8]) -> KeyMaterial {
		let prk = crypto_kdf::hkdf::sha512::extract(None, self.state.as_slice()).unwrap();
		let out: KdfOutput<Role> =
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
impl<Role: roles::ChainKey> Default for Ratchet<Role> {
	fn default() -> Self {
		Self {
			state: [0u8; KDF_STATE_SIZE].into(),
		}
	}
}

impl<Role: roles::ChainKey> Clone for Ratchet<Role> {
	fn clone(&self) -> Self {
		Self {
			state: self.state.clone(),
		}
	}
}

type SendChain = Ratchet<roles::ChainSendKey>;
type RecvChain = Ratchet<roles::ChainRecvKey>;

#[derive(Clone)]
pub struct RatchetManager {
	/// current state of the KDF on the send chain
	send_key: SendChain,
	/// current state of the KDF on the recv chain
	recv_key: RecvChain,
	send_past: HashMap<u64, KeyMaterial>,
	/// One-use logical capabilities paired with every concrete pending send key.
	send_capabilities: HashMap<u64, verified_ratchet::SendKey>,
	/// Concrete receive keys indexed by the verified cache's physical slots.
	recv_past: [Option<KeyMaterial>; verified_ratchet::RECEIVE_CACHE_CAPACITY],
	/// Authoritative counters and logical receive-key ownership.
	control: verified_ratchet::RatchetState,
}

impl RatchetManager {
	pub fn default() -> Self {
		Self {
			send_key: SendChain::default(),
			recv_key: RecvChain::default(),
			send_past: HashMap::new(),
			send_capabilities: HashMap::new(),
			recv_past: std::array::from_fn(|_| None),
			control: verified_ratchet::RatchetState::default(),
		}
	}

	#[cfg(feature = "server")]
	pub fn from_json(json: String) -> Self {
		serde_json::from_str(&json).unwrap()
	}

	pub fn ratchet_send(&mut self, info: &[u8]) -> Option<u64> {
		debug_assert!(self.send_cache_matches_control());
		let advanced = verified_ratchet::advance_send(self.control);
		let current = advanced.sequence?;
		if self.send_past.contains_key(&current) || self.send_capabilities.contains_key(&current) {
			return None;
		}
		let keys = self.send_key.ratchet(info);
		let old_keys = self.send_past.insert(current, keys);
		let old_capability = self.send_capabilities.insert(current, advanced.key);
		debug_assert!(old_keys.is_none());
		debug_assert!(old_capability.is_none());
		self.control = advanced.state;
		debug_assert!(self.send_cache_matches_control());
		Some(current)
	}

	pub fn send_key(&self, seq: u64) -> Option<&KeyMaterial> {
		self.send_capabilities
			.get(&seq)
			.filter(|capability| capability.sequence() == Some(seq))?;
		self.send_past.get(&seq)
	}

	pub fn recv_key(&self, seq: u64) -> Option<&KeyMaterial> {
		let slot = verified_ratchet::lookup_receive_key(self.control, seq)?;
		self.recv_past.get(slot as usize)?.as_ref()
	}

	pub fn ratchet_recv(&mut self, info: &[u8]) -> Option<u64> {
		debug_assert!(self.receive_cache_matches_control());
		let advanced = verified_ratchet::advance_receive(self.control);
		let current = advanced.sequence?;
		let slot = advanced.slot?;
		if self.recv_past[slot as usize].is_some() {
			return None;
		}
		let keys = self.recv_key.ratchet(info);
		self.recv_past[slot as usize] = Some(keys);
		self.control = advanced.state;
		debug_assert_eq!(
			advanced
				.slot
				.and_then(|slot| self.control.receive_key_at(slot)),
			Some(current)
		);
		debug_assert!(self.receive_cache_matches_control());
		Some(current)
	}

	pub fn ratchet_recv_until(&mut self, info: &[u8], until: u64) -> Option<u64> {
		debug_assert!(self.receive_cache_matches_control());
		let plan = verified_ratchet::plan_receive_until(self.control, until);
		let target = plan.sequence?;
		for _ in 0..plan.derivations {
			self.ratchet_recv(info)?;
		}
		if plan.derivations != 0 {
			debug_assert_eq!(self.control.receive_sequence(), target);
		}
		debug_assert!(self.receive_cache_matches_control());
		Some(target)
	}

	pub(crate) fn init_ratchets(
		&mut self,
		ikm: &[u8],
		info: &[u8],
		initialization: RatchetInitialization,
	) -> bool {
		let Ok(prk) = crypto_kdf::hkdf::sha512::extract(None, ikm) else {
			return false;
		};
		let Ok(mut combined) =
			crypto_kdf::hkdf::sha512::expand(KDF_STATE_SIZE * 2, Some(info), &prk)
		else {
			return false;
		};
		let recv_start = initialization.receive_offset() as usize;
		let send_start = initialization.send_offset() as usize;
		if recv_start + RATCHET_CHAIN_SIZE > combined.len()
			|| send_start + RATCHET_CHAIN_SIZE > combined.len()
		{
			combined.zeroize();
			return false;
		}

		self.recv_key
			.state
			.copy_from_slice(&combined[recv_start..recv_start + RATCHET_CHAIN_SIZE]);
		self.send_key
			.state
			.copy_from_slice(&combined[send_start..send_start + RATCHET_CHAIN_SIZE]);
		combined.zeroize();

		self.send_past.clear();
		self.send_capabilities.clear();
		self.recv_past = std::array::from_fn(|_| None);
		self.control = verified_ratchet::RatchetState::default();
		true
	}

	fn consume_send_key(&mut self, seq: u64) -> bool {
		debug_assert!(self.send_cache_matches_control());
		let Some(capability) = self.send_capabilities.remove(&seq) else {
			return false;
		};
		if capability.sequence() != Some(seq) {
			self.send_capabilities.insert(seq, capability);
			return false;
		}

		let finished = verified_ratchet::finish_send(capability);
		if !finished.consumed {
			self.send_capabilities.insert(seq, finished.key);
			return false;
		}
		let removed = self.send_past.remove(&seq);
		debug_assert!(removed.is_some());
		debug_assert!(self.send_cache_matches_control());
		removed.is_some()
	}

	pub fn delete_send_key(&mut self, seq: u64) {
		self.consume_send_key(seq);
	}

	fn complete_recv_key(
		&mut self,
		seq: u64,
		authenticated: bool,
	) -> verified_ratchet::ReceiveDisposition {
		debug_assert!(self.receive_cache_matches_control());
		let Some(slot) = verified_ratchet::lookup_receive_key(self.control, seq) else {
			return verified_ratchet::ReceiveDisposition::Missing;
		};
		let has_concrete_key = self.recv_past[slot as usize].is_some();
		debug_assert!(
			has_concrete_key,
			"logical receive key has no concrete refinement"
		);
		if !has_concrete_key {
			return verified_ratchet::ReceiveDisposition::Missing;
		}

		let finished =
			verified_ratchet::finish_receive_with_removal(self.control, seq, slot, authenticated);
		if finished.disposition == verified_ratchet::ReceiveDisposition::Consumed {
			let Some(removal) = finished.removal else {
				return verified_ratchet::ReceiveDisposition::Missing;
			};
			let target_index = removal.target_slot as usize;
			let last_index = removal.last_slot as usize;
			if target_index >= self.recv_past.len()
				|| last_index >= self.recv_past.len()
				|| self.recv_past[target_index].is_none()
				|| self.recv_past[last_index].is_none()
			{
				return verified_ratchet::ReceiveDisposition::Missing;
			}
			self.recv_past.swap(target_index, last_index);
			let removed = self.recv_past[last_index].take();
			debug_assert!(removed.is_some());
		} else if finished.removal.is_some() || finished.state != self.control {
			return verified_ratchet::ReceiveDisposition::Missing;
		}
		self.control = finished.state;
		debug_assert!(self.receive_cache_matches_control());
		finished.disposition
	}

	pub fn delete_recv_key(&mut self, seq: u64) {
		self.complete_recv_key(seq, true);
	}

	pub fn reset(&mut self) {
		self.send_key = SendChain::default();
		self.recv_key = RecvChain::default();
		self.send_past = HashMap::new();
		self.send_capabilities = HashMap::new();
		self.recv_past = std::array::from_fn(|_| None);
		self.control = verified_ratchet::RatchetState::default();
	}

	#[cfg(any(feature = "server", test))]
	fn send_sequence(&self) -> u64 {
		self.control.send_sequence()
	}

	#[cfg(any(feature = "server", test))]
	fn receive_sequence(&self) -> u64 {
		self.control.receive_sequence()
	}

	fn send_cache_matches_control(&self) -> bool {
		self.send_past.len() == self.send_capabilities.len()
			&& self.send_past.keys().all(|sequence| {
				self.send_capabilities
					.get(sequence)
					.is_some_and(|capability| capability.sequence() == Some(*sequence))
			})
	}

	fn receive_cache_matches_control(&self) -> bool {
		let logical_len = self.control.receive_cache_len() as usize;
		logical_len <= self.recv_past.len()
			&& self.recv_past[..logical_len].iter().all(Option::is_some)
			&& self.recv_past[logical_len..].iter().all(Option::is_none)
			&& (0..self.control.receive_cache_len())
				.all(|slot| self.control.receive_key_at(slot).is_some())
	}

	#[cfg(feature = "server")]
	fn restored_send_capability(sequence: u64) -> Option<verified_ratchet::SendKey> {
		let previous = sequence.checked_sub(1)?;
		let restored =
			verified_ratchet::advance_send(verified_ratchet::RatchetState::new(previous));
		(restored.sequence == Some(sequence)).then_some(restored.key)
	}

	pub fn send_state(&self) -> &KdfSendState {
		&self.send_key.state
	}

	pub fn recv_state(&self) -> &KdfRecvState {
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
	/// The sequence number of the key consumed to decrypt this message.
	pub seq: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Encrypted {
	pub ciphertext: Vec<u8>,
	pub key_id: u64,
	/// The sequence number of the key consumed to encrypt this message.
	pub seq: u64,
}

impl std::ops::Deref for Encrypted {
	type Target = [u8];

	fn deref(&self) -> &Self::Target {
		&self.ciphertext
	}
}

impl std::ops::DerefMut for Encrypted {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.ciphertext
	}
}

impl AsRef<[u8]> for Encrypted {
	fn as_ref(&self) -> &[u8] {
		&self.ciphertext
	}
}

pub(crate) fn encrypted_frame_sender(data: &[u8]) -> Option<u64> {
	let reader = capnp::serialize::read_message(data, ReaderOptions::new()).ok()?;
	let typed_reader = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
	Some(typed_reader.get().ok()?.get_key_id())
}

/// Encrypt one frame against a staged or committed peer ratchet.
///
/// This is shared by the regular high-level provider path and the transactional
/// server-registration path. The Stage-3 send capability and its concrete key
/// are consumed together on every post-allocation outcome.
pub(crate) fn encrypt_message_with_ratchet(
	bytes: &[u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Encrypted> {
	if bytes.is_empty() {
		return None;
	}
	let key_seq = ratchet.ratchet_send(SYM_RATCHET_INFO)?;
	let encrypted = (|| {
		let key = ratchet.send_key(key_seq)?;
		let (mut plaintext, mut tag) = crypto_aead::chacha20poly1305_ietf::encrypt_detached(
			bytes,
			Some(associated_data.as_slice()),
			key.nonce(),
			key.key(),
		)
		.ok()?;
		let mut commitment =
			build_commitment(key, associated_data, tag.as_slice(), key_seq, sender_kid)?;
		plaintext.append(&mut tag);
		plaintext.append(&mut commitment);
		let mut t_builder = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
		let mut builder: cryptoframe_capnp::crypto_frame::Builder<'_> = t_builder.init_root();
		builder.set_cipher_text(&plaintext);
		builder.set_seq(key_seq);
		builder.set_key_id(sender_kid);
		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, t_builder.borrow_inner()).ok()?;
		Some(Encrypted {
			ciphertext: buffer,
			key_id: target_kid,
			seq: key_seq,
		})
	})();
	if !ratchet.consume_send_key(key_seq) {
		return None;
	}
	debug_assert!(ratchet.send_cache_matches_control());
	encrypted
}

/// Decrypt one frame against a staged or committed peer ratchet.
///
/// Authentication failure retains the exact logical and concrete receive key;
/// successful authentication consumes both, preserving the Stage-3 adapter
/// refinement while registration is staged off to the side.
pub(crate) fn decrypt_message_with_ratchet(
	data: &[u8],
	expected_sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Decrypted> {
	if data.is_empty() {
		return None;
	}
	let reader = capnp::serialize::read_message(data, ReaderOptions::new()).ok()?;
	let typed_reader = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
	let frame = typed_reader.get().ok()?;
	let kid = frame.get_key_id();
	if kid != expected_sender_kid {
		return None;
	}
	let ciphertext = frame.get_cipher_text().ok()?;
	let ct_len = ciphertext.len();
	if ct_len <= MESSAGE_OVERHEAD {
		return None;
	}
	let key_seq = ratchet.ratchet_recv_until(SYM_RATCHET_INFO, frame.get_seq())?;
	let key = ratchet.recv_key(key_seq)?;
	let commitment = build_commitment(
		key,
		associated_data.as_slice(),
		&ciphertext[ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE],
		key_seq,
		kid,
	);
	let plaintext = match commitment {
		Some(commitment) if memcmp(&commitment, &ciphertext[ct_len - COMMITMENT_SIZE..]) => {
			crypto_aead::chacha20poly1305_ietf::decrypt(
				&ciphertext[..ct_len - COMMITMENT_SIZE],
				Some(associated_data.as_slice()),
				key.nonce(),
				key.key(),
			)
			.ok()
		}
		_ => None,
	};
	let disposition = ratchet.complete_recv_key(key_seq, plaintext.is_some());
	if !matches!(
		(plaintext.is_some(), disposition),
		(true, verified_ratchet::ReceiveDisposition::Consumed)
			| (false, verified_ratchet::ReceiveDisposition::Retained)
	) {
		return None;
	}
	Some(Decrypted {
		plaintext: plaintext?,
		key_id: kid,
		seq: key_seq,
	})
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
	/// * `None` if some error happens, or decryption or commitment verification fails
	/// * [`Decrypted`] containing the plaintext and consumed key metadata
	fn decrypt_message(&mut self, data: &[u8]) -> Option<Decrypted> {
		let kid = encrypted_frame_sender(data)?;
		let associated_data = self.associated_data(kid)?;
		let ratchet = self.ratchet_manager_mut(kid)?;
		decrypt_message_with_ratchet(data, kid, &associated_data, ratchet)
	}

	/// ## Arguments
	/// * `data`   - Some arbitrary byte buffer to be encrypted
	/// * `kid` - The identifier for the remote to encrypt to
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * [`Encrypted`] containing a serialized `cryptoframe_capnp::crypto_frame` and consumed key
	///   metadata
	fn encrypt_message(&mut self, bytes: &[u8], kid: u64) -> Option<Encrypted> {
		let associated_data = self.associated_data(kid)?;
		let sender_kid = self.identity_key_kid();
		let ratchet = self.ratchet_manager_mut(kid)?;
		encrypt_message_with_ratchet(bytes, kid, sender_kid, &associated_data, ratchet)
	}

	fn set_identity_kid(&mut self, key_id: u64);
	fn identity_key_kid(&self) -> u64;
	/// Allocate the next remote key ID, or return `None` on exhaustion or collision.
	fn new_remote_kid(&mut self) -> Option<u64>;
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

	fn consume_send_key(&mut self, seq: u64, kid: u64) -> bool {
		self.ratchet_manager_mut(kid)
			.is_some_and(|remote| remote.consume_send_key(seq))
	}

	fn delete_recv_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.ratchet_manager_mut(kid) {
			remote.delete_recv_key(seq)
		}
	}

	fn complete_recv_key(&mut self, seq: u64, kid: u64, authenticated: bool) -> bool {
		let Some(remote) = self.ratchet_manager_mut(kid) else {
			return false;
		};
		matches!(
			(authenticated, remote.complete_recv_key(seq, authenticated)),
			(true, verified_ratchet::ReceiveDisposition::Consumed)
				| (false, verified_ratchet::ReceiveDisposition::Retained)
		)
	}
}

/// implementation of the Chan and Rogaway `CTX` scheme: <https://eprint.iacr.org/2022/1260.pdf>
/// `CT, T = ENC(K, N, A, M)`
///
/// `T* = H(K, N, A, T, LE64(seq), LE64(kid))`
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
	if tag.len() != AEAD_TAG_LEN
		|| secret.key.as_bytes().len() != AEAD_KEY_LEN
		|| secret.nonce.as_bytes().len() != AEAD_NONCE_LEN
		|| ad.len() != AD_SIZE
	{
		return None;
	}
	let key = secret.key().as_bytes();
	let nonce = secret.nonce().as_bytes();
	let mut input = build_commitment_transcript(
		key.try_into().ok()?,
		nonce,
		ad.try_into().ok()?,
		tag.try_into().ok()?,
		seq,
		kid,
	);
	let hash = crypto_generichash::generichash(input.as_bytes(), None, COMMITMENT_SIZE).ok();
	input.as_mut_bytes().zeroize();
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
		assert_eq!(u8::from(SignType::MlDsa87), 2);
		assert!(matches!(SignType::from(0), SignType::Undefined));
		assert!(matches!(SignType::from(1), SignType::Ed25519));
		assert!(matches!(SignType::from(2), SignType::MlDsa87));
		assert!(matches!(SignType::from(u8::MAX), SignType::Undefined));
	}

	#[test]
	fn kem_type_discriminants_round_trip() {
		assert_eq!(u8::from(KemType::Undefined), 0);
		assert_eq!(u8::from(KemType::MlKem768), 3);
		assert_eq!(u8::from(KemType::X25519), 4);
		assert_eq!(u8::from(KemType::MlKem1024), 5);
		assert!(matches!(KemType::from(0), KemType::Undefined));
		assert!(matches!(KemType::from(3), KemType::MlKem768));
		assert!(matches!(KemType::from(4), KemType::X25519));
		assert!(matches!(KemType::from(5), KemType::MlKem1024));
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
		assert_eq!(encoded_x25519[0], 4);
		assert_eq!(
			decode_kem(&encoded_x25519, KemType::X25519).unwrap(),
			x25519_key
		);

		let ml_kem_key = [0xC3; 64];
		let encoded_ml_kem = encode_kem(KemType::MlKem768, &ml_kem_key).unwrap();
		assert_eq!(encoded_ml_kem[0], 3);
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
		assert_eq!(encoded_x25519[0], 4);
		assert!(decode_kem(&encoded_x25519, KemType::MlKem768).is_err());
	}

	#[test]
	fn secret_array_conversions_preserve_only_exact_length_inputs() {
		let exact = KdfSendState::from(vec![0x11; KDF_STATE_SIZE]);
		let too_short = KdfSendState::from(vec![0x22; KDF_STATE_SIZE - 1]);
		let too_long = KdfSendState::from(vec![0x33; KDF_STATE_SIZE + 1]);

		assert_eq!(exact.as_slice(), &[0x11; KDF_STATE_SIZE]);
		assert_eq!(too_short.as_slice(), &[0; KDF_STATE_SIZE]);
		assert_eq!(too_long.as_slice(), &[0; KDF_STATE_SIZE]);
		assert_eq!(exact.clone().as_slice(), exact.as_slice());
	}

	#[test]
	fn secret_arrays_with_identical_contents_are_equal() {
		let left = KdfSendState::from([0x11; KDF_STATE_SIZE]);
		let right = KdfSendState::from([0x11; KDF_STATE_SIZE]);

		assert!(left == right);
		assert!(right == left);
	}

	#[test]
	fn secret_arrays_with_different_contents_are_not_equal() {
		let left = KdfSendState::from([0x11; KDF_STATE_SIZE]);
		let mut different = [0x11; KDF_STATE_SIZE];
		different[KDF_STATE_SIZE - 1] = 0x22;
		let right = KdfSendState::from(different);

		assert!(left != right);
		assert!(right != left);
	}

	#[test]
	fn secret_arrays_with_different_systems_are_not_equal() {
		type OtherSystem = SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::ChainSendKey>;

		let left = KdfSendState::from([0x11; KDF_STATE_SIZE]);
		let right = OtherSystem::from([0x11; KDF_STATE_SIZE]);

		assert!(left != right);
		assert!(right != left);
	}

	#[test]
	fn secret_arrays_with_different_roles_are_not_equal() {
		let left = KdfSendState::from([0x11; KDF_STATE_SIZE]);
		let right = KdfRecvState::from([0x11; KDF_STATE_SIZE]);

		assert!(left != right);
		assert!(right != left);
	}

	#[test]
	fn kdf_output_is_split_into_key_state_and_nonce() {
		assert_eq!(KDF_RATCHET_OUTPUT_LEN, 76);
		let mut bytes = [0u8; KDF_RATCHET_OUTPUT_LEN];
		bytes[..AEAD_KEY_LEN].fill(0x11);
		bytes[AEAD_KEY_LEN..AEAD_KEY_LEN + KDF_STATE_SIZE].fill(0x22);
		bytes[AEAD_KEY_LEN + KDF_STATE_SIZE..].fill(0x33);

		let output = KdfOutput::<roles::ChainSendKey>::from(bytes);

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
	/// ad = bytes([0x41]) * 153
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
		let associated_data = [0x41; AD_SIZE];
		let tag = [0x33; AEAD_TAG_LEN];
		let expected = decode_hex::<COMMITMENT_SIZE>(
			"39a3222768c214f7ceb291c4ba7df117a9d537a5ce41a61c33aba27e5f356153\
			 a4a1090295f03aae7e684e03710fd818217a7c8d1420a4b4a5f81d86893a435d",
		);
		let key_seq = 0x44u64;
		let key_id = 0x55u64;

		assert_eq!(
			build_commitment(&secret, &associated_data, &tag, key_seq, key_id).unwrap(),
			expected
		);
	}

	#[test]
	fn commitment_rejects_non_chacha_tag_lengths() {
		let secret = KeyMaterial {
			key: [0x51; AEAD_KEY_LEN].into(),
			nonce: [0x52; AEAD_NONCE_LEN].into(),
		};
		let associated_data = [0x54; AD_SIZE];

		for tag_len in 0..=32 {
			let result = build_commitment(&secret, &associated_data, &vec![0x53; tag_len], 1, 2);
			if tag_len == AEAD_TAG_LEN {
				assert!(result.is_some());
			} else {
				assert!(result.is_none(), "accepted a {tag_len}-byte AEAD tag");
			}
		}
	}

	#[test]
	fn commitment_rejects_non_beaconcrypt_associated_data_lengths() {
		let secret = KeyMaterial {
			key: [0x51; AEAD_KEY_LEN].into(),
			nonce: [0x52; AEAD_NONCE_LEN].into(),
		};
		let tag = [0x53; AEAD_TAG_LEN];

		for ad_len in [0, AD_SIZE - 1, AD_SIZE, AD_SIZE + 1] {
			let result = build_commitment(&secret, &vec![0x54; ad_len], &tag, 1, 2);
			if ad_len == AD_SIZE {
				assert!(result.is_some());
			} else {
				assert!(
					result.is_none(),
					"accepted {ad_len} bytes of associated data"
				);
			}
		}
	}

	#[test]
	fn rfc8439_aead_and_commitment_known_answer() {
		// The key, nonce, plaintext, and expected ciphertext are from RFC 8439 section
		// 2.8.2. Its 12-byte associated data is zero-padded to beaconcrypt's AD_SIZE;
		// this leaves the ciphertext unchanged but produces a beaconcrypt-specific tag.
		// Independent reproductions and outer commitment calculations are in the Python
		// and Go KAT generators (`[rfc8439-and-commitment]`).
		let key = decode_hex::<AEAD_KEY_LEN>(
			"808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f",
		);
		let nonce = decode_hex::<AEAD_NONCE_LEN>("070000004041424344454647");
		let rfc_associated_data = decode_hex::<12>("50515253c0c1c2c3c4c5c6c7");
		let mut associated_data = [0; AD_SIZE];
		associated_data[..rfc_associated_data.len()].copy_from_slice(&rfc_associated_data);
		let plaintext = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
		let expected_ciphertext = decode_hex::<114>(
			"d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6\
			 3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36\
			 92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc\
			 3ff4def08e4b7a9de576d26586cec64b6116",
		);
		let expected_tag = decode_hex::<AEAD_TAG_LEN>("88a5fc9f4d18b9c9d83fefd4f24e5fc4");
		let expected_commitment = decode_hex::<COMMITMENT_SIZE>(
			"1ea461abc0b5d491a23c7437f745548e9647a91c8ed34b29b171859a72e33dc5\
			 82554e0c807220fc0433bedd1f3c4c7353d381683b15fb8d91749c7463cccc1d",
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
		let mut ad_one = [0; AD_SIZE];
		for (index, byte) in ad_one.iter_mut().enumerate() {
			*byte = index as u8;
		}
		let mut ad_two = ad_one;
		ad_two[..16].copy_from_slice(&decode_hex::<16>("d62e8ca42f6f6e6eb114ca6035df7b24"));
		let ciphertext = decode_hex::<16>("00112233445566778899aabbccddeeff");
		let tag = decode_hex::<AEAD_TAG_LEN>("a21c712bf7f8d516c2d0126087060814");
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
			"9cda090561a1140c1e7fdee457c9057be213b87a65e895078564be7fa13360df\
			 fb48bab92db64d3800fd90ba2fc4d8c174add55cbbf0b0bff98eb74b32c1e06e",
		);
		let expected_commitment_two = decode_hex::<COMMITMENT_SIZE>(
			"f092a14b1da49bad4c64f3bacc67480d7dd367f5ba90fa3f79492aea29cd7707\
			 49b0aefdc03fa3736dd11ee3c79038a4a4d10a64959042dd97007690a7506bb2",
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
		let mut beacon = RatchetManager::default();
		let mut server = RatchetManager::default();
		beacon.init_ratchets(
			&ikm,
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		server.init_ratchets(
			&ikm,
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::server_ratchet_initialization(),
		);

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
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x24; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

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
		let mut send = RatchetManager::default();
		send.init_ratchets(
			&[0xA1; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		send.control = verified_ratchet::RatchetState::from_counters(u64::MAX - 1, 0);
		assert_eq!(send.ratchet_send(SYM_RATCHET_INFO), Some(u64::MAX));
		let send_state = send.send_state().as_slice().to_vec();
		let send_cache_len = send.send_past.len();
		assert_eq!(send.ratchet_send(SYM_RATCHET_INFO), None);
		assert_eq!(send.send_sequence(), u64::MAX);
		assert_eq!(send.send_state().as_slice(), send_state);
		assert_eq!(send.send_past.len(), send_cache_len);
		assert!(send.send_cache_matches_control());
		assert!(send.send_key(0).is_none());

		let mut recv = RatchetManager::default();
		recv.init_ratchets(
			&[0xA2; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		recv.control = verified_ratchet::RatchetState::from_counters(0, u64::MAX);
		let recv_state = recv.recv_state().as_slice().to_vec();
		assert_eq!(recv.ratchet_recv(SYM_RATCHET_INFO), None);
		assert_eq!(recv.receive_sequence(), u64::MAX);
		assert_eq!(recv.recv_state().as_slice(), recv_state);
		assert!(recv.recv_past.iter().all(Option::is_none));
		assert!(recv.receive_cache_matches_control());
		assert!(recv.recv_key(0).is_none());
	}

	#[test]
	fn receive_ratchet_handles_exact_gap_near_counter_exhaustion() {
		for distance in [RATCHET_MAX_GAP, RATCHET_MAX_GAP - 1] {
			let mut ratchet = RatchetManager::default();
			ratchet.init_ratchets(
				&[0xA3; KDF_STATE_SIZE],
				SYM_RATCHET_INFO,
				beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
			);
			ratchet.control = verified_ratchet::RatchetState::from_counters(0, u64::MAX - distance);

			assert_eq!(
				ratchet.ratchet_recv_until(SYM_RATCHET_INFO, u64::MAX),
				Some(u64::MAX)
			);
			assert_eq!(ratchet.receive_sequence(), u64::MAX);
			assert_eq!(
				ratchet.control.receive_cache_len() as usize,
				distance as usize
			);
			assert!(ratchet.receive_cache_matches_control());
			assert!(ratchet.recv_key(u64::MAX - distance + 1).is_some());
			assert!(ratchet.recv_key(u64::MAX).is_some());

			let state_at_exhaustion = ratchet.recv_state().as_slice().to_vec();
			assert_eq!(ratchet.ratchet_recv(SYM_RATCHET_INFO), None);
			assert_eq!(ratchet.recv_state().as_slice(), state_at_exhaustion);
			assert_eq!(
				ratchet.control.receive_cache_len() as usize,
				distance as usize
			);
		}
	}

	#[test]
	fn receive_ratchet_caches_skipped_keys_within_the_gap() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x18; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

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
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x81; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, RATCHET_MAX_GAP + 1),
			None,
		);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(ratchet.ratchet_recv(SYM_RATCHET_INFO), Some(1));
	}

	#[test]
	fn receive_ratchet_bounds_total_cached_skipped_keys() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x91; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, RATCHET_MAX_GAP),
			Some(RATCHET_MAX_GAP),
		);
		ratchet.delete_recv_key(RATCHET_MAX_GAP);
		assert_eq!(
			ratchet.control.receive_cache_len() as usize,
			RATCHET_MAX_GAP as usize - 1
		);

		let denied_target = RATCHET_MAX_GAP * 2;
		assert_eq!(
			ratchet.ratchet_recv_until(SYM_RATCHET_INFO, denied_target),
			None,
		);
		assert_eq!(ratchet.receive_sequence(), RATCHET_MAX_GAP);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(
			ratchet.control.receive_cache_len() as usize,
			RATCHET_MAX_GAP as usize - 1
		);
		assert!(ratchet.receive_cache_matches_control());
	}

	#[test]
	fn production_adapter_keeps_logical_and_concrete_keys_in_lockstep() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB1; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(ratchet.ratchet_recv_until(SYM_RATCHET_INFO, 4), Some(4));
		assert!(ratchet.receive_cache_matches_control());
		assert_eq!(ratchet.control.receive_cache_len(), 4);
		let last_key_before_swap = key_bytes(ratchet.recv_key(4).unwrap().key()).to_vec();

		let before_retry = ratchet.control;
		assert_eq!(
			ratchet.complete_recv_key(2, false),
			verified_ratchet::ReceiveDisposition::Retained
		);
		assert_eq!(ratchet.control, before_retry);
		assert!(ratchet.recv_key(2).is_some());
		assert!(ratchet.receive_cache_matches_control());

		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert!(ratchet.recv_key(2).is_none());
		assert_eq!(
			key_bytes(ratchet.recv_key(4).unwrap().key()),
			last_key_before_swap
		);
		assert_eq!(ratchet.control.receive_cache_len(), 3);
		assert!(ratchet.receive_cache_matches_control());

		let after_consumption = ratchet.control;
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Missing
		);
		assert_eq!(ratchet.control, after_consumption);
		assert!(ratchet.receive_cache_matches_control());

		let cloned = ratchet.clone();
		assert_eq!(cloned.control, ratchet.control);
		assert!(cloned.receive_cache_matches_control());

		ratchet.reset();
		assert_eq!(ratchet.control, verified_ratchet::RatchetState::default());
		assert!(ratchet.receive_cache_matches_control());
		assert!(ratchet.send_cache_matches_control());
	}

	#[test]
	fn production_adapter_consumes_core_send_capabilities() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB2; KDF_STATE_SIZE],
			SYM_RATCHET_INFO,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		let sequence = ratchet.ratchet_send(SYM_RATCHET_INFO).unwrap();
		assert_eq!(sequence, 1);
		assert!(ratchet.send_key(sequence).is_some());
		assert!(ratchet.send_cache_matches_control());
		assert!(ratchet.consume_send_key(sequence));
		assert!(ratchet.send_key(sequence).is_none());
		assert!(ratchet.send_cache_matches_control());
		assert!(!ratchet.consume_send_key(sequence));
	}

	#[test]
	fn adapter_invariant_checks_reject_one_sided_key_caches() {
		let mut send_inconsistent = RatchetManager::default();
		let capability =
			verified_ratchet::advance_send(verified_ratchet::RatchetState::default()).key;
		send_inconsistent.send_capabilities.insert(1, capability);
		assert!(!send_inconsistent.send_cache_matches_control());

		let mut receive_inconsistent = RatchetManager::default();
		receive_inconsistent.recv_past[0] = Some(KeyMaterial {
			key: [0xA1; AEAD_KEY_LEN].into(),
			nonce: [0xA2; AEAD_NONCE_LEN].into(),
		});
		assert!(!receive_inconsistent.receive_cache_matches_control());
		assert!(serde_json::to_string(&receive_inconsistent).is_err());
	}

	#[test]
	fn encrypted_as_ref_exposes_the_serialized_ciphertext() {
		let encrypted = Encrypted {
			ciphertext: vec![0x11, 0x22, 0x33],
			key_id: 7,
			seq: 9,
		};

		assert_eq!(
			<Encrypted as AsRef<[u8]>>::as_ref(&encrypted),
			&[0x11, 0x22, 0x33]
		);
	}

	#[test]
	fn remote_principal_exposes_its_key_and_ratchet() {
		struct TestPublicKey([u8; 4]);
		impl SignaturePk for TestPublicKey {}

		let mut principal =
			RemotePrincipal::new(TestPublicKey([1, 2, 3, 4]), RatchetManager::default());
		assert_eq!(principal.pk().0, [1, 2, 3, 4]);
		assert!(principal.ratchet().send_key(1).is_none());
		assert_eq!(
			principal.ratchet_mut().ratchet_send(SYM_RATCHET_INFO),
			Some(1),
		);
		assert!(principal.ratchet().send_key(1).is_some());
	}
}
