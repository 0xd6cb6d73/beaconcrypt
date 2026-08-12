// SPDX-License-Identifier: 0BSD

#[cfg(feature = "server")]
use crate::error::DecodingError;
#[cfg(any(feature = "server", test))]
use crate::error::EncodingError;
use libsodium_rs::utils::memcmp;
use std::any::TypeId;
use std::marker::{PhantomData, PhantomPinned};
#[cfg(any(feature = "server", test))]
use std::vec;
use zeroize::Zeroizing;

use crate::ratchet::{KDF_STATE_SIZE, RatchetManager};

#[cfg(test)]
use crate::ratchet::{
	AEAD_KEY_LEN, AEAD_NONCE_LEN, AEAD_TAG_LEN, AeadKey, AeadNonce, COMMITMENT_SIZE,
	KDF_RATCHET_OUTPUT_LEN, KdfRecvState, KdfSendState, KeyMaterial, MESSAGE_OVERHEAD,
	RATCHET_MAX_GAP, RatchetKernel, SendChain, build_commitment, decrypt_message_with_ratchet,
	encrypt_message_with_ratchet, ratchet_hkdf,
};
#[cfg(test)]
use beaconcrypt_protocol_core::pqxdh::ASSOCIATED_DATA_SIZE as AD_SIZE;
#[cfg(test)]
use beaconcrypt_protocol_core::ratchet as verified_ratchet;
#[cfg(test)]
use libsodium_rs::crypto_aead;

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
const _: () = assert!(KEX_KDF_OUT_LEN == KDF_STATE_SIZE);
/// crypto_scalarmult::BYTES
#[cfg(feature = "pqxdh")]
pub const DH_OUT_LEN: usize = 32;
#[cfg(feature = "pqxdh")]
pub const ED25519_SEED_SIZE: usize = 32;
#[cfg(feature = "server")]
/// Byte sequence used to test successful keychain derivation during registration. Used only if the server doesn't provide an initial message
pub const REGISTRATION_WITNESS: &[u8; 1] = &[0xFF; 1];

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

pub(crate) mod systems {
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
	pub struct EncryptionRecvKey;
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
	impl Identified for EncryptionRecvKey {
		const IDENTIFIER: Identifier = Identifier::EncryptionRecvKey;
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

	pub fn as_array(&self) -> &[u8; S] {
		&self.data
	}

	#[cfg(test)]
	pub fn copy_from_slice(&mut self, src: &[u8]) {
		self.data.copy_from_slice(src);
	}

	#[cfg(test)]
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
pub type KexDerivedSecret = SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>;

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

#[cfg(test)]
mod tests {
	use super::*;

	fn key_bytes(key: &verified_ratchet::RatchetKey) -> &[u8] {
		key.as_bytes()
	}

	fn nonce_bytes(nonce: &verified_ratchet::RatchetNonce) -> &[u8] {
		nonce.as_bytes()
	}

	fn assert_key_material_eq(left: &KeyMaterial, right: &KeyMaterial) {
		assert_eq!(key_bytes(left.key()), key_bytes(right.key()));
		assert_eq!(nonce_bytes(left.nonce()), nonce_bytes(right.nonce()));
	}

	fn receive_slot_snapshot(ratchet: &RatchetManager) -> Vec<Option<(Vec<u8>, Vec<u8>)>> {
		(0..verified_ratchet::RECEIVE_CACHE_CAPACITY as u8)
			.map(|slot| {
				ratchet.receive_entry_at(slot).map(|(_, material)| {
					(
						key_bytes(material.key()).to_vec(),
						nonce_bytes(material.nonce()).to_vec(),
					)
				})
			})
			.collect()
	}

	fn receive_slot(ratchet: &RatchetManager, sequence: u64) -> Option<u8> {
		(0..ratchet.receive_cache_len()).find(|slot| {
			ratchet
				.receive_entry_at(*slot)
				.is_some_and(|entry| entry.0 == sequence)
		})
	}

	fn logical_snapshot(ratchet: &RatchetManager) -> (u64, u64, Vec<u64>) {
		(
			ratchet.send_sequence(),
			ratchet.receive_sequence(),
			(0..ratchet.receive_cache_len())
				.map(|slot| ratchet.receive_entry_at(slot).unwrap().0)
				.collect(),
		)
	}

	fn set_counters(ratchet: &mut RatchetManager, send_sequence: u64, receive_sequence: u64) {
		let send_chain = ratchet.refined.send_chain().clone();
		let receive_chain = ratchet.refined.receive_chain().clone();
		ratchet.refined = RatchetKernel::from_counters(
			send_sequence,
			receive_sequence,
			send_chain,
			receive_chain,
			ratchet_hkdf,
		);
	}

	fn assert_receive_slots_aligned(ratchet: &RatchetManager) {
		let active_len = ratchet.receive_cache_len();
		for slot in 0..active_len {
			let (sequence, material) = ratchet.receive_entry_at(slot).unwrap();
			assert_eq!(receive_slot(ratchet, sequence), Some(slot));
			assert_key_material_eq(ratchet.recv_key(sequence).unwrap(), material);
		}
		for slot in active_len..verified_ratchet::RECEIVE_CACHE_CAPACITY as u8 {
			assert!(ratchet.receive_entry_at(slot).is_none());
		}
	}

	fn commitment_for_test(
		key: [u8; AEAD_KEY_LEN],
		nonce: [u8; AEAD_NONCE_LEN],
		ad: &[u8],
		tag: &[u8],
		seq: u64,
		kid: u64,
	) -> Vec<u8> {
		let secret = KeyMaterial::from_bytes(key, nonce);
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

	#[cfg(feature = "server")]
	#[test]
	fn secret_array_copy_and_inner_access_preserve_bytes() {
		let mut secret = KdfSendState::default();
		secret.copy_from_slice(&[0xA5; KDF_STATE_SIZE]);

		assert_eq!(secret.inner().as_slice(), &[0xA5; KDF_STATE_SIZE]);
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

		let output = verified_ratchet::split_ratchet_kdf_output(&bytes);

		assert_eq!(output.key().as_bytes(), &[0x11; AEAD_KEY_LEN]);
		assert_eq!(output.next_chain().as_bytes(), &[0x22; KDF_STATE_SIZE]);
		assert_eq!(output.nonce().as_bytes(), &[0x33; AEAD_NONCE_LEN]);
	}

	#[test]
	fn ratchet_matches_hkdf_sha512_known_answer_over_two_steps() {
		// Reproduced independently by `python scripts/generate_kat_vectors.py` and
		// `go run scripts/generate_kat_vectors.go` (`[ratchet]`).
		let ratchet = SendChain::from_bytes([0x24; KDF_STATE_SIZE]);

		let first = verified_ratchet::derive_ratchet_step(&ratchet, ratchet_hkdf);
		assert_eq!(
			key_bytes(first.material.key()),
			decode_hex::<AEAD_KEY_LEN>(
				"f57007f1b1c7a62a7d6cdfa5df07538c43d83656906764d607e627401906e42a"
			)
		);
		assert_eq!(
			nonce_bytes(first.material.nonce()),
			decode_hex::<AEAD_NONCE_LEN>("43483e81091a393409afbf53")
		);
		assert_eq!(
			*first.chain.as_bytes(),
			decode_hex::<KDF_STATE_SIZE>(
				"5936897d8bd06b7daf70bd0d64b2f607a055fd843ddb779051cb975bbb02b1d3"
			)
		);

		let second = verified_ratchet::derive_ratchet_step(&first.chain, ratchet_hkdf);
		assert_eq!(
			key_bytes(second.material.key()),
			decode_hex::<AEAD_KEY_LEN>(
				"f30ee97ccdc39577bb1320268d7fc10d55c53649e879e98a9670d58b9a1539d0"
			)
		);
		assert_eq!(
			nonce_bytes(second.material.nonce()),
			decode_hex::<AEAD_NONCE_LEN>("d497a96123dfcbe5700b5cc0")
		);
		assert_eq!(
			*second.chain.as_bytes(),
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
		let secret = KeyMaterial::from_bytes([0x11; AEAD_KEY_LEN], [0x22; AEAD_NONCE_LEN]);
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
		let secret = KeyMaterial::from_bytes([0x51; AEAD_KEY_LEN], [0x52; AEAD_NONCE_LEN]);
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
		let secret = KeyMaterial::from_bytes([0x51; AEAD_KEY_LEN], [0x52; AEAD_NONCE_LEN]);
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
		let associated_data = [0x43; AD_SIZE];
		let mut beacon = RatchetManager::default();
		let mut server = RatchetManager::default();
		beacon.init_ratchets(
			&ikm,
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		server.init_ratchets(
			&ikm,
			beaconcrypt_protocol_core::pqxdh::server_ratchet_initialization(),
		);

		let beacon_frame =
			encrypt_message_with_ratchet(b"from beacon", 7, 9, &associated_data, &mut beacon)
				.unwrap();
		assert_eq!(beacon_frame.seq, 1);
		let opened_at_server = decrypt_message_with_ratchet(
			&beacon_frame.ciphertext,
			9,
			&associated_data,
			&mut server,
		)
		.unwrap();
		assert_eq!(opened_at_server.plaintext, b"from beacon");

		let server_frame =
			encrypt_message_with_ratchet(b"from server", 9, 7, &associated_data, &mut server)
				.unwrap();
		assert_eq!(server_frame.seq, 1);
		let opened_at_beacon = decrypt_message_with_ratchet(
			&server_frame.ciphertext,
			7,
			&associated_data,
			&mut beacon,
		)
		.unwrap();
		assert_eq!(opened_at_beacon.plaintext, b"from server");
	}

	#[test]
	fn high_level_sends_advance_without_staging_keys() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x24; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		let initial_state = ratchet.send_state().as_slice().to_vec();
		let associated_data = [0x25; AD_SIZE];
		let first =
			encrypt_message_with_ratchet(b"first", 7, 9, &associated_data, &mut ratchet).unwrap();
		let first_state = ratchet.send_state().as_slice().to_vec();
		let second =
			encrypt_message_with_ratchet(b"second", 7, 9, &associated_data, &mut ratchet).unwrap();

		assert_eq!((first.seq, second.seq), (1, 2));
		assert_ne!(first.ciphertext, second.ciphertext);
		assert_ne!(first_state, initial_state);
		assert_ne!(ratchet.send_state().as_slice(), first_state);
		assert_eq!(ratchet.send_sequence(), 2);
	}

	#[test]
	fn ratchets_reject_counter_exhaustion_without_mutating_state() {
		let mut send = RatchetManager::default();
		send.init_ratchets(
			&[0xA1; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		set_counters(&mut send, u64::MAX - 1, 0);
		let associated_data = [0xA0; AD_SIZE];
		let last =
			encrypt_message_with_ratchet(b"last", 7, 9, &associated_data, &mut send).unwrap();
		assert_eq!(last.seq, u64::MAX);
		let logical = logical_snapshot(&send);
		let send_state = send.send_state().as_slice().to_vec();
		assert!(
			encrypt_message_with_ratchet(b"exhausted", 7, 9, &associated_data, &mut send).is_none()
		);
		assert_eq!(logical_snapshot(&send), logical);
		assert_eq!(send.send_sequence(), u64::MAX);
		assert_eq!(send.send_state().as_slice(), send_state);

		let mut recv = RatchetManager::default();
		recv.init_ratchets(
			&[0xA2; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		set_counters(&mut recv, 0, u64::MAX);
		let recv_state = recv.recv_state().as_slice().to_vec();
		assert_eq!(recv.ratchet_recv(), None);
		assert_eq!(recv.receive_sequence(), u64::MAX);
		assert_eq!(recv.recv_state().as_slice(), recv_state);
		assert_eq!(recv.receive_cache_len(), 0);
		assert_receive_slots_aligned(&recv);
		assert!(recv.recv_key(0).is_none());
	}

	#[test]
	fn refined_receive_ratchet_exposes_only_paired_active_entries() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xA4; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(2), Some(2));
		assert_receive_slots_aligned(&ratchet);
		assert!(ratchet.receive_entry_at(2).is_none());
		assert!(serde_json::to_string(&ratchet).is_ok());
	}

	#[test]
	fn receive_ratchet_handles_exact_gap_near_counter_exhaustion() {
		for distance in [RATCHET_MAX_GAP, RATCHET_MAX_GAP - 1] {
			let mut ratchet = RatchetManager::default();
			ratchet.init_ratchets(
				&[0xA3; KDF_STATE_SIZE],
				beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
			);
			set_counters(&mut ratchet, 0, u64::MAX - distance);

			assert_eq!(ratchet.ratchet_recv_until(u64::MAX), Some(u64::MAX));
			assert_eq!(ratchet.receive_sequence(), u64::MAX);
			assert_eq!(ratchet.receive_cache_len() as usize, distance as usize);
			assert_receive_slots_aligned(&ratchet);
			assert!(ratchet.recv_key(u64::MAX - distance + 1).is_some());
			assert!(ratchet.recv_key(u64::MAX).is_some());

			let logical_at_exhaustion = logical_snapshot(&ratchet);
			let state_at_exhaustion = ratchet.recv_state().as_slice().to_vec();
			let slots_at_exhaustion = receive_slot_snapshot(&ratchet);
			assert_eq!(ratchet.ratchet_recv(), None);
			assert_eq!(logical_snapshot(&ratchet), logical_at_exhaustion);
			assert_eq!(ratchet.recv_state().as_slice(), state_at_exhaustion);
			assert_eq!(receive_slot_snapshot(&ratchet), slots_at_exhaustion);
			assert_receive_slots_aligned(&ratchet);
		}
	}

	#[test]
	fn receive_ratchet_caches_skipped_keys_within_the_gap() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x18; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(
			ratchet.ratchet_recv_until(RATCHET_MAX_GAP),
			Some(RATCHET_MAX_GAP),
		);
		assert!(ratchet.recv_key(1).is_some());
		assert!(ratchet.recv_key(RATCHET_MAX_GAP).is_some());
		assert_eq!(ratchet.ratchet_recv_until(1), Some(1),);
	}

	#[test]
	fn receive_ratchet_rejects_a_gap_over_the_limit_without_advancing() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x81; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(ratchet.ratchet_recv_until(RATCHET_MAX_GAP + 1), None,);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(ratchet.ratchet_recv(), Some(1));
	}

	#[test]
	fn receive_ratchet_bounds_total_cached_skipped_keys() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0x91; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(
			ratchet.ratchet_recv_until(RATCHET_MAX_GAP),
			Some(RATCHET_MAX_GAP),
		);
		ratchet.delete_recv_key(RATCHET_MAX_GAP);
		assert_eq!(
			ratchet.receive_cache_len() as usize,
			RATCHET_MAX_GAP as usize - 1
		);

		let denied_target = RATCHET_MAX_GAP * 2;
		assert_eq!(ratchet.ratchet_recv_until(denied_target), None,);
		assert_eq!(ratchet.receive_sequence(), RATCHET_MAX_GAP);
		assert!(ratchet.recv_key(RATCHET_MAX_GAP + 1).is_none());
		assert_eq!(
			ratchet.receive_cache_len() as usize,
			RATCHET_MAX_GAP as usize - 1
		);
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn refined_kernel_keeps_logical_and_concrete_keys_in_lockstep() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB1; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));
		assert_receive_slots_aligned(&ratchet);
		assert_eq!(ratchet.receive_cache_len(), 4);
		let last_key_before_swap = key_bytes(ratchet.recv_key(4).unwrap().key()).to_vec();

		let before_retry = logical_snapshot(&ratchet);
		assert_eq!(
			ratchet.complete_recv_key(2, false),
			verified_ratchet::ReceiveDisposition::Retained
		);
		assert_eq!(logical_snapshot(&ratchet), before_retry);
		assert!(ratchet.recv_key(2).is_some());
		assert_receive_slots_aligned(&ratchet);

		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert!(ratchet.recv_key(2).is_none());
		assert_eq!(
			key_bytes(ratchet.recv_key(4).unwrap().key()),
			last_key_before_swap
		);
		assert_eq!(ratchet.receive_cache_len(), 3);
		assert_receive_slots_aligned(&ratchet);

		let after_consumption = logical_snapshot(&ratchet);
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Missing
		);
		assert_eq!(logical_snapshot(&ratchet), after_consumption);
		assert_receive_slots_aligned(&ratchet);

		let cloned = ratchet.clone();
		assert_eq!(logical_snapshot(&cloned), logical_snapshot(&ratchet));
		assert_receive_slots_aligned(&cloned);

		ratchet.reset();
		assert_eq!(logical_snapshot(&ratchet), (0, 0, Vec::new()));
		assert_receive_slots_aligned(&ratchet);

		assert_eq!(ratchet.ratchet_recv_until(2), Some(2));
		assert_eq!(ratchet.receive_cache_len(), 2);
		ratchet.init_ratchets(
			&[0xBB; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(logical_snapshot(&ratchet), (0, 0, Vec::new()));
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn receive_allocation_populates_every_verified_slot() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB3; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));
		assert_eq!(ratchet.receive_cache_len(), 4);
		assert_receive_slots_aligned(&ratchet);
		for sequence in 1..=4 {
			let slot = receive_slot(&ratchet, sequence).unwrap();
			assert_eq!(ratchet.receive_entry_at(slot).unwrap().0, sequence);
		}
	}

	#[test]
	fn non_last_receive_removal_preserves_key_nonce_and_exact_slot() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB4; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));

		let target_slot = receive_slot(&ratchet, 2).unwrap();
		let last_slot = receive_slot(&ratchet, 4).unwrap();
		let last_material = ratchet.recv_key(4).unwrap().clone();
		assert_ne!(target_slot, last_slot);

		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert_eq!(receive_slot(&ratchet, 2), None);
		assert_eq!(receive_slot(&ratchet, 4), Some(target_slot));
		assert_key_material_eq(
			ratchet.receive_entry_at(target_slot).unwrap().1,
			&last_material,
		);
		assert!(ratchet.receive_entry_at(last_slot).is_none());
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn last_receive_slot_removal_preserves_the_active_prefix() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB5; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));

		let last_slot = receive_slot(&ratchet, 4).unwrap();
		let prefix = (1..=3)
			.map(|sequence| {
				(
					sequence,
					receive_slot(&ratchet, sequence).unwrap(),
					ratchet.recv_key(sequence).unwrap().clone(),
				)
			})
			.collect::<Vec<_>>();

		assert_eq!(
			ratchet.complete_recv_key(4, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert_eq!(receive_slot(&ratchet, 4), None);
		assert!(ratchet.receive_entry_at(last_slot).is_none());
		for (sequence, slot, material) in prefix {
			assert_eq!(receive_slot(&ratchet, sequence), Some(slot));
			assert_key_material_eq(ratchet.recv_key(sequence).unwrap(), &material);
		}
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn failed_receive_retry_is_concretely_and_kdf_neutral() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB6; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));

		let admitted_logical = logical_snapshot(&ratchet);
		let admitted_chain = ratchet.recv_state().as_slice().to_vec();
		let admitted_slots = receive_slot_snapshot(&ratchet);
		for _ in 0..2 {
			assert_eq!(
				ratchet.complete_recv_key(4, false),
				verified_ratchet::ReceiveDisposition::Retained
			);
			assert_eq!(logical_snapshot(&ratchet), admitted_logical);
			assert_eq!(ratchet.recv_state().as_slice(), admitted_chain);
			assert_eq!(receive_slot_snapshot(&ratchet), admitted_slots);
			assert_eq!(ratchet.ratchet_recv_until(4), Some(4));
			assert_eq!(logical_snapshot(&ratchet), admitted_logical);
			assert_eq!(ratchet.recv_state().as_slice(), admitted_chain);
			assert_eq!(receive_slot_snapshot(&ratchet), admitted_slots);
		}
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn receive_replay_is_concretely_and_kdf_neutral() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB7; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);

		let consumed_logical = logical_snapshot(&ratchet);
		let consumed_chain = ratchet.recv_state().as_slice().to_vec();
		let consumed_slots = receive_slot_snapshot(&ratchet);
		assert_eq!(receive_slot(&ratchet, 2), None);
		assert!(ratchet.recv_key(2).is_none());
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Missing
		);
		assert_eq!(logical_snapshot(&ratchet), consumed_logical);
		assert_eq!(ratchet.recv_state().as_slice(), consumed_chain);
		assert_eq!(receive_slot_snapshot(&ratchet), consumed_slots);
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn full_receive_cache_releases_and_refills_the_verified_last_slot() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB8; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		let capacity = verified_ratchet::RECEIVE_CACHE_CAPACITY as u64;
		assert_eq!(ratchet.ratchet_recv_until(capacity), Some(capacity));
		assert_receive_slots_aligned(&ratchet);

		let full_logical = logical_snapshot(&ratchet);
		let full_chain = ratchet.recv_state().as_slice().to_vec();
		let full_slots = receive_slot_snapshot(&ratchet);
		assert_eq!(ratchet.ratchet_recv_until(capacity + 1), None);
		assert_eq!(logical_snapshot(&ratchet), full_logical);
		assert_eq!(ratchet.recv_state().as_slice(), full_chain);
		assert_eq!(receive_slot_snapshot(&ratchet), full_slots);

		let target_slot = receive_slot(&ratchet, 2).unwrap();
		let old_last_slot = receive_slot(&ratchet, capacity).unwrap();
		let old_last_material = ratchet.recv_key(capacity).unwrap().clone();
		assert_ne!(target_slot, old_last_slot);
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);
		assert_eq!(ratchet.receive_cache_len(), capacity as u8 - 1);
		assert_eq!(receive_slot(&ratchet, capacity), Some(target_slot));
		assert_key_material_eq(ratchet.recv_key(capacity).unwrap(), &old_last_material);
		assert!(ratchet.receive_entry_at(old_last_slot).is_none());

		let next_sequence = capacity + 1;
		assert_eq!(
			ratchet.ratchet_recv_until(next_sequence),
			Some(next_sequence)
		);
		assert_eq!(receive_slot(&ratchet, next_sequence), Some(old_last_slot));
		assert!(ratchet.receive_entry_at(old_last_slot).is_some());
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn cloned_receive_cache_remains_independent_after_non_last_removal() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB9; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(4), Some(4));

		let cloned = ratchet.clone();
		let cloned_logical = logical_snapshot(&cloned);
		let cloned_chain = cloned.recv_state().as_slice().to_vec();
		let cloned_slots = receive_slot_snapshot(&cloned);
		assert_eq!(
			ratchet.complete_recv_key(2, true),
			verified_ratchet::ReceiveDisposition::Consumed
		);

		assert_eq!(logical_snapshot(&cloned), cloned_logical);
		assert_eq!(cloned.recv_state().as_slice(), cloned_chain);
		assert_eq!(receive_slot_snapshot(&cloned), cloned_slots);
		assert_eq!(receive_slot(&cloned, 2), Some(1));
		assert_eq!(receive_slot(&cloned, 4), Some(3));
		assert_eq!(receive_slot(&ratchet, 2), None);
		assert_eq!(receive_slot(&ratchet, 4), Some(1));
		assert_receive_slots_aligned(&cloned);
		assert_receive_slots_aligned(&ratchet);
	}

	#[test]
	fn production_send_advances_the_refined_kernel_once() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xB2; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);

		let encrypted =
			encrypt_message_with_ratchet(b"one use", 7, 9, &[0xB3; AD_SIZE], &mut ratchet).unwrap();
		assert_eq!(encrypted.seq, 1);
		assert_eq!(ratchet.send_sequence(), 1);
	}

	#[test]
	fn refined_receive_state_serializes_only_paired_entries() {
		let mut ratchet = RatchetManager::default();
		ratchet.init_ratchets(
			&[0xBA; KDF_STATE_SIZE],
			beaconcrypt_protocol_core::pqxdh::beacon_ratchet_initialization(),
		);
		assert_eq!(ratchet.ratchet_recv_until(2), Some(2));
		assert_receive_slots_aligned(&ratchet);

		let serialized = serde_json::to_value(&ratchet).unwrap();
		let recv_past = serialized["recv_past"].as_object().unwrap();
		assert_eq!(recv_past.len(), 2);
		assert!(recv_past.contains_key("1"));
		assert!(recv_past.contains_key("2"));
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
		assert!(principal.ratchet().recv_key(1).is_none());
		assert_eq!(principal.ratchet_mut().ratchet_recv(), Some(1),);
		assert!(principal.ratchet().recv_key(1).is_some());
	}
}
