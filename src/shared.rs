// SPDX-License-Identifier: 0BSD

use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, Mutex};
use std::{mem, vec};

use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
#[cfg(feature = "ml-dsa")]
use libcrux_ml_dsa::ml_dsa_65;
use libsodium_rs::{
	SodiumError, crypto_aead, crypto_kdf, crypto_kem, crypto_kx, crypto_sign, ensure_init,
};
use zeroize::{Zeroize, Zeroizing};

use crate::error::{DecodingError, EncodingError};
use crate::{cryptoframe_capnp, protogram_capnp};

pub const PQXDH_INFO: &[u8; 35] = b"Pqxdh_CURVE25519_SHA-512_ML-KEM-768";
pub const KEX_KDF_OUT_LEN: usize = 32usize;
pub const KDF_STATE_SIZE: usize = 32usize;
pub const SYM_RATCHET_INFO: &[u8; 41] = b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305";
pub const AD_SIZE: usize =
	PQXDH_INFO.len() + SYM_RATCHET_INFO.len() + ((crypto_sign::PUBLICKEYBYTES + 1) * 2);
/// crypto_aead::chacha20poly1305_ietf::KEYBYTES
pub const AEAD_KEY_LEN: usize = 32;
/// crypto_aead::chacha20poly1305_ietf::NPUBBYTES
pub const AEAD_NONCE_LEN: usize = 12;
pub const KDF_RATCHET_OUTPUT_LEN: usize = AEAD_KEY_LEN + KDF_STATE_SIZE + AEAD_NONCE_LEN;
/// crypto_scalarmult::BYTES
pub const DH_OUT_LEN: usize = 32;
// the maximum amounts of out-of-order messages we tolerate
pub const RATCHET_MAX_GAP: u64 = 50;
#[cfg(feature = "ml-dsa")]
const ML_DSA_RAND_SIZE: usize = libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE;

pub static STATE: LazyLock<Mutex<BeaconCryptAgent>> =
	LazyLock::new(|| Mutex::new(BeaconCryptAgent::default()));
pub static INITIALIZED: AtomicBool = AtomicBool::new(false);

#[repr(u8)]
pub enum CurveType {
	Undefined = 0,
	Ed25519 = 1,
	X25519 = 2,
}

impl From<CurveType> for u8 {
	fn from(value: CurveType) -> Self {
		match value {
			CurveType::Undefined => 0,
			CurveType::Ed25519 => 1,
			CurveType::X25519 => 2,
		}
	}
}

impl From<u8> for CurveType {
	fn from(value: u8) -> Self {
		match value {
			1 => Self::Ed25519,
			2 => Self::X25519,
			_ => Self::Undefined,
		}
	}
}

#[repr(u8)]
pub enum KemType {
	Undefined = 0,
	MlKem768 = 1,
}

impl From<KemType> for u8 {
	fn from(value: KemType) -> Self {
		match value {
			KemType::Undefined => 0,
			KemType::MlKem768 => 1,
		}
	}
}

impl From<u8> for KemType {
	fn from(value: u8) -> Self {
		match value {
			1 => Self::MlKem768,
			_ => Self::Undefined,
		}
	}
}

pub fn encode_ec(curve_type: CurveType, pk_bytes: &[u8]) -> Result<Vec<u8>, EncodingError> {
	match curve_type {
		CurveType::Undefined => Err(EncodingError),
		CurveType::Ed25519 => {
			let mut byt = Vec::from(pk_bytes);
			byt.insert(0, curve_type.into());
			Ok(byt)
		}
		CurveType::X25519 => {
			let mut byt = Vec::from(pk_bytes);
			byt.insert(0, curve_type.into());
			Ok(byt)
		}
	}
}

pub fn decode_ec(encoded_pk: &[u8]) -> Result<Vec<u8>, DecodingError> {
	if encoded_pk.len() < crypto_kx::PUBLICKEYBYTES + 1 {
		return Err(DecodingError);
	}
	match CurveType::from(encoded_pk[0]) {
		CurveType::Undefined => Err(DecodingError),
		CurveType::Ed25519 => {
			let mut key = vec![0u8; crypto_sign::PUBLICKEYBYTES + 1];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
		CurveType::X25519 => {
			let mut key = vec![0u8; crypto_kx::PUBLICKEYBYTES + 1];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
	}
}

pub fn encode_kem(kem_type: KemType, pk_bytes: &[u8]) -> Result<Vec<u8>, EncodingError> {
	match kem_type {
		KemType::Undefined => Err(EncodingError),
		KemType::MlKem768 => {
			let mut byt = Vec::from(pk_bytes);
			byt.insert(0, kem_type.into());
			Ok(byt)
		}
	}
}

#[cfg(feature = "server")]
pub fn decode_kem(encoded_pk: &[u8]) -> Result<Vec<u8>, DecodingError> {
	if encoded_pk.len() < crypto_kem::mlkem768::PUBLICKEYBYTES + 1 {
		return Err(DecodingError);
	}
	match KemType::from(encoded_pk[0]) {
		KemType::Undefined => Err(DecodingError),
		KemType::MlKem768 => {
			let mut key = vec![0u8; crypto_kem::mlkem768::PUBLICKEYBYTES + 1];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
	}
}

mod systems {
	pub struct X25519;
	pub struct Hkdf;
	#[cfg(feature = "server")]
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
	fn as_slice(&self) -> &[u8] {
		self.data.as_slice()
	}

	pub fn copy_from_slice(&mut self, src: &[u8]) {
		self.data.copy_from_slice(src);
	}

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

pub type DhSecret = SecretArr<DH_OUT_LEN, systems::X25519, roles::DerivedSecret>;
pub type KdfState = SecretArr<KDF_STATE_SIZE, systems::Hkdf, roles::ChainKey>;
#[cfg(feature = "server")]
pub type PqxdhSecret = SecretArr<KDF_STATE_SIZE, systems::Pqxdh, roles::DerivedSecret>;

#[cfg(feature = "server")]
#[derive(Clone)]
pub struct RegistrationOutput {
	pub kem_ciphertext: crypto_kem::mlkem768::Ciphertext,
	pub derived_secret: PqxdhSecret,
	pub ephemeral: crypto_kx::PublicKey,
	pub public_key: crypto_sign::PublicKey,
}

/// This function is safe to call multiple times
/// ## Arguments
///
/// * `is_beacon` - Whether the current instance is a beacon
/// * `server_seq` - The ID of the server's identity key for the campaign
#[unsafe(no_mangle)]
pub extern "C" fn init(is_beacon: bool, server_seq: u64) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		*state = BeaconCryptAgent::new(is_beacon, server_seq, None);
	}
}

pub struct KeyMaterial {
	key: AeadKey,
	nonce: AeadNonce,
}

impl KeyMaterial {
	fn get_key(&self) -> &crypto_aead::chacha20poly1305_ietf::Key {
		&self.key
	}

	fn get_nonce(&self) -> &crypto_aead::chacha20poly1305_ietf::Nonce {
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

	pub fn get_send_key(&self, id: u64) -> Option<&KeyMaterial> {
		self.send_past.get(&id)
	}

	pub fn get_recv_key(&self, id: u64) -> Option<&KeyMaterial> {
		self.recv_past.get(&id)
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
		if until < self.recv_ctr || until > self.recv_ctr + RATCHET_MAX_GAP {
			None
		} else if until == self.recv_ctr {
			Some(until)
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
		let mut first_start: usize = 0;
		let mut second_start: usize = KDF_STATE_SIZE;
		if !is_beacon {
			first_start = KDF_STATE_SIZE;
			second_start = 0;
		}
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

	pub fn delete_send_key(&mut self, id: u64) {
		self.send_past.remove(&id);
	}

	pub fn delete_recv_key(&mut self, id: u64) {
		self.recv_past.remove(&id);
	}
}

struct RemotePrincipal {
	pk: crypto_sign::PublicKey,
	ratchet: RatchetManager,
}

impl RemotePrincipal {
	fn new(pk: crypto_sign::PublicKey, ratchet: RatchetManager) -> Self {
		Self { pk, ratchet }
	}

	pub fn get_pk(&self) -> &crypto_sign::PublicKey {
		&self.pk
	}

	pub fn get_ratchet(&self) -> &RatchetManager {
		&self.ratchet
	}

	pub fn get_ratchet_mut(&mut self) -> &mut RatchetManager {
		&mut self.ratchet
	}
}

pub struct BeaconCryptAgent {
	identity_key_pk: crypto_sign::PublicKey,
	identity_key_sk: crypto_sign::SecretKey,
	#[cfg(feature = "ml-dsa")]
	identity_pq: libcrux_ml_dsa::ml_dsa_65::MLDSA65KeyPair,
	identity_key_kid: u64,

	prekey_pk: crypto_kx::PublicKey,
	prekey_sk: crypto_kx::SecretKey,

	onetime_key_pk: crypto_kx::PublicKey,
	onetime_key_sk: crypto_kx::SecretKey,

	pq_key_pk: crypto_kem::mlkem768::PublicKey,
	pq_key_sk: crypto_kem::mlkem768::SecretKey,

	additional_data: [u8; AD_SIZE],
	// unfortunately we can't use static generics so we have to store the role at runtime
	is_beacon: bool,
	// stores the server's `seq` for the beacon. Stores the counter of remote `seq`s for the server
	server_kid: u64,
	known_ids: HashMap<u64, RemotePrincipal>,
}

impl Default for BeaconCryptAgent {
	fn default() -> Self {
		Self {
			// our cryptographic identity, this is unique to the specific agent instance and uniquely identifies it to the server
			identity_key_pk: crypto_sign::PublicKey::from_bytes(
				&[0u8; crypto_sign::PUBLICKEYBYTES],
			)
			.unwrap(),
			identity_key_sk: crypto_sign::SecretKey::from_bytes(
				&[0u8; crypto_sign::SECRETKEYBYTES],
			)
			.unwrap(),
			#[cfg(feature = "ml-dsa")]
			identity_pq: libcrux_ml_dsa::ml_dsa_65::generate_key_pair(
				[0u8; libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE],
			),
			identity_key_kid: 0,

			prekey_pk: crypto_kx::PublicKey::from_bytes(&[0u8; crypto_kx::PUBLICKEYBYTES]).unwrap(),
			prekey_sk: crypto_kx::SecretKey::from_bytes(&[0u8; crypto_kx::SECRETKEYBYTES]).unwrap(),

			onetime_key_pk: crypto_kx::PublicKey::from_bytes(&[0u8; crypto_kx::PUBLICKEYBYTES])
				.unwrap(),
			onetime_key_sk: crypto_kx::SecretKey::from_bytes(&[0u8; crypto_kx::SECRETKEYBYTES])
				.unwrap(),

			pq_key_pk: crypto_kem::mlkem768::PublicKey::from_bytes(
				&[0u8; crypto_kem::mlkem768::PUBLICKEYBYTES],
			)
			.unwrap(),
			pq_key_sk: crypto_kem::mlkem768::SecretKey::from_bytes(
				&[0u8; crypto_kem::mlkem768::SECRETKEYBYTES],
			)
			.unwrap(),

			additional_data: [0u8; AD_SIZE],
			is_beacon: true,
			server_kid: 0,
			known_ids: HashMap::new(),
		}
	}
}

impl BeaconCryptAgent {
	pub fn new(is_beacon: bool, server_kid: u64, server_pk: Option<&[u8]>) -> Self {
		ensure_init().expect("Failed to initialize libsodium");

		let id_keypair = crypto_sign::KeyPair::generate().unwrap();
		let prekey = crypto_kx::KeyPair::generate().unwrap();
		let onetime = crypto_kx::KeyPair::generate().unwrap();
		let pqkey = crypto_kem::mlkem768::KeyPair::generate().unwrap();
		#[cfg(feature = "ml-dsa")]
		let binding = libsodium_rs::random::bytes(libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE);
		#[cfg(feature = "ml-dsa")]
		let pq_sig_rand = *binding.as_array::<ML_DSA_RAND_SIZE>().unwrap();
		let known = if let Some(pk) = server_pk {
			let mut hm = HashMap::new();
			hm.insert(
				server_kid,
				RemotePrincipal::new(
					crypto_sign::PublicKey::from_bytes(&pk).unwrap(),
					RatchetManager::new(),
				),
			);
			hm
		} else {
			HashMap::new()
		};

		Self {
			identity_key_pk: id_keypair.public_key,
			identity_key_sk: id_keypair.secret_key,
			#[cfg(feature = "ml-dsa")]
			identity_pq: libcrux_ml_dsa::ml_dsa_65::generate_key_pair(pq_sig_rand),
			// this will be overwritten when the agent registers
			identity_key_kid: server_kid,
			prekey_pk: prekey.public_key,
			prekey_sk: prekey.secret_key,
			onetime_key_pk: onetime.public_key,
			onetime_key_sk: onetime.secret_key,
			pq_key_pk: pqkey.public_key,
			pq_key_sk: pqkey.secret_key,
			additional_data: [0u8; AD_SIZE],
			is_beacon,
			server_kid,
			known_ids: known,
		}
	}

	/// ## Arguments
	/// * `data`   - Some a serialized `CryptoFrame` to be decrypted
	/// * `stob` - The identifier of the party who encrypted `data`
	/// * `is_beacon` - Whether the caller is a beacon
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `cryptoframe_capnp::crypto_frame`
	pub fn decrypt_message(&mut self, data: &[u8], kid: u64, stob: bool) -> Option<Vec<u8>> {
		let associated_data = self.additional_data;
		match capnp::serialize::read_message(data, ReaderOptions::new()) {
			Ok(reader) => {
				let typed_reader =
					TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
				match typed_reader.get() {
					Ok(frame) => {
						if frame.get_s_to_b() != stob {
							return None;
						}
						let key_seq =
							self.ratchet_recv_until(SYM_RATCHET_INFO, frame.get_seq(), kid)?;
						let key = self.get_recv_key(key_seq, kid)?;
						let plaintext = crypto_aead::chacha20poly1305_ietf::decrypt(
							frame.get_cipher_text().unwrap(),
							Some(associated_data.as_slice()),
							key.get_nonce(),
							key.get_key(),
						);
						self.delete_recv_key(key_seq, kid);
						plaintext.ok()
					}
					Err(_) => None,
				}
			}
			Err(_) => None,
		}
	}

	/// ## Arguments
	/// * `data`   - Some arbitrary byte buffer to be encrypted
	/// * `stob` - The direction of this message
	/// * `seq` - The identifier for the remote to encrypt to
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `cryptoframe_capnp::crypto_frame`
	pub fn encrypt_message(&mut self, bytes: &[u8], stob: bool, seq: u64) -> Option<Vec<u8>> {
		let associated_data = self.additional_data;
		let key_seq = self.ratchet_send(SYM_RATCHET_INFO, seq)?;
		let key = self.get_send_key(key_seq, seq)?;
		let plaintext = crypto_aead::chacha20poly1305_ietf::encrypt(
			&bytes,
			Some(associated_data.as_slice()),
			key.get_nonce(),
			key.get_key(),
		);
		self.delete_send_key(key_seq, seq);
		match plaintext {
			Ok(plaintext) => {
				let mut t_builder =
					TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
				let mut builder: cryptoframe_capnp::crypto_frame::Builder<'_> =
					t_builder.init_root();
				builder.set_cipher_text(&plaintext);
				builder.set_s_to_b(stob);
				builder.set_seq(key_seq);
				let mut buffer = vec![];
				capnp::serialize::write_message(&mut buffer, t_builder.borrow_inner()).unwrap();
				Some(buffer)
			}
			Err(_) => None,
		}
	}

	/// ## Arguments
	/// * `data`   - buffer to be signed, probably should be a serialized `cryptoframe_capnp::crypto_frame`
	pub fn sign_message(&self, data: &[u8]) -> Option<Vec<u8>> {
		let mut t_builder: TypedBuilder<protogram_capnp::proto_gram::Owned> =
			TypedBuilder::<protogram_capnp::proto_gram::Owned>::new_default();
		let mut builder: protogram_capnp::proto_gram::Builder<'_> = t_builder.init_root();
		builder.set_key_seq(self.identity_key_kid);
		let signed = crypto_sign::sign(&data, self.get_identity_sk()).ok()?;
		builder.set_data(&signed);
		let mut buffer = vec![];
		capnp::serialize_packed::write_message(&mut buffer, t_builder.borrow_inner()).unwrap();
		Some(buffer)
	}

	pub fn set_identity_kid(&mut self, key_id: u64) {
		self.identity_key_kid = key_id;
	}

	/// ## Arguments
	/// * `data`   - wire buffer to check the signature for, MUST be a serialized `protogram_capnp::proto_gram`
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	pub fn verify_signature(&self, data: &[u8]) -> Option<Vec<u8>> {
		let t_reader = create_protogram_reader(data)?;
		let reader = t_reader.get().ok()?;
		let message = reader.get_data().ok()?;
		// hardcode this to avoid potential confusion
		if self.is_beacon {
			crypto_sign::verify(message, self.get_server_id()?)
		} else {
			crypto_sign::verify(message, self.get_id_by_seq(reader.get_key_seq())?)
		}
	}

	pub fn add_known_kid(&mut self, key_id: u64, pk: crypto_sign::PublicKey) {
		self.known_ids
			.entry(key_id)
			.or_insert(RemotePrincipal::new(pk, RatchetManager::new()));
	}

	pub fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		self.additional_data = data
	}

	pub fn add_server_pk(&mut self, pk: crypto_sign::PublicKey) {
		self.add_known_kid(self.server_kid, pk)
	}

	pub fn get_server_id(&self) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&self.server_kid) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	pub fn get_server_kid(&self) -> u64 {
		self.server_kid
	}

	pub fn get_id_by_seq(&self, seq: u64) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&seq) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	pub fn get_identity_pk(&self) -> &crypto_sign::PublicKey {
		&self.identity_key_pk
	}

	pub fn get_identity_sk(&self) -> &crypto_sign::SecretKey {
		&self.identity_key_sk
	}

	pub fn get_prekey_pk(&self) -> &crypto_kx::PublicKey {
		&self.prekey_pk
	}

	pub fn get_prekey_sk(&self) -> &crypto_kx::SecretKey {
		&self.prekey_sk
	}

	pub fn get_onetime_pk(&self) -> &crypto_kx::PublicKey {
		&self.onetime_key_pk
	}

	pub fn get_onetime_sk(&self) -> &crypto_kx::SecretKey {
		&self.onetime_key_sk
	}

	pub fn get_pq_pk(&self) -> &crypto_kem::mlkem768::PublicKey {
		&self.pq_key_pk
	}

	pub fn get_pq_sk(&self) -> &crypto_kem::mlkem768::SecretKey {
		&self.pq_key_sk
	}

	pub fn get_ratchet_manager(&self, kid: u64) -> Option<&RatchetManager> {
		if let Some(remote) = self.known_ids.get(&kid) {
			Some(remote.get_ratchet())
		} else {
			None
		}
	}

	pub fn get_ratchet_manager_mut(&mut self, kid: u64) -> Option<&mut RatchetManager> {
		if let Some(remote) = self.known_ids.get_mut(&kid) {
			Some(remote.get_ratchet_mut())
		} else {
			None
		}
	}

	/// ## Arguments
	/// * `info` - The info buffer to use for the ratchet step(s)
	/// * `until` - The message sequence number to ratchet to
	/// * `seq` - The identity to ratchet for
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	pub fn ratchet_recv_until(&mut self, info: &[u8], until: u64, kid: u64) -> Option<u64> {
		let remote = self.get_ratchet_manager_mut(kid)?;
		remote.ratchet_recv_until(info, until)
	}

	pub fn ratchet_send(&mut self, info: &[u8], kid: u64) -> Option<u64> {
		let remote = self.get_ratchet_manager_mut(kid)?;
		remote.ratchet_send(info)
	}

	pub fn get_send_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.get_ratchet_manager(kid) {
			Some(remote) => remote.get_send_key(seq),
			None => None,
		}
	}

	pub fn get_recv_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.get_ratchet_manager(kid) {
			Some(remote) => remote.get_recv_key(seq),
			None => None,
		}
	}

	pub fn delete_send_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.get_ratchet_manager_mut(kid) {
			remote.delete_send_key(seq)
		}
	}

	pub fn delete_recv_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.get_ratchet_manager_mut(kid) {
			remote.delete_recv_key(seq)
		}
	}

	/// You must call `BeaconCryptAgent::add_known_id` or `BeaconCryptAgent::add_server_id` before this
	pub fn init_ratchets(&mut self, ikm: &[u8], info: &[u8], is_beacon: bool, seq: u64) -> bool {
		match self.get_ratchet_manager_mut(seq) {
			Some(remote) => {
				remote.init_ratchets(ikm, info, is_beacon);
				true
			}
			None => false,
		}
	}

	#[cfg(feature = "server")]
	pub fn new_remote_kid(&mut self) -> u64 {
		self.server_kid += 1;
		self.server_kid
	}
}

pub fn derive_root_key(
	dh1: DhSecret,
	dh2: DhSecret,
	dh3: DhSecret,
	dh4: DhSecret,
	shared_secret: crypto_kem::mlkem768::SharedSecret,
) -> Result<Vec<u8>, SodiumError> {
	// make sure to start inserting after sizeof(Ed25519) so the first bytes are filled with 0xFF as per the spec:
	// https://signal.org/docs/specifications/pqxdh/#cryptographic-notation
	let mut ikm = vec![0xFFu8; crypto_kx::PUBLICKEYBYTES];
	ikm.extend_from_slice(dh1.as_slice());
	ikm.extend_from_slice(dh2.as_slice());
	ikm.extend_from_slice(dh3.as_slice());
	ikm.extend_from_slice(dh4.as_slice());
	ikm.extend_from_slice(shared_secret.as_bytes());

	let prk = crypto_kdf::hkdf::sha512::extract(None, &ikm)?;
	crypto_kdf::hkdf::sha512::expand(KEX_KDF_OUT_LEN, Some(PQXDH_INFO), &prk)
}

pub fn build_additional_data(
	server_id: crypto_sign::PublicKey,
	beacon_id: crypto_sign::PublicKey,
) -> [u8; AD_SIZE] {
	let mut buffer = vec![0u8; 0];
	let mut kex_proto = [0u8; PQXDH_INFO.len()];
	kex_proto.copy_from_slice(PQXDH_INFO);
	buffer.extend_from_slice(&kex_proto);
	let mut sym_proto = [0u8; SYM_RATCHET_INFO.len()];
	sym_proto.copy_from_slice(SYM_RATCHET_INFO);
	buffer.extend_from_slice(&sym_proto);
	let mut encoded_server = encode_ec(CurveType::Ed25519, server_id.as_bytes()).unwrap();
	buffer.append(&mut encoded_server);
	let mut encoded_beacon = encode_ec(CurveType::Ed25519, beacon_id.as_bytes()).unwrap();
	buffer.append(&mut encoded_beacon);
	*buffer.as_array::<AD_SIZE>().unwrap()
}

/// # Safety
/// * This function MUST only be called to clean up byte buffers returned by this library, do NOT use as a general `free`
/// * `ptr` should NOT be null and should point to a byte buffer of `len` length, in bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn free_vec(ptr: *mut u8, len: usize, capa: usize) {
	if !ptr.is_null() {
		unsafe { Vec::from_raw_parts(ptr, len, capa) };
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

/// The beacon calls this to set its ID to that which it got from the server upon registering. In must be called exactly once. The server should not have a use for this.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn set_identity_seq(seq: u64) {
	let mut state = STATE.lock().unwrap();
	state.set_identity_kid(seq);
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - A serialized `protogram_capnp::proto_gram`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn verify_signature(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let state = STATE.lock().unwrap();
	match state.verify_signature(data_vec.as_slice()) {
		Some(mut verified) => {
			unsafe {
				_out = verified.as_mut_ptr();
				*out_len = verified.len();
				*out_capa = verified.capacity();
				mem::forget(verified);
			};
			0
		}
		None => -1,
	}
}

/// # Safety
/// * `bytes` should NOT be null and should point to a byte buffer of `bytes_len` length, in bytes.
/// * The library will overwrite all the `out` parameters
/// * It is not safe to read the `out` parameters if the function doesn't return `0`
///
/// ## Arguments
/// * `bytes` - Buffer to sign, probably should be a `cryptoframe_capnp::crypto_frame`
/// * `bytes_len` - The size of the `bytes` buffer
/// * `out` - A caller-managed pointer that will contain the results in case of success. Call `free_vec` to free it once you're done
/// * `out_len` - The actual size of the `out` buffer
/// * `out_capa` - The size of the underlying allocation for the `out` buffer
///
/// ## Returns
/// `0` on success, negative values on error
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sign_message(
	bytes: *const u8,
	bytes_len: usize,
	mut _out: *mut u8,
	out_len: *mut usize,
	out_capa: *mut usize,
) -> i32 {
	if bytes.is_null() || bytes_len == 0 {
		return -1;
	}
	let data_vec = unsafe { vec::Vec::from_raw_parts(bytes.cast_mut(), bytes_len, bytes_len) };
	let state = STATE.lock().unwrap();
	match state.sign_message(data_vec.as_slice()) {
		Some(mut signed) => {
			unsafe {
				_out = signed.as_mut_ptr();
				*out_len = signed.len();
				*out_capa = signed.capacity();
				mem::forget(signed);
			};
			0
		}
		None => -1,
	}
}
