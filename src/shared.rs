// SPDX-License-Identifier: 0BSD

#[cfg(feature = "cnsa2")]
use crate::cnsa2::{AD_SIZE, BeaconCryptCnsa2};
use crate::error::{DecodingError, EncodingError};
#[cfg(feature = "pqxdh")]
use crate::pqxdh::{AD_SIZE, BeaconCryptPqxdh};
use crate::{cryptoframe_capnp, protogram_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{crypto_aead, crypto_kdf};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, Mutex};
use std::{mem, vec};
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
#[cfg(feature = "cnsa2")]
pub const KEM_SHARED_SECRET_SIZE: usize = 32;

#[cfg(feature = "pqxdh")]
pub type Provider = BeaconCryptPqxdh;
#[cfg(feature = "cnsa2")]
pub type Provider = BeaconCryptCnsa2;

pub static STATE: LazyLock<Mutex<Provider>> = LazyLock::new(|| Mutex::new(Provider::default()));
pub static INITIALIZED: AtomicBool = AtomicBool::new(false);

#[repr(u8)]
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

pub fn decode_sign(encoded_pk: &[u8]) -> Result<Vec<u8>, DecodingError> {
	match SignType::from(encoded_pk[0]) {
		SignType::Undefined => Err(DecodingError),
		_ => {
			let mut key = vec![0u8; encoded_pk.len()];
			key.copy_from_slice(encoded_pk);
			key.remove(0);
			Ok(key)
		}
	}
}

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
pub fn decode_kem(encoded_pk: &[u8]) -> Result<Vec<u8>, DecodingError> {
	match KemType::from(encoded_pk[0]) {
		KemType::Undefined => Err(DecodingError),
		_ => {
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
	#[cfg(feature = "cnsa2")]
	pub struct MlKem;
}
mod roles {
	pub struct ChainKey;
	pub struct DerivedSecret;
	#[cfg(feature = "cnsa2")]
	pub struct SharedSecret;
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
#[cfg(feature = "cnsa2")]
pub type MlKemSharedSecret = SecretArr<KEM_SHARED_SECRET_SIZE, systems::MlKem, roles::SharedSecret>;

/// This function is safe to call multiple times
/// ## Arguments
///
/// * `is_beacon` - Whether the current instance is a beacon
/// * `server_seq` - The ID of the server's identity key for the campaign
#[unsafe(no_mangle)]
pub extern "C" fn init(is_beacon: bool, server_seq: u64) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		*state = Provider::new(is_beacon, server_seq, None, None);
	}
}

pub struct KeyMaterial {
	key: AeadKey,
	nonce: AeadNonce,
}

impl KeyMaterial {
	fn get_key(&self) -> &AeadKey {
		&self.key
	}

	fn get_nonce(&self) -> &AeadNonce {
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

	pub fn delete_send_key(&mut self, id: u64) {
		self.send_past.remove(&id);
	}

	pub fn delete_recv_key(&mut self, id: u64) {
		self.recv_past.remove(&id);
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

	pub fn get_pk(&self) -> &PkType {
		&self.pk
	}

	pub fn get_ratchet(&self) -> &RatchetManager {
		&self.ratchet
	}

	pub fn get_ratchet_mut(&mut self) -> &mut RatchetManager {
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
	fn get_associated_data(&self) -> [u8; AD_SIZE];
	/// ## Arguments
	/// * `data`   - Some a serialized `CryptoFrame` to be decrypted
	/// * `stob` - The identifier of the party who encrypted `data`
	/// * `is_beacon` - Whether the caller is a beacon
	///
	/// ## Returns
	/// * `None` if some other error happens.
	/// * `Vec<u8>` containing a serialized `cryptoframe_capnp::crypto_frame`
	fn decrypt_message(&mut self, data: &[u8], kid: u64, stob: bool) -> Option<Vec<u8>> {
		let associated_data = self.get_associated_data();
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
	fn encrypt_message(&mut self, bytes: &[u8], stob: bool, seq: u64) -> Option<Vec<u8>> {
		let associated_data = self.get_associated_data();
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
	fn sign_message(&self, data: &[u8]) -> Option<Vec<u8>>;
	fn verify_signature(&self, data: &[u8]) -> Option<Vec<u8>>;
	fn set_identity_kid(&mut self, key_id: u64);
	fn new_remote_kid(&mut self) -> u64;
	fn add_known_kid(&mut self, key_id: u64, pk: Self::SignaturePublicKey);
	fn get_server_id(&self) -> Option<&Self::SignaturePublicKey>;
	fn get_server_kid(&self) -> u64;
	fn add_server_pk(&mut self, pk: Self::SignaturePublicKey) {
		self.add_known_kid(self.get_server_kid(), pk)
	}
	fn get_id_by_seq(&self, seq: u64) -> Option<&Self::SignaturePublicKey>;
	fn get_identity_pk(&self) -> &Self::SignaturePublicKey;
	fn get_identity_sk(&self) -> &Self::SignatureSecretKey;
	fn get_pq_pk(&self) -> Option<&Self::KemPublicKey>;
	fn get_pq_sk(&self) -> Option<&Self::KemSecretKey>;
	fn get_ratchet_manager(&self, kid: u64) -> Option<&RatchetManager>;
	fn get_ratchet_manager_mut(&mut self, kid: u64) -> Option<&mut RatchetManager>;
	/// ## Arguments
	/// * `info` - The info buffer to use for the ratchet step(s)
	/// * `until` - The message sequence number to ratchet to
	/// * `seq` - The identity to ratchet for
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	fn ratchet_recv_until(&mut self, info: &[u8], until: u64, kid: u64) -> Option<u64> {
		let remote = self.get_ratchet_manager_mut(kid)?;
		remote.ratchet_recv_until(info, until)
	}

	fn ratchet_send(&mut self, info: &[u8], kid: u64) -> Option<u64> {
		let remote = self.get_ratchet_manager_mut(kid)?;
		remote.ratchet_send(info)
	}
	fn get_send_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.get_ratchet_manager(kid) {
			Some(remote) => remote.get_send_key(seq),
			None => None,
		}
	}

	fn get_recv_key(&self, seq: u64, kid: u64) -> Option<&KeyMaterial> {
		match self.get_ratchet_manager(kid) {
			Some(remote) => remote.get_recv_key(seq),
			None => None,
		}
	}

	fn delete_send_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.get_ratchet_manager_mut(kid) {
			remote.delete_send_key(seq)
		}
	}

	fn delete_recv_key(&mut self, seq: u64, kid: u64) {
		if let Some(remote) = self.get_ratchet_manager_mut(kid) {
			remote.delete_recv_key(seq)
		}
	}

	/// You must call `add_known_id` or `add_server_id` before this
	fn init_ratchets(&mut self, ikm: &[u8], info: &[u8], is_beacon: bool, seq: u64) -> bool {
		match self.get_ratchet_manager_mut(seq) {
			Some(remote) => {
				remote.init_ratchets(ikm, info, is_beacon);
				true
			}
			None => false,
		}
	}
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
