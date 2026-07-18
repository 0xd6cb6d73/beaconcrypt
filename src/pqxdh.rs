// SPDX-License-Identifier: 0BSD

use crate::beacon::ProviderBeacon;
use crate::server::{ProviderServer, RegResponse, RegistrationOutput};
use crate::shared::{
	DhSecret, ED25519_SEED_SIZE, INITIALIZED, KEX_KDF_OUT_LEN, KemType, Provider,
	REGISTRATION_WITNESS, RatchetManager, RemotePrincipal, STATE, SYM_RATCHET_INFO, SignType,
	SignaturePk, VerifiedMessage, create_protogram_reader, decode_kem, decode_sign, encode_kem,
	encode_sign,
};
use crate::{CryptoProvider, phase1_capnp, phase2_capnp, protogram_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{
	SodiumError, crypto_kdf, crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init,
};
use std::collections::HashMap;
use std::mem::swap;
use std::ptr::slice_from_raw_parts;
use std::sync::atomic::Ordering;
use std::vec;

// https://signal.org/docs/specifications/pqxdh/#pqxdh-parameters: `info` An ASCII string identifying the application with a minimum length of 8 bytes
pub const PQXDH_INFO: &[u8; 46] = b"BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768";
pub const AD_SIZE: usize =
	PQXDH_INFO.len() + SYM_RATCHET_INFO.len() + ((crypto_sign::PUBLICKEYBYTES + 1) * 2);

impl SignaturePk for crypto_sign::PublicKey {}

pub struct BeaconCryptPqxdh {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,

	prekey: Option<crypto_kx::KeyPair>,

	onetime_key: Option<crypto_kx::KeyPair>,

	pq_key: Option<crypto_kem::mlkem768::KeyPair>,

	// only used by the beacon to cache the value, server computes it every time
	associated_data: Option<[u8; AD_SIZE]>,
	// unfortunately we can't use static generics so we have to store the role at runtime
	is_beacon: bool,
	// stores the server's `key_id` for the beacon. Stores the counter of remote `key_id`s for the server
	server_kid: u64,
	known_ids: HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
}

impl CryptoProvider for BeaconCryptPqxdh {
	type SignaturePublicKey = crypto_sign::PublicKey;
	type SignatureSecretKey = crypto_sign::SecretKey;
	type KemPublicKey = crypto_kem::mlkem768::PublicKey;
	type KemSecretKey = crypto_kem::mlkem768::SecretKey;

	fn default() -> Self {
		Self {
			// our cryptographic identity, this is unique to the specific agent instance and uniquely identifies it to the server
			identity_key: crypto_sign::KeyPair::from_seed(&[0u8; ED25519_SEED_SIZE]).unwrap(),
			identity_key_kid: 0,

			prekey: None,

			onetime_key: None,

			pq_key: None,

			associated_data: None,
			is_beacon: true,
			server_kid: 0,
			known_ids: HashMap::new(),
		}
	}
	fn new(
		is_beacon: bool,
		server_kid: u64,
		server_id_pk: Option<&[u8]>,
		id_seed: Option<&[u8]>,
	) -> Self {
		ensure_init().expect("Failed to initialize libsodium");

		let id_keypair = if !is_beacon {
			if let Some(seed) = id_seed {
				crypto_sign::KeyPair::from_seed(seed).unwrap()
			} else {
				crypto_sign::KeyPair::generate().unwrap()
			}
		} else {
			crypto_sign::KeyPair::generate().unwrap()
		};
		// the server doesn't use prekeys
		let prekey = if is_beacon {
			Some(crypto_kx::KeyPair::generate().unwrap())
		} else {
			None
		};
		// the server doesn't use its own ML-KEM keypair
		let pqkey = if is_beacon {
			Some(crypto_kem::mlkem768::KeyPair::generate().unwrap())
		} else {
			None
		};
		let known_id_pk = if let Some(pk) = server_id_pk {
			if !is_beacon {
				HashMap::new()
			} else {
				let mut hm = HashMap::new();
				hm.insert(
					server_kid,
					RemotePrincipal::new(
						crypto_sign::PublicKey::from_bytes(pk).unwrap(),
						RatchetManager::new(),
					),
				);
				hm
			}
		} else {
			HashMap::new()
		};

		Self {
			identity_key: id_keypair,
			// this will be overwritten when the agent registers
			identity_key_kid: server_kid,
			prekey,
			// only the beacon uses it, and it generated at registration time
			onetime_key: None,
			pq_key: pqkey,
			associated_data: None,
			is_beacon,
			server_kid,
			known_ids: known_id_pk,
		}
	}

	fn is_beacon(&self) -> bool {
		self.is_beacon
	}

	/// ## Arguments
	/// * `data`   - buffer to be signed, probably should be a serialized `cryptoframe_capnp::crypto_frame`
	fn sign_message(&self, data: &[u8]) -> Option<Vec<u8>> {
		let mut t_builder: TypedBuilder<protogram_capnp::proto_gram::Owned> =
			TypedBuilder::<protogram_capnp::proto_gram::Owned>::new_default();
		let mut builder: protogram_capnp::proto_gram::Builder<'_> = t_builder.init_root();
		builder.set_key_id(self.identity_key_kid);
		let signed = crypto_sign::sign(data, self.identity_sk()).ok()?;
		builder.set_data(&signed);
		let mut buffer = vec![];
		capnp::serialize_packed::write_message(&mut buffer, t_builder.borrow_inner()).ok()?;
		Some(buffer)
	}

	fn set_identity_kid(&mut self, key_id: u64) {
		self.identity_key_kid = key_id;
	}

	/// ## Arguments
	/// * `data`   - wire buffer to check the signature for, MUST be a serialized `protogram_capnp::proto_gram`
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	fn verify_signature(&self, data: &[u8]) -> Option<VerifiedMessage> {
		let t_reader = create_protogram_reader(data)?;
		let reader = t_reader.get().ok()?;
		let message = reader.get_data().ok()?;
		// hardcode this to avoid potential confusion
		let verified = if self.is_beacon {
			(
				self.server_kid(),
				crypto_sign::verify(message, self.server_id()?)?,
			)
		} else {
			let kid = reader.get_key_id();
			(kid, crypto_sign::verify(message, self.pk_by_kid(kid)?)?)
		};
		Some(VerifiedMessage {
			data: verified.1,
			key_id: verified.0,
		})
	}

	fn add_known_kid(&mut self, key_id: u64, pk: crypto_sign::PublicKey) {
		self.known_ids
			.entry(key_id)
			.or_insert(RemotePrincipal::new(pk, RatchetManager::new()));
	}

	fn delete_known_kid(&mut self, key_id: u64) {
		self.known_ids.remove(&key_id);
	}

	fn reset_known_kid(&mut self, key_id: u64) {
		if let Some(to_reset) = self.ratchet_manager_mut(key_id) {
			to_reset.reset()
		}
	}

	fn new_remote_kid(&mut self) -> u64 {
		self.server_kid += 1;
		self.server_kid
	}

	fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		self.associated_data = Some(data)
	}

	fn associated_data(&self, kid: u64) -> Option<[u8; AD_SIZE]> {
		if self.is_beacon {
			// the beacon must have set its associated data at the end of registration
			Some(self.associated_data?)
		} else {
			let k = self.pk_by_kid(kid)?;
			Some(build_associated_data(self.identity_pk().clone(), k.clone()))
		}
	}

	fn server_id(&self) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&self.server_kid) {
			Some(remote.pk())
		} else {
			None
		}
	}

	fn server_kid(&self) -> u64 {
		self.server_kid
	}

	fn pk_by_kid(&self, kid: u64) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&kid) {
			Some(remote.pk())
		} else {
			None
		}
	}

	fn identity_pk(&self) -> &crypto_sign::PublicKey {
		&self.identity_key.public_key
	}

	fn identity_sk(&self) -> &crypto_sign::SecretKey {
		&self.identity_key.secret_key
	}

	fn pq_pk(&self) -> Option<&crypto_kem::mlkem768::PublicKey> {
		match &self.pq_key {
			Some(key) => Some(&key.public_key),
			None => None,
		}
	}

	fn pq_sk(&self) -> Option<&crypto_kem::mlkem768::SecretKey> {
		match &self.pq_key {
			Some(key) => Some(&key.secret_key),
			None => None,
		}
	}

	fn ratchet_manager(&self, kid: u64) -> Option<&RatchetManager> {
		if let Some(remote) = self.known_ids.get(&kid) {
			Some(remote.ratchet())
		} else {
			None
		}
	}

	fn ratchet_manager_mut(&mut self, kid: u64) -> Option<&mut RatchetManager> {
		if let Some(remote) = self.known_ids.get_mut(&kid) {
			Some(remote.ratchet_mut())
		} else {
			None
		}
	}
}

impl BeaconCryptPqxdh {
	pub fn get_prekey_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.prekey {
			Some(key) => Some(&key.public_key),
			None => None,
		}
	}

	pub fn get_prekey_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.prekey {
			Some(key) => Some(&key.secret_key),
			None => None,
		}
	}

	pub fn get_onetime_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.onetime_key {
			Some(key) => Some(&key.public_key),
			None => None,
		}
	}

	pub fn get_onetime_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.onetime_key {
			Some(key) => Some(&key.secret_key),
			None => None,
		}
	}

	pub fn new_onetime_keypair(&mut self) -> Option<()> {
		self.onetime_key = Some(crypto_kx::KeyPair::generate().ok()?);
		Some(())
	}

	pub fn delete_onetime_keypair(&mut self) {
		if let Some(onetime) = &mut self.onetime_key {
			let mut keypair = crypto_kx::KeyPair::from_seed(&[0u8; ED25519_SEED_SIZE]).unwrap();
			swap(onetime, &mut keypair);
			self.onetime_key = None
		}
	}
}

#[cfg(feature = "beacon")]
impl ProviderBeacon for BeaconCryptPqxdh {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>> {
		use crate::shared::{SignType, encode_sign};

		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();

		let encoded_id = encode_sign(SignType::Ed25519, self.identity_pk().as_bytes()).ok()?;
		bundle.set_identity_key(&encoded_id);

		let encoded_prekey = encode_kem(KemType::X25519, self.get_prekey_pk()?.as_bytes()).ok()?;
		let prekey_sig = crypto_sign::sign(&encoded_prekey, self.identity_sk()).ok()?;
		bundle.set_pre_key(&prekey_sig);

		self.new_onetime_keypair()?;
		let encoded_onetime =
			encode_kem(KemType::X25519, self.get_onetime_pk()?.as_bytes()).ok()?;
		let onetime_sig = crypto_sign::sign(&encoded_onetime, self.identity_sk()).ok()?;
		bundle.set_one_time_key(&onetime_sig);

		let encoded_pq = encode_kem(KemType::MlKem768, self.pq_pk()?.as_bytes()).ok()?;
		let pq_sig = crypto_sign::sign(&encoded_pq, self.identity_sk()).ok()?;
		bundle.set_pq_key(&pq_sig);

		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		Some(buffer)
	}

	/// Returns the server's intitial message or a single 0xFF byte if the server didn't provide one. A return value of `None` MUST be treated as a protocol failure
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let response = typed_reader.get().ok()?;

		let kem_ciphertext =
			crypto_kem::mlkem768::Ciphertext::from_bytes(response.get_kem_cipher_text().ok()?)
				.ok()?;
		let ephemeral =
			crypto_kx::PublicKey::from_bytes(response.get_ephemeral_key().ok()?).ok()?;
		let server_id =
			crypto_sign::PublicKey::from_bytes(response.get_identity_key().ok()?).ok()?;
		if server_id != self.server_id()?.clone() {
			return None;
		}
		let server_kex_id = crypto_sign::ed25519_pk_to_curve25519(&server_id).ok()?;
		let beacon_kex_id = crypto_sign::ed25519_sk_to_curve25519(self.identity_sk()).ok()?;
		let shared_secret =
			crypto_kem::mlkem768::decapsulate(&kem_ciphertext, self.pq_sk()?).ok()?;
		let dh1: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk()?.as_bytes(), &server_kex_id)
				.ok()?
				.into();
		let dh2: DhSecret = crypto_scalarmult::scalarmult(&beacon_kex_id, ephemeral.as_bytes())
			.ok()?
			.into();
		let dh3: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk()?.as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let dh4: DhSecret =
			crypto_scalarmult::scalarmult(self.get_onetime_sk()?.as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, shared_secret).ok()?;
		self.delete_onetime_keypair();

		self.set_identity_kid(response.get_key_id());
		let id = self.identity_pk().clone();
		self.set_associated_data(build_associated_data(server_id, id));
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let srv_key_id = self.server_kid();
		self.init_ratchets(&derived_secret, &info_str, true, srv_key_id);

		match response.get_app_cipher_text() {
			// https://signal.org/docs/specifications/pqxdh/#receiving-the-initial-message
			Ok(ciphertext) => self.decrypt_message(ciphertext, srv_key_id).map_or_else(
				|| {
					// deletes the derived keychains but not the entire `RemotePrincipal` as the server is currently special-cased.
					// I think this matches the protocol's requirements: "If the initial ciphertext fails to decrypt, then Bob aborts the protocol and deletes SK".
					self.reset_known_kid(self.server_kid());
					self.set_identity_kid(self.server_kid());
					self.associated_data = None;
					None
				},
				// PQXDH protcol run is now complete and the beacon is successfully registered
				Some,
			),
			Err(_) => None,
		}
	}
}

#[cfg(feature = "server")]
impl ProviderServer for BeaconCryptPqxdh {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().ok()?;

		let decoded_beacon_id = decode_sign(registration.get_identity_key().ok()?).ok()?;
		let remote_id = crypto_sign::PublicKey::from_bytes(&decoded_beacon_id).ok()?;
		let pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id)?;
		let prekey_verified = crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id)?;
		let onetime_verified =
			crypto_sign::verify(registration.get_one_time_key().ok()?, &remote_id)?;

		let beacon_prekey =
			crypto_kx::PublicKey::from_bytes(&decode_kem(&prekey_verified).ok()?).ok()?;
		let beacon_onetime =
			crypto_kx::PublicKey::from_bytes(&decode_kem(&onetime_verified).ok()?).ok()?;
		let ephemeral = crypto_kx::KeyPair::generate().ok()?;
		let pq_pub =
			crypto_kem::mlkem768::PublicKey::from_bytes(&decode_kem(&pq_verified).ok()?).ok()?;
		let (kem_ciphertext, kem_shared) = crypto_kem::mlkem768::encapsulate(&pq_pub).ok()?;

		let remote_id_kex = crypto_sign::ed25519_pk_to_curve25519(&remote_id).ok()?;
		let id_kex_sk = crypto_sign::ed25519_sk_to_curve25519(self.identity_sk()).ok()?;
		let dh1: DhSecret = crypto_scalarmult::scalarmult(&id_kex_sk, beacon_prekey.as_bytes())
			.ok()?
			.into();
		let dh2: DhSecret =
			crypto_scalarmult::scalarmult(ephemeral.secret_key.as_bytes(), &remote_id_kex)
				.ok()?
				.into();
		let dh3: DhSecret = crypto_scalarmult::scalarmult(
			ephemeral.secret_key.as_bytes(),
			beacon_prekey.as_bytes(),
		)
		.ok()?
		.into();
		let dh4: DhSecret = crypto_scalarmult::scalarmult(
			ephemeral.secret_key.as_bytes(),
			beacon_onetime.as_bytes(),
		)
		.ok()?
		.into();

		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, kem_shared).ok()?;

		Some(RegistrationOutput {
			kem_ciphertext,
			derived_secret: derived_secret.into(),
			ephemeral: ephemeral.public_key,
			public_key: remote_id,
		})
	} // ephemeral and kem

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse> {
		// create the session on our end
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let remote_kid = self.new_remote_kid();
		self.add_known_kid(remote_kid, reg_out.public_key);
		self.init_ratchets(
			reg_out.derived_secret.inner().as_slice(),
			&info_str,
			false,
			remote_kid,
		);

		let mut msg = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
		let mut bundle = msg.init_root();
		bundle.set_key_id(self.server_kid());
		bundle.set_ephemeral_key(reg_out.ephemeral.as_bytes());
		bundle.set_identity_key(self.identity_pk().as_bytes());
		bundle.set_kem_cipher_text(reg_out.kem_ciphertext.as_bytes());

		let mut buffer = vec![];
		let ciphertext = if let Some(plaintext) = data {
			self.encrypt_message(plaintext, remote_kid)?
		} else {
			self.encrypt_message(REGISTRATION_WITNESS, remote_kid)?
		};
		bundle.set_app_cipher_text(&ciphertext);
		capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;

		Some(RegResponse {
			serialized: buffer,
			kid: remote_kid,
		})
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

pub fn build_associated_data(
	server_id: crypto_sign::PublicKey,
	beacon_id: crypto_sign::PublicKey,
) -> [u8; AD_SIZE] {
	// AD = EncodeEC(IKA) || EncodeEC(IKB) + what we choose, in this case both protocol strings
	let mut buffer = vec![0u8; 0];
	let mut encoded_server = encode_sign(SignType::Ed25519, server_id.as_bytes()).unwrap();
	buffer.append(&mut encoded_server);
	let mut encoded_beacon = encode_sign(SignType::Ed25519, beacon_id.as_bytes()).unwrap();
	buffer.append(&mut encoded_beacon);
	let mut kex_proto = [0u8; PQXDH_INFO.len()];
	kex_proto.copy_from_slice(PQXDH_INFO);
	buffer.extend_from_slice(&kex_proto);
	let mut sym_proto = [0u8; SYM_RATCHET_INFO.len()];
	sym_proto.copy_from_slice(SYM_RATCHET_INFO);
	buffer.extend_from_slice(&sym_proto);
	*buffer.as_array::<AD_SIZE>().unwrap()
}

/// Initialize a server with existing keys from seeds. This MUST only be called by a server
/// # Safety
/// This function is safe to call multiple times.
/// ## Arguments
///
/// * `server_kid` - The ID of the server's identity key for the campaign
/// * `id_seed` - 32 byte Ed25519 seed for the server's identity key
#[unsafe(no_mangle)]
pub extern "C" fn init_server_from_seeds(server_kid: u64, id_seed: *const u8) {
	if !INITIALIZED.swap(true, Ordering::AcqRel) {
		let mut state = STATE.lock().unwrap();
		let id_seed_slice = slice_from_raw_parts(id_seed, ED25519_SEED_SIZE);
		let mut id_seed_vec = vec![0u8; crypto_sign::PUBLICKEYBYTES];
		id_seed_vec.copy_from_slice(unsafe { id_seed_slice.as_ref().unwrap() });
		*state = Provider::new(false, server_kid, None, Some(&id_seed_vec));
	}
}

#[cfg(test)]
mod tests {
	use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
	use libsodium_rs::{crypto_kdf, crypto_kem, crypto_kx, crypto_sign};

	use super::{AD_SIZE, PQXDH_INFO, build_associated_data, derive_root_key};
	use crate::{
		BeaconCryptPqxdh,
		beacon::ProviderBeacon,
		phase1_capnp, protogram_capnp,
		server::ProviderServer,
		shared::{
			CryptoProvider, DH_OUT_LEN, DhSecret, ED25519_SEED_SIZE, SYM_RATCHET_INFO, decode_kem,
			decode_sign,
		},
	};

	fn test_register_beacon(
		server: &mut BeaconCryptPqxdh,
		beacon: &mut BeaconCryptPqxdh,
	) -> Vec<u8> {
		let message = [0xFFu8; 32];

		let phase_1 = beacon.get_registration_bundle().unwrap();
		let reg_out = server.get_shared_secret(&phase_1).unwrap();
		let phase2 = server
			.build_registration_response(reg_out, Some(&message))
			.unwrap();
		beacon.finish_registration(&phase2.serialized).unwrap()
	}

	#[test]
	fn server_can_register_multiple() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let b1_reg = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let b2_reg = test_register_beacon(&mut server, &mut b2);

		assert_eq!(b1_reg, b2_reg);
	}

	#[test]
	fn server_encrypt_to_multiple() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let _ = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let _ = test_register_beacon(&mut server, &mut b2);

		assert!(server.pk_by_kid(1).is_some());
		assert!(server.pk_by_kid(2).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, 1).unwrap();
		let b2_m1 = server.encrypt_message(&message, 2).unwrap();
		assert_ne!(b1_m1, b2_m1);
	}

	#[test]
	fn server_encrypt_multiple() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let _ = test_register_beacon(&mut server, &mut b1);

		assert!(server.pk_by_kid(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);
	}

	#[test]
	fn server_init_from_id_seed() {
		let empty = [0u8; ED25519_SEED_SIZE];
		let seeded = crypto_sign::KeyPair::from_seed(&empty).unwrap();
		let server = BeaconCryptPqxdh::new(false, 0, None, Some(&empty));
		assert_eq!(
			seeded.secret_key.as_bytes(),
			server.identity_sk().as_bytes()
		);
		assert_eq!(
			seeded.public_key.as_bytes(),
			server.identity_pk().as_bytes()
		);
	}

	#[test]
	fn beacon_sign_can_check() {
		let server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk();
		let beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let message = [0xFFu8; 32];
		let signed = server.sign_message(&message).unwrap();

		assert!(beacon.verify_signature(signed.as_slice()).is_some());
	}

	#[test]
	fn beacon_can_register() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk();
		let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let message = [0xFFu8; 32];
		let phase_1 = beacon.get_registration_bundle().unwrap();
		let reg_out = server.get_shared_secret(&phase_1).unwrap();
		let phase2 = server
			.build_registration_response(reg_out, Some(&message))
			.unwrap();
		let plaintext = beacon.finish_registration(&phase2.serialized).unwrap();
		assert!(plaintext.len() == message.len());
		assert_eq!(plaintext.as_array::<32>().unwrap().to_owned(), message);
	}

	#[test]
	fn beacon_can_sign() {
		let beacon = BeaconCryptPqxdh::new(true, 0, None, None);
		let message = [0xFFu8; 32];
		assert!(beacon.sign_message(&message).is_some());
	}

	#[test]
	fn beacon_can_catch_up() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(server.pk_by_kid(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);

		let dec_b1_m2 = b1.decrypt_message(&b1_m2, 0).unwrap();
		let dec_b1_m1 = b1.decrypt_message(&b1_m1, 0).unwrap();
		assert_eq!(dec_b1_m1, dec_b1_m2);
	}

	#[test]
	fn beacon_delete_onetime() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		// the beacon doesn't generate its one-time key until it generates its registration bundle
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		assert!(b1.get_onetime_pk() == None);
		assert!(b1.get_onetime_sk() == None);
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(b1.get_onetime_pk() == None);
		assert!(b1.get_onetime_sk() == None);
	}

	#[test]
	fn beacon_generates_onetime() {
		let server_id = [0u8; crypto_sign::PUBLICKEYBYTES];
		// the beacon doesn't generate its one-time key until it generates its registration bundle
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(&server_id), None);
		assert!(b1.get_onetime_pk() == None);
		assert!(b1.get_onetime_sk() == None);
		let _ = b1.get_registration_bundle();
		assert!(b1.get_onetime_pk().is_some());
		assert!(b1.get_onetime_sk().is_some());
	}

	#[test]
	fn provider_roles_create_only_their_required_key_material() {
		let server = BeaconCryptPqxdh::new(false, 7, None, None);
		assert!(!server.is_beacon());
		assert_eq!(server.server_kid(), 7);
		assert!(server.get_prekey_pk().is_none());
		assert!(server.get_onetime_pk().is_none());
		assert!(server.pq_pk().is_none());

		let server_id = server.identity_pk().clone();
		let beacon = BeaconCryptPqxdh::new(true, 7, Some(server_id.as_bytes()), None);
		assert!(beacon.is_beacon());
		assert!(beacon.get_prekey_pk().is_some());
		assert!(beacon.get_prekey_sk().is_some());
		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_pk().is_some());
		assert!(beacon.pq_sk().is_some());
		assert_eq!(beacon.server_id(), Some(&server_id));
	}

	#[test]
	fn adding_an_existing_key_id_does_not_replace_its_identity() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let first = crypto_sign::KeyPair::generate().unwrap().public_key;
		let replacement = crypto_sign::KeyPair::generate().unwrap().public_key;

		server.add_known_kid(9, first.clone());
		server.add_known_kid(9, replacement);

		assert_eq!(server.pk_by_kid(9), Some(&first));
	}

	#[test]
	fn registration_bundle_authenticates_each_declared_public_key() {
		let mut beacon = BeaconCryptPqxdh::new(true, 0, None, None);
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();

		let identity = registration.get_identity_key().unwrap();
		assert_eq!(identity[0], 1);
		assert_eq!(
			decode_sign(identity).unwrap(),
			beacon.identity_pk().as_bytes()
		);

		let prekey =
			crypto_sign::verify(registration.get_pre_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(prekey[0], 2);
		assert_eq!(
			decode_kem(&prekey).unwrap(),
			beacon.get_prekey_pk().unwrap().as_bytes()
		);

		let onetime = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		assert_eq!(onetime[0], 2);
		assert_eq!(
			decode_kem(&onetime).unwrap(),
			beacon.get_onetime_pk().unwrap().as_bytes(),
		);

		let pq =
			crypto_sign::verify(registration.get_pq_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(pq[0], 1);
		assert_eq!(decode_kem(&pq).unwrap(), beacon.pq_pk().unwrap().as_bytes());
	}

	#[test]
	fn server_rejects_a_registration_with_a_tampered_signed_key() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = BeaconCryptPqxdh::new(true, 0, None, None);
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();
		let mut tampered_prekey = registration.get_pre_key().unwrap().to_vec();
		let last = tampered_prekey.len() - 1;
		tampered_prekey[last] ^= 1;

		let mut tampered = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut root = tampered.init_root();
		root.set_identity_key(registration.get_identity_key().unwrap());
		root.set_pre_key(&tampered_prekey);
		root.set_one_time_key(registration.get_one_time_key().unwrap());
		root.set_pq_key(registration.get_pq_key().unwrap());
		let mut tampered_serialized = vec![];
		capnp::serialize::write_message(&mut tampered_serialized, tampered.borrow_inner()).unwrap();

		assert!(server.get_shared_secret(&tampered_serialized).is_none());
	}

	#[test]
	fn signature_verification_rejects_an_unknown_key_id() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().clone();
		let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		test_register_beacon(&mut server, &mut beacon);

		let signed = beacon.sign_message(b"authenticated message").unwrap();
		let valid = server.verify_signature(&signed).unwrap();
		assert_eq!(valid.key_id, 1);
		assert_eq!(valid.data, b"authenticated message");

		let message =
			capnp::serialize_packed::read_message(&signed[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, protogram_capnp::proto_gram::Owned>::new(message);
		let protogram = typed.get().unwrap();
		let mut altered = TypedBuilder::<protogram_capnp::proto_gram::Owned>::new_default();
		let mut root = altered.init_root();
		root.set_key_id(2);
		root.set_data(protogram.get_data().unwrap());
		let mut altered_serialized = vec![];
		capnp::serialize_packed::write_message(&mut altered_serialized, altered.borrow_inner())
			.unwrap();

		assert!(server.verify_signature(&altered_serialized).is_none());
	}

	#[test]
	fn root_key_derivation_matches_the_pqxdh_transcript() {
		let dh1 = DhSecret::from([0x11; DH_OUT_LEN]);
		let dh2 = DhSecret::from([0x22; DH_OUT_LEN]);
		let dh3 = DhSecret::from([0x33; DH_OUT_LEN]);
		let dh4 = DhSecret::from([0x44; DH_OUT_LEN]);
		let shared_bytes = [0x55; crypto_kem::mlkem768::SHAREDSECRETBYTES];
		let shared = crypto_kem::mlkem768::SharedSecret::from_bytes(&shared_bytes).unwrap();

		let actual =
			derive_root_key(dh1.clone(), dh2.clone(), dh3.clone(), dh4.clone(), shared).unwrap();
		let mut ikm = vec![0xFF; crypto_kx::PUBLICKEYBYTES];
		ikm.extend_from_slice(dh1.as_slice());
		ikm.extend_from_slice(dh2.as_slice());
		ikm.extend_from_slice(dh3.as_slice());
		ikm.extend_from_slice(dh4.as_slice());
		ikm.extend_from_slice(&shared_bytes);
		let prk = crypto_kdf::hkdf::sha512::extract(None, &ikm).unwrap();
		let expected =
			crypto_kdf::hkdf::sha512::expand(actual.len(), Some(PQXDH_INFO), &prk).unwrap();

		assert_eq!(actual, expected);
	}

	#[test]
	fn associated_data_has_a_stable_order_and_layout() {
		let server = crypto_sign::KeyPair::from_seed(&[0x61; ED25519_SEED_SIZE]).unwrap();
		let beacon = crypto_sign::KeyPair::from_seed(&[0x62; ED25519_SEED_SIZE]).unwrap();
		let actual = build_associated_data(server.public_key.clone(), beacon.public_key.clone());
		let mut expected = Vec::with_capacity(AD_SIZE);
		expected.push(1);
		expected.extend_from_slice(server.public_key.as_bytes());
		expected.push(1);
		expected.extend_from_slice(beacon.public_key.as_bytes());
		expected.extend_from_slice(PQXDH_INFO);
		expected.extend_from_slice(SYM_RATCHET_INFO);
		assert_eq!(actual.as_slice(), expected);
		assert_ne!(
			actual,
			build_associated_data(beacon.public_key, server.public_key),
		);
	}
}
