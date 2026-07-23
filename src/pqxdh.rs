// SPDX-License-Identifier: 0BSD

#[cfg(feature = "server")]
use crate::server::EncryptState;
use crate::shared::{
	DhSecret, ED25519_SEED_SIZE, KEX_KDF_OUT_LEN, KemType, KexDerivedSecret, RatchetManager,
	RemotePrincipal, SYM_RATCHET_INFO, SignType, SignaturePk, encode_sign,
};
use crate::{CryptoProvider, phase1_capnp, phase2_capnp};
#[cfg(feature = "beacon")]
use crate::{beacon::ProviderBeacon, shared::encode_kem};
#[cfg(feature = "server")]
use crate::{
	server::{ProviderServer, RegResponse, RegistrationOutput},
	shared::{REGISTRATION_WITNESS, decode_kem, decode_sign},
};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{
	crypto_kdf, crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init,
};
use std::collections::HashMap;
use std::mem::swap;
use std::vec;
use zeroize::Zeroize;

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

	fn set_identity_kid(&mut self, key_id: u64) {
		self.identity_key_kid = key_id;
	}

	fn identity_key_kid(&self) -> u64 {
		self.identity_key_kid
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

	pub fn delete_pq_keypair(&mut self) {
		if let Some(pq_key) = &mut self.pq_key {
			let mut keypair = crypto_kem::mlkem768::KeyPair::from_seed(&[0u8; 64]).unwrap();
			swap(pq_key, &mut keypair);
			self.pq_key = None;
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
		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, shared_secret)?;
		self.delete_onetime_keypair();
		self.delete_pq_keypair();

		self.set_identity_kid(response.get_key_id());
		let id = self.identity_pk().clone();
		self.set_associated_data(build_associated_data(server_id, id));
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let srv_key_id = self.server_kid();
		self.init_ratchets(derived_secret.as_slice(), &info_str, true, srv_key_id);

		match response.get_app_cipher_text() {
			// https://signal.org/docs/specifications/pqxdh/#receiving-the-initial-message
			Ok(ciphertext) => self.decrypt_message(ciphertext).map_or_else(
				|| {
					// deletes the derived keychains but not the entire `RemotePrincipal` as the server is currently special-cased.
					// I think this matches the protocol's requirements: "If the initial ciphertext fails to decrypt, then Bob aborts the protocol and deletes SK".
					self.reset_known_kid(self.server_kid());
					self.set_identity_kid(self.server_kid());
					self.associated_data = None;
					None
				},
				// PQXDH protcol run is now complete and the beacon is successfully registered
				|decrypted| Some(decrypted.plaintext),
			),
			Err(_) => {
				self.reset_known_kid(self.server_kid());
				self.set_identity_kid(self.server_kid());
				self.associated_data = None;
				None
			}
		}
	}
}

#[cfg(feature = "server")]
impl ProviderServer for BeaconCryptPqxdh {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().ok()?;

		let decoded_beacon_id =
			decode_sign(registration.get_identity_key().ok()?, SignType::Ed25519).ok()?;
		let remote_id = crypto_sign::PublicKey::from_bytes(&decoded_beacon_id).ok()?;
		let pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id)?;
		let prekey_verified = crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id)?;
		let onetime_verified =
			crypto_sign::verify(registration.get_one_time_key().ok()?, &remote_id)?;

		let beacon_prekey =
			crypto_kx::PublicKey::from_bytes(&decode_kem(&prekey_verified, KemType::X25519).ok()?)
				.ok()?;
		let beacon_onetime =
			crypto_kx::PublicKey::from_bytes(&decode_kem(&onetime_verified, KemType::X25519).ok()?)
				.ok()?;
		let ephemeral = crypto_kx::KeyPair::generate().ok()?;
		let pq_pub = crypto_kem::mlkem768::PublicKey::from_bytes(
			&decode_kem(&pq_verified, KemType::MlKem768).ok()?,
		)
		.ok()?;
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

		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, kem_shared)?;

		Some(RegistrationOutput {
			kem_ciphertext,
			derived_secret,
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
		bundle.set_key_id(remote_kid);
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

	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<EncryptState> {
		let ciphertext = self.encrypt_message(bytes, kid)?;
		let ratchet = self.ratchet_manager_mut(kid)?;
		let state = ratchet.send_state();
		Some(EncryptState {
			kid,
			key: state.clone(),
			data: ciphertext,
		})
	}

	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<EncryptState> {
		let decrypted = self.decrypt_message(bytes)?;
		let ratchet = self.ratchet_manager_mut(decrypted.key_id)?;
		let state = ratchet.recv_state();
		Some(EncryptState {
			kid: decrypted.key_id,
			key: state.clone(),
			data: decrypted.plaintext,
		})
	}
}

pub fn derive_root_key(
	dh1: DhSecret,
	dh2: DhSecret,
	dh3: DhSecret,
	dh4: DhSecret,
	shared_secret: crypto_kem::mlkem768::SharedSecret,
) -> Option<KexDerivedSecret> {
	// make sure to start inserting after sizeof(Ed25519) so the first bytes are filled with 0xFF as per the spec:
	// https://signal.org/docs/specifications/pqxdh/#cryptographic-notation
	let mut ikm = vec![0xFFu8; crypto_kx::PUBLICKEYBYTES];
	ikm.extend_from_slice(dh1.as_slice());
	ikm.extend_from_slice(dh2.as_slice());
	ikm.extend_from_slice(dh3.as_slice());
	ikm.extend_from_slice(dh4.as_slice());
	ikm.extend_from_slice(shared_secret.as_bytes());

	let prk = crypto_kdf::hkdf::sha512::extract(None, &ikm).ok()?;
	ikm.zeroize();
	let derived: KexDerivedSecret =
		crypto_kdf::hkdf::sha512::expand(KEX_KDF_OUT_LEN, Some(PQXDH_INFO), &prk)
			.ok()?
			.into();
	Some(derived)
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

#[cfg(all(test, feature = "beacon", feature = "server"))]
mod tests {
	use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
	use libsodium_rs::{crypto_kdf, crypto_kem, crypto_kx, crypto_sign};

	use super::{AD_SIZE, PQXDH_INFO, build_associated_data, derive_root_key};
	use crate::{
		BeaconCryptPqxdh, KDF_STATE_SIZE, SignType,
		beacon::ProviderBeacon,
		phase1_capnp,
		server::ProviderServer,
		shared::{
			CryptoProvider, DH_OUT_LEN, DhSecret, ED25519_SEED_SIZE, KemType, KexDerivedSecret,
			SYM_RATCHET_INFO, decode_kem, decode_sign,
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

		let dec_b1_m2 = b1.decrypt_message(&b1_m2).unwrap();
		let dec_b1_m1 = b1.decrypt_message(&b1_m1).unwrap();
		assert_eq!(dec_b1_m1.plaintext, dec_b1_m2.plaintext);
		assert_eq!(dec_b1_m1.key_id, dec_b1_m2.key_id);
	}

	#[test]
	fn beacon_deletes_one_time_and_pq_keys_after_registration() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		// The beacon doesn't generate its one-time key until it generates its registration bundle.
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		assert!(b1.get_onetime_pk().is_none());
		assert!(b1.get_onetime_sk().is_none());
		assert!(b1.pq_pk().is_some());
		assert!(b1.pq_sk().is_some());
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(b1.get_onetime_pk().is_none());
		assert!(b1.get_onetime_sk().is_none());
		assert!(b1.pq_pk().is_none());
		assert!(b1.pq_sk().is_none());
	}

	#[test]
	fn beacon_generates_onetime() {
		let server_id = [0u8; crypto_sign::PUBLICKEYBYTES];
		// the beacon doesn't generate its one-time key until it generates its registration bundle
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(&server_id), None);
		assert!(b1.get_onetime_pk().is_none());
		assert!(b1.get_onetime_sk().is_none());
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
			decode_sign(identity, SignType::Ed25519).unwrap(),
			beacon.identity_pk().as_bytes()
		);

		let prekey =
			crypto_sign::verify(registration.get_pre_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(prekey[0], 2);
		assert_eq!(
			decode_kem(&prekey, KemType::X25519).unwrap(),
			beacon.get_prekey_pk().unwrap().as_bytes()
		);

		let onetime = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		assert_eq!(onetime[0], 2);
		assert_eq!(
			decode_kem(&onetime, KemType::X25519).unwrap(),
			beacon.get_onetime_pk().unwrap().as_bytes(),
		);

		let pq =
			crypto_sign::verify(registration.get_pq_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(pq[0], 1);
		assert_eq!(
			decode_kem(&pq, KemType::MlKem768).unwrap(),
			beacon.pq_pk().unwrap().as_bytes()
		);
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
	fn server_rejects_tampering_of_each_signed_registration_key() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = BeaconCryptPqxdh::new(true, 0, None, None);
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();
		let identity = registration.get_identity_key().unwrap().to_vec();
		let prekey = registration.get_pre_key().unwrap().to_vec();
		let onetime = registration.get_one_time_key().unwrap().to_vec();
		let pq = registration.get_pq_key().unwrap().to_vec();

		for field in ["preKey", "oneTimeKey", "pqKey"] {
			let mut tampered_prekey = prekey.clone();
			let mut tampered_onetime = onetime.clone();
			let mut tampered_pq = pq.clone();
			let selected = match field {
				"preKey" => &mut tampered_prekey,
				"oneTimeKey" => &mut tampered_onetime,
				"pqKey" => &mut tampered_pq,
				_ => unreachable!(),
			};
			let last = selected.len() - 1;
			selected[last] ^= 1;

			let mut message = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
			let mut root = message.init_root();
			root.set_identity_key(&identity);
			root.set_pre_key(&tampered_prekey);
			root.set_one_time_key(&tampered_onetime);
			root.set_pq_key(&tampered_pq);
			let mut tampered = vec![];
			capnp::serialize::write_message(&mut tampered, message.borrow_inner()).unwrap();

			assert!(
				server.get_shared_secret(&tampered).is_none(),
				"server accepted tampered {field}"
			);
		}
	}

	#[test]
	fn server_rejects_signed_registration_keys_with_wrong_type_prefixes() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = BeaconCryptPqxdh::new(true, 0, None, None);
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();

		let identity = registration.get_identity_key().unwrap().to_vec();
		let prekey =
			crypto_sign::verify(registration.get_pre_key().unwrap(), beacon.identity_pk()).unwrap();
		let onetime = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		let pq =
			crypto_sign::verify(registration.get_pq_key().unwrap(), beacon.identity_pk()).unwrap();

		for field in ["preKey", "oneTimeKey", "pqKey"] {
			let mut wrong_prekey = prekey.clone();
			let mut wrong_onetime = onetime.clone();
			let mut wrong_pq = pq.clone();
			match field {
				"preKey" => wrong_prekey[0] = u8::from(KemType::MlKem768),
				"oneTimeKey" => wrong_onetime[0] = u8::from(KemType::MlKem768),
				"pqKey" => wrong_pq[0] = u8::from(KemType::X25519),
				_ => unreachable!(),
			}

			let wrong_prekey = crypto_sign::sign(&wrong_prekey, beacon.identity_sk()).unwrap();
			let wrong_onetime = crypto_sign::sign(&wrong_onetime, beacon.identity_sk()).unwrap();
			let wrong_pq = crypto_sign::sign(&wrong_pq, beacon.identity_sk()).unwrap();
			let mut message = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
			let mut root = message.init_root();
			root.set_identity_key(&identity);
			root.set_pre_key(&wrong_prekey);
			root.set_one_time_key(&wrong_onetime);
			root.set_pq_key(&wrong_pq);
			let mut wrong_type = vec![];
			capnp::serialize::write_message(&mut wrong_type, message.borrow_inner()).unwrap();

			assert!(
				server.get_shared_secret(&wrong_type).is_none(),
				"server accepted a wrong type prefix in {field}"
			);
		}
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
		let expected: KexDerivedSecret =
			crypto_kdf::hkdf::sha512::expand(KDF_STATE_SIZE, Some(PQXDH_INFO), &prk)
				.unwrap()
				.into();
		let known_answer = [
			0xcb, 0xcf, 0x9d, 0x12, 0xdb, 0x13, 0x92, 0x7a, 0xc3, 0x3a, 0x04, 0x9c, 0xb6, 0x10,
			0x94, 0x8b, 0xaf, 0x33, 0x9b, 0x5c, 0x8c, 0x78, 0x2a, 0x2e, 0xaf, 0x14, 0x3e, 0x12,
			0x3b, 0xda, 0xa7, 0xe2,
		];

		assert_eq!(actual.as_slice(), expected.as_slice());
		assert_eq!(actual.as_slice(), known_answer.as_slice());
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
