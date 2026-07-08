// SPDX-License-Identifier: 0BSD

use crate::beacon::ProviderBeacon;
use crate::server::{ProviderServer, RegResponse};
use crate::shared::{
	AD_SIZE, CurveType, DhSecret, KemType, RatchetManager, RegistrationOutput, RemotePrincipal,
	SYM_RATCHET_INFO, SignaturePk, build_additional_data, create_protogram_reader, decode_ec,
	decode_kem, derive_root_key, encode_ec, encode_kem,
};
use crate::{CryptoProvider, phase1_capnp, phase2_capnp, protogram_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init};
use std::collections::HashMap;
use std::vec;
impl SignaturePk for crypto_sign::PublicKey {}

pub struct BeaconCryptPqxdh {
	identity_key_pk: crypto_sign::PublicKey,
	identity_key_sk: crypto_sign::SecretKey,
	identity_key_kid: u64,

	prekey_pk: crypto_kx::PublicKey,
	prekey_sk: crypto_kx::SecretKey,

	onetime_key_pk: crypto_kx::PublicKey,
	onetime_key_sk: crypto_kx::SecretKey,

	pq_key_pk: crypto_kem::mlkem768::PublicKey,
	pq_key_sk: crypto_kem::mlkem768::SecretKey,

	associated_data: [u8; AD_SIZE],
	// unfortunately we can't use static generics so we have to store the role at runtime
	is_beacon: bool,
	// stores the server's `seq` for the beacon. Stores the counter of remote `seq`s for the server
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
			identity_key_pk: crypto_sign::PublicKey::from_bytes(
				&[0u8; crypto_sign::PUBLICKEYBYTES],
			)
			.unwrap(),
			identity_key_sk: crypto_sign::SecretKey::from_bytes(
				&[0u8; crypto_sign::SECRETKEYBYTES],
			)
			.unwrap(),
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

			associated_data: [0u8; AD_SIZE],
			is_beacon: true,
			server_kid: 0,
			known_ids: HashMap::new(),
		}
	}
	fn new(is_beacon: bool, server_kid: u64, server_pk: Option<&[u8]>) -> Self {
		ensure_init().expect("Failed to initialize libsodium");

		let id_keypair = crypto_sign::KeyPair::generate().unwrap();
		let prekey = crypto_kx::KeyPair::generate().unwrap();
		let onetime = crypto_kx::KeyPair::generate().unwrap();
		let pqkey = crypto_kem::mlkem768::KeyPair::generate().unwrap();
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
			// this will be overwritten when the agent registers
			identity_key_kid: server_kid,
			prekey_pk: prekey.public_key,
			prekey_sk: prekey.secret_key,
			onetime_key_pk: onetime.public_key,
			onetime_key_sk: onetime.secret_key,
			pq_key_pk: pqkey.public_key,
			pq_key_sk: pqkey.secret_key,
			associated_data: [0u8; AD_SIZE],
			is_beacon,
			server_kid,
			known_ids: known,
		}
	}

	/// ## Arguments
	/// * `data`   - buffer to be signed, probably should be a serialized `cryptoframe_capnp::crypto_frame`
	fn sign_message(&self, data: &[u8]) -> Option<Vec<u8>> {
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

	fn set_identity_kid(&mut self, key_id: u64) {
		self.identity_key_kid = key_id;
	}

	/// ## Arguments
	/// * `data`   - wire buffer to check the signature for, MUST be a serialized `protogram_capnp::proto_gram`
	///
	/// ## Returns
	/// * `None` if signature verification fails or some other error happens.
	/// * `Vec<u8>` containing the authenticated buffer with the signature stripped
	fn verify_signature(&self, data: &[u8]) -> Option<Vec<u8>> {
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

	fn add_known_kid(&mut self, key_id: u64, pk: crypto_sign::PublicKey) {
		self.known_ids
			.entry(key_id)
			.or_insert(RemotePrincipal::new(pk, RatchetManager::new()));
	}

	fn new_remote_kid(&mut self) -> u64 {
		self.server_kid += 1;
		self.server_kid
	}

	fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		self.associated_data = data
	}

	fn get_associated_data(&self) -> [u8; AD_SIZE] {
		self.associated_data.clone()
	}

	fn get_server_id(&self) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&self.server_kid) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	fn get_server_kid(&self) -> u64 {
		self.server_kid
	}

	fn get_id_by_seq(&self, seq: u64) -> Option<&crypto_sign::PublicKey> {
		if let Some(remote) = self.known_ids.get(&seq) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	fn get_identity_pk(&self) -> &crypto_sign::PublicKey {
		&self.identity_key_pk
	}

	fn get_identity_sk(&self) -> &crypto_sign::SecretKey {
		&self.identity_key_sk
	}

	fn get_pq_pk(&self) -> &crypto_kem::mlkem768::PublicKey {
		&self.pq_key_pk
	}

	fn get_pq_sk(&self) -> &crypto_kem::mlkem768::SecretKey {
		&self.pq_key_sk
	}

	fn get_ratchet_manager(&self, kid: u64) -> Option<&RatchetManager> {
		if let Some(remote) = self.known_ids.get(&kid) {
			Some(remote.get_ratchet())
		} else {
			None
		}
	}

	fn get_ratchet_manager_mut(&mut self, kid: u64) -> Option<&mut RatchetManager> {
		if let Some(remote) = self.known_ids.get_mut(&kid) {
			Some(remote.get_ratchet_mut())
		} else {
			None
		}
	}
}

impl BeaconCryptPqxdh {
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

	pub fn delete_onetime_keypair(&mut self) {
		self.onetime_key_pk = crypto_kx::PublicKey::from([0u8; 32]);
		self.onetime_key_sk = crypto_kx::SecretKey::from([0u8; 32]);
	}
}

#[cfg(feature = "beacon")]
impl ProviderBeacon for BeaconCryptPqxdh {
	fn get_registration_bundle(&self) -> Option<Vec<u8>> {
		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();

		let encoded_id = encode_ec(CurveType::Ed25519, self.get_identity_pk().as_bytes()).ok()?;
		bundle.set_identity_key(&encoded_id);

		let encoded_prekey = encode_ec(CurveType::X25519, self.get_prekey_pk().as_bytes()).ok()?;
		let prekey_sig = crypto_sign::sign(&encoded_prekey, self.get_identity_sk()).ok()?;
		bundle.set_pre_key(&prekey_sig);

		let encoded_onetime =
			encode_ec(CurveType::X25519, self.get_onetime_pk().as_bytes()).ok()?;
		let onetime_sig = crypto_sign::sign(&encoded_onetime, self.get_identity_sk()).ok()?;
		bundle.set_one_time_key(&onetime_sig);

		let encoded_pq = encode_kem(KemType::MlKem768, self.get_pq_pk().as_bytes()).ok()?;
		let pq_sig = crypto_sign::sign(&encoded_pq, self.get_identity_sk()).ok()?;
		bundle.set_pq_key(&pq_sig);

		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).unwrap();
		Some(buffer)
	}

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
		let server_kex_id = crypto_sign::ed25519_pk_to_curve25519(&server_id).ok()?;
		let beacon_kex_id = crypto_sign::ed25519_sk_to_curve25519(self.get_identity_sk()).ok()?;
		let shared_secret =
			crypto_kem::mlkem768::decapsulate(&kem_ciphertext, self.get_pq_sk()).ok()?;
		let dh1: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk().as_bytes(), &server_kex_id)
				.ok()?
				.into();
		let dh2: DhSecret = crypto_scalarmult::scalarmult(&beacon_kex_id, ephemeral.as_bytes())
			.ok()?
			.into();
		let dh3: DhSecret =
			crypto_scalarmult::scalarmult(self.get_prekey_sk().as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let dh4: DhSecret =
			crypto_scalarmult::scalarmult(self.get_onetime_sk().as_bytes(), ephemeral.as_bytes())
				.ok()?
				.into();
		let derived_secret = derive_root_key(dh1, dh2, dh3, dh4, shared_secret).ok()?;
		self.delete_onetime_keypair();

		self.add_server_pk(server_id.clone());
		self.set_identity_kid(response.get_key_id());
		let id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(server_id.clone(), id));
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let srv_key_id = self.get_server_kid();
		self.init_ratchets(&derived_secret, &info_str, true, srv_key_id);

		match response.get_app_cipher_text() {
			Ok(ciphertext) => match self.decrypt_message(ciphertext, srv_key_id, true) {
				Some(plaintext) => Some(plaintext),
				None => None,
			},
			Err(_) => Some(vec![0u8; 0]),
		}
	}
}

#[cfg(feature = "server")]
impl ProviderServer for BeaconCryptPqxdh {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).unwrap();
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().unwrap();

		let decoded_beacon_id = decode_ec(registration.get_identity_key().ok()?).ok()?;
		let remote_id = crypto_sign::PublicKey::from_bytes(&decoded_beacon_id).ok()?;
		let pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id).unwrap();
		let prekey_verified =
			crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id).unwrap();
		let onetime_verified =
			crypto_sign::verify(registration.get_one_time_key().ok()?, &remote_id).unwrap();

		let beacon_prekey =
			crypto_kx::PublicKey::from_bytes(&decode_ec(&prekey_verified).ok()?).ok()?;
		let beacon_onetime =
			crypto_kx::PublicKey::from_bytes(&decode_ec(&onetime_verified).ok()?).ok()?;
		let ephemeral = crypto_kx::KeyPair::generate().ok()?;
		let pq_pub =
			crypto_kem::mlkem768::PublicKey::from_bytes(&decode_kem(&pq_verified).ok()?).ok()?;
		let (kem_ciphertext, kem_shared) = crypto_kem::mlkem768::encapsulate(&pq_pub).ok()?;

		let remote_id_kex = crypto_sign::ed25519_pk_to_curve25519(&remote_id).ok()?;
		let id_kex_sk = crypto_sign::ed25519_sk_to_curve25519(self.get_identity_sk()).ok()?;
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
		let server_id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(server_id, remote_id.clone()));

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
		bundle.set_key_id(self.get_server_kid());
		bundle.set_ephemeral_key(reg_out.ephemeral.as_bytes());
		bundle.set_identity_key(self.get_identity_pk().as_bytes());
		bundle.set_kem_cipher_text(reg_out.kem_ciphertext.as_bytes());

		let mut buffer = vec![];
		if let Some(plaintext) = data {
			let ciphertext = self.encrypt_message(plaintext, true, remote_kid)?;
			let _ = bundle.set_app_cipher_text(&ciphertext);
			capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		} else {
			capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		};

		Some(RegResponse {
			serialized: buffer,
			kid: remote_kid,
		})
	}
}

#[cfg(test)]
mod tests {
	use libsodium_rs::crypto_kx;

	use crate::{
		BeaconCryptPqxdh, beacon::ProviderBeacon, server::ProviderServer, shared::CryptoProvider,
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
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let b1_reg = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let b2_reg = test_register_beacon(&mut server, &mut b2);

		assert_eq!(b1_reg, b2_reg);
	}

	#[test]
	fn server_encrypt_to_multiple() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b2);

		assert!(server.get_id_by_seq(1).is_some());
		assert!(server.get_id_by_seq(2).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b2_m1 = server.encrypt_message(&message, true, 2).unwrap();
		assert_ne!(b1_m1, b2_m1);
	}

	#[test]
	fn server_encrypt_multiple() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);

		assert!(server.get_id_by_seq(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, true, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);
	}

	#[test]
	fn beacon_sign_can_check() {
		let server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk();
		let beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let message = [0xFFu8; 32];
		let signed = server.sign_message(&message).unwrap();

		assert!(beacon.verify_signature(signed.as_slice()).is_some());
	}

	#[test]
	fn beacon_can_register() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk();
		let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
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
		let beacon = BeaconCryptPqxdh::new(true, 0, None);
		let message = [0xFFu8; 32];
		assert!(beacon.sign_message(&message).is_some());
	}

	#[test]
	fn beacon_can_catch_up() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(server.get_id_by_seq(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, true, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);

		let dec_b1_m1 = b1.decrypt_message(&b1_m1, 0, true).unwrap();
		let dec_b1_m2 = b1.decrypt_message(&b1_m2, 0, true).unwrap();
		assert_eq!(dec_b1_m1, dec_b1_m2);
	}

	#[test]
	fn beacon_delete_onetime() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None);
		let server_id = server.get_identity_pk().to_owned();

		let empty = [0u8; crypto_kx::PUBLICKEYBYTES];
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()));
		assert!(b1.get_onetime_pk().as_bytes() != empty);
		assert!(b1.get_onetime_sk().as_bytes() != empty);
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(b1.get_onetime_pk().as_bytes() == empty);
		assert!(b1.get_onetime_sk().as_bytes() == empty);
	}
}
