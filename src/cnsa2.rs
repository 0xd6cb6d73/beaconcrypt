// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
use crate::beacon::ProviderBeacon;
#[cfg(feature = "server")]
use crate::server::RegistrationOutput;
#[cfg(feature = "server")]
use crate::server::{ProviderServer, RegResponse};
use crate::shared::{
	KEX_KDF_OUT_LEN, MlKemSharedSecret, RatchetManager, RemotePrincipal, SYM_RATCHET_INFO,
	SignaturePk, create_protogram_reader,
};
#[cfg(feature = "beacon")]
use crate::shared::{KemType, SignType, decode_kem, decode_sign, encode_kem, encode_sign};
use crate::{CryptoProvider, protogram_capnp};
#[cfg(feature = "beacon")]
use crate::{phase1_capnp, phase2_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
#[cfg(feature = "beacon")]
use libcrux_ml_dsa::SIGNING_RANDOMNESS_SIZE;
use libcrux_ml_dsa::ml_dsa_87;
use libcrux_ml_kem::{SHARED_SECRET_SIZE, mlkem1024};
use libsodium_rs::{crypto_kdf, crypto_kx, ensure_init, random};
use std::collections::HashMap;
#[cfg(feature = "server")]
use std::marker::PhantomData;
use std::vec;

pub const CNSA2_INFO: &[u8; 35] = b"Cnsa2_ML_DSA_87_SHA-512_ML-KEM-1024";
pub const AD_SIZE: usize =
	CNSA2_INFO.len() + SYM_RATCHET_INFO.len() + ((ML_DSA_87_PUBKEY_SIZE + 1) * 2);
pub const ML_DSA_RAND_SIZE: usize = libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE;
pub const ML_DSA_PK_SIZE: usize = ml_dsa_87::MLDSA87VerificationKey::len();
pub const ML_DSA_SIGN_RANDOM_SIZE: usize = 32;
pub const ML_KEM_1024_SEED_SIZE: usize = libcrux_ml_kem::KEY_GENERATION_SEED_SIZE;
pub const ML_DSA_87_SIG_SIZE: usize = ml_dsa_87::MLDSA87Signature::len();
pub const ML_DSA_87_PUBKEY_SIZE: usize = ml_dsa_87::MLDSA87VerificationKey::len();
pub const ML_KEM_1024_CT_SIZE: usize = mlkem1024::MlKem1024Ciphertext::len();
pub const ML_DSA_87_ENC_PUBKEY_SIZE: usize = ML_DSA_87_PUBKEY_SIZE + 1;
pub const ML_KEM_1024_PUBKEY_SIZE: usize = mlkem1024::MlKem1024PublicKey::len();
pub const ML_KEM_1024_ENCAP_RAN_SIZE: usize = SHARED_SECRET_SIZE;
impl SignaturePk for ml_dsa_87::MLDSA87VerificationKey {}

pub struct BeaconCryptCnsa2 {
	identity_key_pk: ml_dsa_87::MLDSA87VerificationKey,
	identity_key_sk: ml_dsa_87::MLDSA87SigningKey,
	identity_key_kid: u64,

	pq_key_pk: mlkem1024::MlKem1024PublicKey,
	pq_key_sk: mlkem1024::MlKem1024PrivateKey,

	associated_data: [u8; AD_SIZE],
	// unfortunately we can't use static generics so we have to store the role at runtime
	is_beacon: bool,
	// stores the server's `key_id` for the beacon. Stores the counter of remote `key_id`s for the server
	server_kid: u64,
	known_ids: HashMap<u64, RemotePrincipal<ml_dsa_87::MLDSA87VerificationKey>>,
}

impl CryptoProvider for BeaconCryptCnsa2 {
	type SignaturePublicKey = ml_dsa_87::MLDSA87VerificationKey;
	type SignatureSecretKey = ml_dsa_87::MLDSA87SigningKey;
	type KemPublicKey = mlkem1024::MlKem1024PublicKey;
	type KemSecretKey = mlkem1024::MlKem1024PrivateKey;

	fn default() -> Self {
		Self {
			// our cryptographic identity, this is unique to the specific agent instance and uniquely identifies it to the server
			identity_key_pk: ml_dsa_87::MLDSA87VerificationKey::new(
				[0u8; ml_dsa_87::MLDSA87VerificationKey::len()],
			),
			identity_key_sk: ml_dsa_87::MLDSA87SigningKey::new(
				[0u8; ml_dsa_87::MLDSA87SigningKey::len()],
			),
			identity_key_kid: 0,

			pq_key_pk: mlkem1024::MlKem1024PublicKey::default(),
			pq_key_sk: mlkem1024::MlKem1024PrivateKey::default(),

			associated_data: [0u8; AD_SIZE],
			is_beacon: true,
			server_kid: 0,
			known_ids: HashMap::new(),
		}
	}
	fn new(
		is_beacon: bool,
		server_kid: u64,
		server_id_pk: Option<&[u8]>,
		_id_seed: Option<&[u8]>,
		_prekey_seed: Option<&[u8]>,
	) -> Self {
		ensure_init().expect("Failed to initialize libsodium");

		let sig_random =
			libsodium_rs::random::bytes(libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE);
		let sig_rand = *sig_random.as_array::<ML_DSA_RAND_SIZE>().unwrap();
		let signing = ml_dsa_87::generate_key_pair(sig_rand);

		let kem_random = libsodium_rs::random::bytes(ML_KEM_1024_SEED_SIZE);
		let kem_rand = *kem_random.as_array::<ML_KEM_1024_SEED_SIZE>().unwrap();
		let kem = mlkem1024::generate_key_pair(kem_rand);
		let known = if let Some(pk) = server_id_pk {
			if !is_beacon {
				HashMap::new()
			} else {
				let mut hm = HashMap::new();
				let pk_arr = pk.as_array::<ML_DSA_PK_SIZE>().unwrap().to_owned();
				hm.insert(
					server_kid,
					RemotePrincipal::new(
						ml_dsa_87::MLDSA87VerificationKey::new(pk_arr),
						RatchetManager::new(),
					),
				);
				hm
			}
		} else {
			HashMap::new()
		};

		Self {
			identity_key_pk: signing.verification_key,
			identity_key_sk: signing.signing_key,
			// this will be overwritten when the agent registers
			identity_key_kid: server_kid,
			pq_key_pk: kem.public_key().to_owned(),
			pq_key_sk: kem.private_key().to_owned(),
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
		builder.set_key_id(self.identity_key_kid);
		let ctx = [0u8; 0];
		let random = libsodium_rs::random::bytes(ML_DSA_SIGN_RANDOM_SIZE);
		let random_arr = random.as_array::<ML_DSA_SIGN_RANDOM_SIZE>().unwrap();
		let signature = ml_dsa_87::sign(self.get_identity_sk(), &data, &ctx, *random_arr).ok()?;
		let mut signed = vec![0u8; ML_DSA_87_SIG_SIZE];
		signed.copy_from_slice(signature.as_slice());
		signed.extend_from_slice(data);
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
		let parsed = reader.get_data().ok()?;
		if parsed.len() < ML_DSA_87_SIG_SIZE {
			return None;
		}

		let mut sig = [0u8; ML_DSA_87_SIG_SIZE];
		sig.copy_from_slice(&parsed[0..ML_DSA_87_SIG_SIZE]);
		let signature = ml_dsa_87::MLDSA87Signature::new(sig);
		let mut message = vec![0u8; parsed.len() - ML_DSA_87_SIG_SIZE];
		message.copy_from_slice(&parsed[ML_DSA_87_SIG_SIZE..]);

		let ctx = [0u8; 0];
		// hardcode this to avoid potential confusion
		let pubkey = if self.is_beacon {
			self.get_server_id()?
		} else {
			self.get_id_by_seq(reader.get_key_id())?
		};
		ml_dsa_87::verify(pubkey, &message, &ctx, &signature).ok()?;
		Some(message)
	}

	fn add_known_kid(&mut self, key_id: u64, pk: Self::SignaturePublicKey) {
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

	fn get_server_id(&self) -> Option<&Self::SignaturePublicKey> {
		if let Some(remote) = self.known_ids.get(&self.server_kid) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	fn get_server_kid(&self) -> u64 {
		self.server_kid
	}

	fn get_id_by_seq(&self, seq: u64) -> Option<&Self::SignaturePublicKey> {
		if let Some(remote) = self.known_ids.get(&seq) {
			Some(remote.get_pk())
		} else {
			None
		}
	}

	fn get_identity_pk(&self) -> &Self::SignaturePublicKey {
		&self.identity_key_pk
	}

	fn get_identity_sk(&self) -> &Self::SignatureSecretKey {
		&self.identity_key_sk
	}

	fn get_pq_pk(&self) -> &mlkem1024::MlKem1024PublicKey {
		&self.pq_key_pk
	}

	fn get_pq_sk(&self) -> &mlkem1024::MlKem1024PrivateKey {
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

#[cfg(feature = "beacon")]
impl ProviderBeacon for BeaconCryptCnsa2 {
	fn get_registration_bundle(&self) -> Option<Vec<u8>> {
		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();

		let encoded_id = encode_sign(SignType::MlDsa87, self.get_identity_pk().as_slice()).ok()?;
		bundle.set_identity_key(&encoded_id);
		let mut encoded_kem = encode_kem(KemType::MlKem1024, self.get_pq_pk().as_slice()).ok()?;

		let ctx = [0u8; 0];
		let mut randomness = [0u8; SIGNING_RANDOMNESS_SIZE];
		random::fill_bytes(&mut randomness);
		let mut kem_signature =
			ml_dsa_87::sign(self.get_identity_sk(), &encoded_kem, &ctx, randomness)
				.ok()?
				.as_mut_slice()
				.to_vec();
		kem_signature.append(&mut encoded_kem);
		bundle.set_pq_key(&kem_signature);
		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).unwrap();
		Some(buffer)
	}

	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let response = typed_reader.get().ok()?;

		let mldsa_buf = *decode_sign(
			response
				.get_identity_key()
				.ok()?
				.as_array::<ML_DSA_87_ENC_PUBKEY_SIZE>()
				.unwrap(),
		)
		.ok()?
		.as_array::<ML_DSA_87_PUBKEY_SIZE>()?;
		let mldsa = ml_dsa_87::MLDSA87VerificationKey::new(mldsa_buf);

		let kem_ct_buf = response
			.get_kem_cipher_text()
			.ok()?
			.as_array::<ML_KEM_1024_CT_SIZE>()?;
		let kem_ct = mlkem1024::MlKem1024Ciphertext::from(kem_ct_buf);
		let shared_secret: MlKemSharedSecret =
			mlkem1024::decapsulate(self.get_pq_sk(), &kem_ct).into();
		let derived_secret = derive_root_key(shared_secret)?;

		self.add_server_pk(mldsa.clone());
		self.set_identity_kid(response.get_key_id());
		let id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(mldsa, id));
		let mut info_str = vec![0u8; SYM_RATCHET_INFO.len()];
		info_str.copy_from_slice(SYM_RATCHET_INFO);
		let srv_key_id = self.get_server_kid();
		self.init_ratchets(&derived_secret, &info_str, true, srv_key_id);

		match response.get_app_cipher_text() {
			Ok(ciphertext) if ciphertext.is_empty() => Some(vec![]),
			Ok(ciphertext) => match self.decrypt_message(ciphertext, srv_key_id, true) {
				Some(plaintext) => Some(plaintext),
				None => None,
			},
			Err(_) => Some(vec![0u8; 0]),
		}
	}
}

#[cfg(feature = "server")]
impl ProviderServer for BeaconCryptCnsa2 {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).unwrap();
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().unwrap();

		let decoded_id = decode_sign(registration.get_identity_key().ok()?).ok()?;
		let decoded_beacon_id = decoded_id.as_array::<ML_DSA_87_PUBKEY_SIZE>()?;
		let remote_id = ml_dsa_87::MLDSA87VerificationKey::new(*decoded_beacon_id);

		let ctx = [0u8; 0];
		let pq_sig_slice = &registration.get_pq_key().ok()?[..ML_DSA_87_SIG_SIZE];
		let kem_sig =
			ml_dsa_87::MLDSA87Signature::new(*pq_sig_slice.as_array::<ML_DSA_87_SIG_SIZE>()?);
		let pq_buf_slice = &registration.get_pq_key().ok()?[ML_DSA_87_SIG_SIZE..];
		let _ = ml_dsa_87::verify(&remote_id, pq_buf_slice, &ctx, &kem_sig).ok()?;
		let decoded_kem = decode_kem(pq_buf_slice).ok()?;
		let kem_key_buf = decoded_kem.as_array::<ML_KEM_1024_PUBKEY_SIZE>()?;
		let kem_key = mlkem1024::MlKem1024PublicKey::from(kem_key_buf);

		let mut randomness = [0u8; ML_KEM_1024_ENCAP_RAN_SIZE];
		random::fill_bytes(&mut randomness);
		let (kem_ciphertext, kem_shared) = mlkem1024::encapsulate(&kem_key, randomness);

		let derived_secret = derive_root_key(kem_shared.into())?;
		let server_id = self.get_identity_pk().clone();
		self.set_associated_data(build_additional_data(server_id, remote_id.clone()));

		Some(RegistrationOutput {
			kem_ciphertext,
			derived_secret: derived_secret.into(),
			ephemeral: PhantomData,
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
		bundle.set_identity_key(
			encode_sign(SignType::MlDsa87, self.get_identity_pk().as_slice())
				.ok()?
				.as_slice(),
		);
		bundle.set_kem_cipher_text(reg_out.kem_ciphertext.as_slice());

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

pub fn derive_root_key(shared_secret: MlKemSharedSecret) -> Option<Vec<u8>> {
	// make sure to start inserting after sizeof(Ed25519) so the first bytes are filled with 0xFF as per the spec:
	// https://signal.org/docs/specifications/pqxdh/#cryptographic-notation
	let mut ikm = vec![0xFFu8; crypto_kx::PUBLICKEYBYTES];
	ikm.extend_from_slice(shared_secret.as_slice());

	let prk = crypto_kdf::hkdf::sha512::extract(None, &ikm).ok()?;
	crypto_kdf::hkdf::sha512::expand(KEX_KDF_OUT_LEN, Some(CNSA2_INFO), &prk).ok()
}

pub fn build_additional_data(
	server_id: ml_dsa_87::MLDSA87VerificationKey,
	beacon_id: ml_dsa_87::MLDSA87VerificationKey,
) -> [u8; AD_SIZE] {
	let mut buffer = vec![0u8; 0];
	let mut kex_proto = [0u8; CNSA2_INFO.len()];
	kex_proto.copy_from_slice(CNSA2_INFO);
	buffer.extend_from_slice(&kex_proto);
	let mut sym_proto = [0u8; SYM_RATCHET_INFO.len()];
	sym_proto.copy_from_slice(SYM_RATCHET_INFO);
	buffer.extend_from_slice(&sym_proto);
	let mut encoded_server = encode_sign(SignType::MlDsa87, server_id.as_slice()).unwrap();
	buffer.append(&mut encoded_server);
	let mut encoded_beacon = encode_sign(SignType::MlDsa87, beacon_id.as_slice()).unwrap();
	buffer.append(&mut encoded_beacon);
	*buffer.as_array::<AD_SIZE>().unwrap()
}

#[cfg(test)]
mod tests {
	use crate::{
		beacon::ProviderBeacon, cnsa2::BeaconCryptCnsa2, server::ProviderServer,
		shared::CryptoProvider,
	};

	fn test_register_beacon(
		server: &mut BeaconCryptCnsa2,
		beacon: &mut BeaconCryptCnsa2,
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
		let mut server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
		let b1_reg = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
		let b2_reg = test_register_beacon(&mut server, &mut b2);

		assert_eq!(b1_reg, b2_reg);
	}

	#[test]
	fn server_encrypt_to_multiple() {
		let mut server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
		let _ = test_register_beacon(&mut server, &mut b1);
		let mut b2 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
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
		let mut server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
		let _ = test_register_beacon(&mut server, &mut b1);

		assert!(server.get_id_by_seq(1).is_some());

		let message = [0xFFu8; 32];
		let b1_m1 = server.encrypt_message(&message, true, 1).unwrap();
		let b1_m2 = server.encrypt_message(&message, true, 1).unwrap();
		assert_ne!(b1_m1, b1_m2);
	}

	#[test]
	fn beacon_sign_can_check() {
		let server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk();
		let beacon = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
		let message = [0xFFu8; 32];
		let signed = server.sign_message(&message).unwrap();

		assert!(beacon.verify_signature(signed.as_slice()).is_some());
	}

	#[test]
	fn beacon_can_register() {
		let mut server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk();
		let mut beacon = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
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
		let beacon = BeaconCryptCnsa2::new(true, 0, None, None, None);
		let message = [0xFFu8; 32];
		assert!(beacon.sign_message(&message).is_some());
	}

	#[test]
	fn beacon_can_catch_up() {
		let mut server = BeaconCryptCnsa2::new(false, 0, None, None, None);
		let server_id = server.get_identity_pk().to_owned();

		let mut b1 = BeaconCryptCnsa2::new(true, 0, Some(server_id.as_slice()), None, None);
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
}
