// SPDX-License-Identifier: 0BSD

use crate::error::{DecodingError, EncodingError};
use crate::{cryptoframe_capnp, protogram_capnp};
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libcrux_aesgcm::AeadConsts as _;
use libcrux_aesgcm::{AesGcm256, AesGcm256Key, AesGcm256Nonce, AesGcm256Tag, NONCE_LEN, TAG_LEN};
use libcrux_ml_dsa::ml_dsa_87;
use libcrux_ml_kem::mlkem1024;
use libsodium_rs::{
	SodiumError, crypto_aead, crypto_kdf, crypto_kem, crypto_kx, crypto_sign, ensure_init,
};
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{LazyLock, Mutex};
use std::{mem, vec};
use zeroize::{Zeroize, Zeroizing};

pub type AeadKey = AesGcm256Key;
pub type AeadNonce = AesGcm256Nonce;

pub const ML_DSA_RAND_SIZE: usize = libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE;
pub const ML_DSA_PK_SIZE: usize = ml_dsa_87::MLDSA87VerificationKey::len();
pub const ML_DSA_SIGN_RANDOM_SIZE: usize = 32;
pub const ML_KEM_1024_SEED_SIZE: usize = libcrux_ml_kem::KEY_GENERATION_SEED_SIZE;
pub const ML_DSA_87_SIG_SIZE: usize = ml_dsa_87::MLDSA87Signature::len();
pub const ML_DSA_87_PUBKEY_SIZE: usize = ml_dsa_87::MLDSA87VerificationKey::len();
pub const ML_KEM_1024_CT_SIZE: usize = mlkem1024::MlKem1024Ciphertext::len();

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
	// stores the server's `seq` for the beacon. Stores the counter of remote `seq`s for the server
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
	fn new(is_beacon: bool, server_kid: u64, server_pk: Option<&[u8]>) -> Self {
		ensure_init().expect("Failed to initialize libsodium");

		let sig_random =
			libsodium_rs::random::bytes(libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE);
		let sig_rand = *sig_random.as_array::<ML_DSA_RAND_SIZE>().unwrap();
		let signing = ml_dsa_87::generate_key_pair(sig_rand);

		let kem_random =
			libsodium_rs::random::bytes(libcrux_ml_dsa::KEY_GENERATION_RANDOMNESS_SIZE);
		let kem_rand = *kem_random.as_array::<ML_KEM_1024_SEED_SIZE>().unwrap();
		let kem = mlkem1024::generate_key_pair(kem_rand);
		let known = if let Some(pk) = server_pk {
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
		builder.set_key_seq(self.identity_key_kid);
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
			self.get_id_by_seq(reader.get_key_seq())?
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

		bundle.set_identity_key(self.get_identity_pk().as_slice());
		bundle.set_pq_key(self.get_pq_pk().as_slice());
		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).unwrap();
		Some(buffer)
	}
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
		let response = typed_reader.get().ok()?;

		let mldsa_buf = response
			.get_identity_key()
			.ok()?
			.as_array::<ML_DSA_87_PUBKEY_SIZE>()
			.unwrap();
		let mldsa = ml_dsa_87::MLDSA87VerificationKey::new(*mldsa_buf);

		let kem_ct_buf = response
			.get_kem_cipher_text()
			.ok()?
			.as_array::<ML_KEM_1024_CT_SIZE>()
			.unwrap();
		let kem_ct = mlkem1024::MlKem1024Ciphertext::from(kem_ct_buf);

		None
	}
}
