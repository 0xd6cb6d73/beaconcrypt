// SPDX-License-Identifier: 0BSD

use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

use crate::pqxdh::{
	AD_SIZE, build_associated_data, derive_root_key_input, shared_secrets, zeroize_shared_secrets,
};
#[cfg(test)]
use crate::ratchet::KeyMaterial;
use crate::ratchet::{
	RatchetManager, decrypt_message_with_ratchet, encrypt_message_with_ratchet,
	initial_ratchet_hkdf, ratchet_hkdf,
};
use crate::shared::{
	DhSecret, KexDerivedSecret, REGISTRATION_WITNESS, RemotePrincipal, deserialize_server_state,
	roles, serialize_server_state,
};
use crate::{phase1_capnp, phase2_capnp};
use beaconcrypt_protocol_core::pqxdh as verified_pqxdh;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init};
use std::vec;
use zeroize::Zeroize;

pub struct Server {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	control: verified_pqxdh::ServerState,
	known_ids: HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}

pub struct RegResponse {
	pub serialized: Vec<u8>,
	pub kid: u64,
}

pub struct RegistrationOutput {
	pub(crate) derived_secret: KexDerivedSecret,
	pub(crate) control: beaconcrypt_protocol_core::pqxdh::PendingServerRegistration,
}

pub struct StateUpdate<Role: roles::ChainKey> {
	pub kid: u64,
	/// The sequence number of the key consumed by this operation.
	pub seq: u64,
	pub state: RatchetManager,
	pub data: Vec<u8>,
	pub(crate) _role: PhantomData<Role>,
}

pub type SendState = StateUpdate<roles::ChainSendKey>;
pub type RecvState = StateUpdate<roles::ChainRecvKey>;

pub trait ProviderServer {
	/// Validate an `InitKex` and return its one-use pending response token.
	///
	/// A successful call permanently consumes the registration identifier for
	/// replay protection, even if the returned token is dropped or response
	/// construction later fails.
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput>;

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse>;

	/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
	/// and complete ratchet state for `kid`.
	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState>;
	/// Encrypt some bytes to `kid` and return the ciphertext, `kid`, consumed key sequence,
	/// and complete ratchet state for `kid` as a JSON string.
	fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`.
	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid`, consumed key sequence, and complete ratchet state for `kid`
	/// as a JSON string.
	fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String>;
	/// Export the complete server state as JSON
	fn export_state(&self) -> Option<String>;
	/// Restore a server from serialized state, returning `None` if the state is invalid.
	fn try_from_state(server_state: &str) -> Option<Self>
	where
		Self: Sized;
	/// Restore a server from serialized state.
	///
	/// # Panics
	///
	/// Panics if the serialized state is invalid.
	fn from_state(server_state: String) -> Self
	where
		Self: Sized,
	{
		Self::try_from_state(&server_state).expect("failed to restore server state")
	}
}

impl Server {
	pub fn new(server_kid: u64, id_seed: Option<&[u8]>) -> Self {
		ensure_init().expect("Failed to initialize libsodium");
		Self {
			identity_key: id_seed
				.map(|s| crypto_sign::KeyPair::from_seed(s).unwrap())
				.unwrap_or_else(|| crypto_sign::KeyPair::generate().unwrap()),
			identity_key_kid: server_kid,
			control: verified_pqxdh::ServerState::new(server_kid),
			known_ids: HashMap::new(),
			consumed_registrations: HashSet::new(),
		}
	}
	pub fn set_identity_kid(&mut self, k: u64) {
		self.identity_key_kid = k
	}
	pub fn identity_key_kid(&self) -> u64 {
		self.identity_key_kid
	}
	pub fn identity_pk(&self) -> &crypto_sign::PublicKey {
		&self.identity_key.public_key
	}
	pub fn identity_sk(&self) -> &crypto_sign::SecretKey {
		&self.identity_key.secret_key
	}
	pub fn server_kid(&self) -> u64 {
		self.control.last_key_id()
	}
	pub fn add_known_kid(&mut self, k: u64, pk: crypto_sign::PublicKey) {
		self.known_ids
			.entry(k)
			.or_insert(RemotePrincipal::new(pk, RatchetManager::default()));
	}
	pub fn delete_known_kid(&mut self, k: u64) {
		self.known_ids.remove(&k);
	}
	pub fn reset_known_kid(&mut self, k: u64) {
		if let Some(r) = self.ratchet_manager_mut(k) {
			r.reset()
		}
	}
	pub fn new_remote_kid(&mut self) -> Option<u64> {
		let n = verified_pqxdh::server_next_key_id(self.control).ok()?;
		if self.known_ids.contains_key(&n) {
			return None;
		}
		self.control = verified_pqxdh::ServerState::new(n);
		Some(n)
	}
	pub fn pk_by_kid(&self, k: u64) -> Option<&crypto_sign::PublicKey> {
		self.known_ids.get(&k).map(RemotePrincipal::pk)
	}
	pub fn ratchet_manager(&self, k: u64) -> Option<&RatchetManager> {
		self.known_ids.get(&k).map(RemotePrincipal::ratchet)
	}
	pub fn ratchet_manager_mut(&mut self, k: u64) -> Option<&mut RatchetManager> {
		self.known_ids.get_mut(&k).map(RemotePrincipal::ratchet_mut)
	}
	pub fn associated_data(&self, k: u64) -> Option<[u8; AD_SIZE]> {
		Some(build_associated_data(
			self.identity_pk().clone(),
			self.pk_by_kid(k)?.clone(),
		))
	}
	pub fn encrypt_message(&mut self, b: &[u8], k: u64) -> Option<crate::Encrypted> {
		let ad = self.associated_data(k)?;
		let sender = self.identity_key_kid;
		encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)
	}
	pub fn decrypt_message(&mut self, b: &[u8]) -> Option<crate::Decrypted> {
		let k = crate::ratchet::encrypted_frame_sender(b)?;
		let ad = self.associated_data(k)?;
		decrypt_message_with_ratchet(b, k, &ad, self.ratchet_manager_mut(k)?)
	}
	#[cfg(test)]
	pub(crate) fn ratchet_recv_until(&mut self, u: u64, k: u64) -> Option<u64> {
		self.ratchet_manager_mut(k)?.ratchet_recv_until(u)
	}
	#[cfg(test)]
	pub(crate) fn recv_key(&self, s: u64, k: u64) -> Option<&KeyMaterial> {
		self.ratchet_manager(k)?.recv_key(s)
	}
	#[cfg(test)]
	pub(crate) fn delete_recv_key(&mut self, s: u64, k: u64) {
		if let Some(r) = self.ratchet_manager_mut(k) {
			r.delete_recv_key(s)
		}
	}
	#[cfg(test)]
	pub(crate) fn complete_recv_key(&mut self, s: u64, k: u64, a: bool) -> bool {
		self.ratchet_manager_mut(k).is_some_and(|r| {
			matches!(
				(a, r.complete_recv_key(s, a)),
				(
					true,
					beaconcrypt_protocol_core::ratchet::ReceiveDisposition::Consumed
				) | (
					false,
					beaconcrypt_protocol_core::ratchet::ReceiveDisposition::Retained
				)
			)
		})
	}
}

impl ProviderServer for Server {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let control = self.control;
		let reader = capnp::serialize::read_message(buffer, ReaderOptions::new()).ok()?;
		let typed_reader = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(reader);
		let registration = typed_reader.get().ok()?;
		let encoded_identity: [u8; verified_pqxdh::ENCODED_SIGN_PUBLIC_KEY_SIZE] =
			registration.get_identity_key().ok()?.try_into().ok()?;
		if encoded_identity[0] != verified_pqxdh::SIGN_TYPE_ED25519 {
			return None;
		}
		let remote_id = crypto_sign::PublicKey::from_bytes(&encoded_identity[1..]).ok()?;
		let pq_verified = crypto_sign::verify(registration.get_pq_key().ok()?, &remote_id)?;
		let prekey_verified = crypto_sign::verify(registration.get_pre_key().ok()?, &remote_id)?;
		let onetime_verified =
			crypto_sign::verify(registration.get_one_time_key().ok()?, &remote_id)?;
		let init_kex = verified_pqxdh::InitKex::from_encoded(
			encoded_identity,
			prekey_verified.as_slice().try_into().ok()?,
			onetime_verified.as_slice().try_into().ok()?,
			pq_verified.as_slice().try_into().ok()?,
		);
		let verified_registration = verified_pqxdh::validate_init_kex(init_kex).ok()?;
		let registration_id = *verified_pqxdh::registration_id(&verified_registration).as_bytes();
		let registration_status = if self.consumed_registrations.contains(&registration_id) {
			verified_pqxdh::RegistrationStatus::Consumed
		} else {
			verified_pqxdh::RegistrationStatus::Fresh
		};
		verified_pqxdh::validate_registration_status(registration_status).ok()?;
		self.consumed_registrations.try_reserve(1).ok()?;
		let beacon_prekey =
			crypto_kx::PublicKey::from_bytes(verified_registration.beacon_prekey_public_key())
				.ok()?;
		let beacon_onetime =
			crypto_kx::PublicKey::from_bytes(verified_registration.beacon_one_time_public_key())
				.ok()?;
		let ephemeral = crypto_kx::KeyPair::generate().ok()?;
		let pq_pub = crypto_kem::mlkem768::PublicKey::from_bytes(
			verified_registration.beacon_pq_public_key(),
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
		let mut secrets = shared_secrets(dh1, dh2, dh3, dh4, &kem_shared)?;
		let accepted = verified_pqxdh::server_accept(
			control,
			verified_registration,
			registration_status,
			verified_pqxdh::ServerBinding {
				identity_public_key: *self.identity_pk().as_bytes(),
				identity_key_id: self.identity_key_kid,
			},
			verified_pqxdh::ServerCoins {
				ephemeral_public_key: ephemeral.public_key.as_bytes().try_into().ok()?,
				kem_ciphertext: *kem_ciphertext.as_bytes(),
			},
			&secrets,
		);
		zeroize_shared_secrets(&mut secrets);
		let (unchanged, mut pending) = accepted.ok()?;
		debug_assert_eq!(unchanged, control);
		debug_assert_eq!(pending.registration_id().as_bytes(), &registration_id);
		let derived_secret = derive_root_key_input(pending.root_key_input_mut())?;
		let inserted = self.consumed_registrations.insert(registration_id);
		debug_assert!(inserted);

		Some(RegistrationOutput {
			derived_secret,
			control: pending,
		})
	} // ephemeral and kem

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse> {
		let control = self.control;
		let RegistrationOutput {
			derived_secret,
			control: pending,
		} = reg_out;
		let next_key_id = verified_pqxdh::server_next_key_id(control).ok()?;
		let key_id_availability = if self.known_ids.contains_key(&next_key_id) {
			verified_pqxdh::KeyIdAvailability::Occupied
		} else {
			verified_pqxdh::KeyIdAvailability::Available
		};
		let candidate = verified_pqxdh::server_prepare_commit(
			control,
			pending,
			verified_pqxdh::ServerBinding {
				identity_public_key: *self.identity_pk().as_bytes(),
				identity_key_id: self.identity_key_kid,
			},
			key_id_availability,
		)
		.ok()?;
		let remote_kid = candidate.key_id();
		debug_assert_eq!(remote_kid, next_key_id);
		let public_key =
			crypto_sign::PublicKey::from_bytes(candidate.beacon_identity_public_key()).ok()?;
		debug_assert!(!self.known_ids.contains_key(&remote_kid));
		self.known_ids.try_reserve(1).ok()?;
		let mut ratchet = RatchetManager::from_kernel(candidate.derive_ratchet_kernel(
			derived_secret.as_array(),
			initial_ratchet_hkdf,
			ratchet_hkdf,
		));
		let associated_data = *candidate.associated_data();
		let plaintext = data.unwrap_or(REGISTRATION_WITNESS);
		if plaintext.is_empty() {
			return None;
		}
		let authenticated_len =
			verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE.checked_add(plaintext.len())?;
		let mut authenticated_plaintext = Vec::new();
		authenticated_plaintext
			.try_reserve_exact(authenticated_len)
			.ok()?;
		authenticated_plaintext.extend_from_slice(candidate.key_id_binding().as_bytes());
		authenticated_plaintext.extend_from_slice(plaintext);
		let encrypted = encrypt_message_with_ratchet(
			&authenticated_plaintext,
			remote_kid,
			candidate.server_identity_key_id(),
			&associated_data,
			&mut ratchet,
		);
		authenticated_plaintext.zeroize();
		let encrypted = encrypted?;
		let mut msg = TypedBuilder::<phase2_capnp::kex_response::Owned>::new_default();
		let mut bundle = msg.init_root();
		bundle.set_key_id(remote_kid);
		bundle.set_ephemeral_key(candidate.ephemeral_public_key());
		bundle.set_identity_key(candidate.server_identity_public_key());
		bundle.set_kem_cipher_text(candidate.kem_ciphertext());
		bundle.set_app_cipher_text(&encrypted.ciphertext);
		let mut buffer = vec![];
		capnp::serialize_packed::write_message(&mut buffer, msg.borrow_inner()).ok()?;
		let (next_control, established_peer) = verified_pqxdh::server_commit(candidate);
		debug_assert_eq!(established_peer.key_id, remote_kid);
		debug_assert_eq!(established_peer.associated_data, associated_data);
		debug_assert_eq!(&established_peer.identity_public_key, public_key.as_bytes());
		let old = self
			.known_ids
			.insert(remote_kid, RemotePrincipal::new(public_key, ratchet));
		debug_assert!(old.is_none());
		self.control = next_control;
		Some(RegResponse {
			serialized: buffer,
			kid: remote_kid,
		})
	}

	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState> {
		let encrypted = self.encrypt_message(bytes, kid)?;
		let ratchet = self.ratchet_manager_mut(kid)?;
		Some(SendState {
			kid,
			seq: encrypted.seq,
			state: ratchet.clone(),
			data: encrypted.ciphertext,
			_role: PhantomData,
		})
	}

	fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String> {
		serde_json::to_string(&self.encrypt_and_update(bytes, kid)?).ok()
	}

	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState> {
		let decrypted = self.decrypt_message(bytes)?;
		let ratchet = self.ratchet_manager_mut(decrypted.key_id)?;
		Some(RecvState {
			kid: decrypted.key_id,
			seq: decrypted.seq,
			state: ratchet.clone(),
			data: decrypted.plaintext,
			_role: PhantomData,
		})
	}

	fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String> {
		serde_json::to_string(&self.decrypt_and_update(bytes)?).ok()
	}

	fn export_state(&self) -> Option<String> {
		serialize_server_state(
			&self.identity_key,
			self.identity_key_kid,
			self.control.last_key_id(),
			&self.known_ids,
			&self.consumed_registrations,
		)
	}

	fn try_from_state(server_state: &str) -> Option<Self> {
		ensure_init().ok()?;

		let (id_keypair, identity_key_kid, server_kid, known_ids, consumed_registrations) =
			deserialize_server_state(server_state)?;

		Some(Self {
			identity_key: id_keypair,
			identity_key_kid,
			control: verified_pqxdh::ServerState::new(server_kid),
			known_ids,
			consumed_registrations,
		})
	}
}
