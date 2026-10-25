// SPDX-License-Identifier: 0BSD

use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;

use crate::auth::{self, MLDSA_PUBLIC_KEY_LEN, MldsaIdentity};
use crate::pqxdh::AD_SIZE;
#[cfg(test)]
use crate::ratchet::KeyMaterial;
use crate::ratchet::{
	RatchetManager, RatchetStatus, decrypt_message_with_ratchet, encrypt_message_with_ratchet,
	encrypt_registration_message_with_ratchet,
};
use crate::shared::{
	EstablishedRemote, REGISTRATION_WITNESS, deserialize_server_state, roles,
	serialize_server_state,
};
use beaconcrypt_core::pqxdh as verified_pqxdh;
use beaconcrypt_core::session::ServerAuthenticationPin;
#[cfg(test)]
use beaconcrypt_core::session::SessionBinding;
use beaconcrypt_parse::{KexResponse, decode_init};
use libsodium_rs::{crypto_sign, ensure_init};
use zeroize::{Zeroize, Zeroizing};

pub struct Server {
	identity_key: crypto_sign::KeyPair,
	mldsa_identity: MldsaIdentity,
	identity_key_kid: u64,
	control: verified_pqxdh::ServerState,
	known_ids: HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>,
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}

pub struct RegResponse {
	pub serialized: Vec<u8>,
	pub kid: u64,
}

pub struct RegistrationOutput {
	agreement: beaconcrypt_core::agreement::ServerAgreement,
}

fn registration_response_len(application_len: usize, assigned_key_id: u64) -> Option<usize> {
	let ciphertext_len = verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE
		.checked_add(application_len)?
		.checked_add(crate::ratchet::MESSAGE_OVERHEAD)?;
	beaconcrypt_parse::encoded_response_len(
		[
			verified_pqxdh::SIGN_PUBLIC_KEY_SIZE,
			verified_pqxdh::X25519_PUBLIC_KEY_SIZE,
			verified_pqxdh::MLKEM768_CIPHERTEXT_SIZE,
			ciphertext_len,
			auth::MLDSA_SIGNATURE_LEN,
		],
		assigned_key_id,
	)
}

/// The state effect of one receive attempt.
///
/// `Rejected` is returned only when the complete entry state is preserved. `Accepted` means the
/// selected receive key was consumed and the resulting state must be committed before releasing
/// the output from a persistent owner.
pub(crate) enum ReceiveTransition<T> {
	Rejected,
	Accepted(T),
}

impl<T> ReceiveTransition<T> {
	pub(crate) fn map<U>(self, map: impl FnOnce(T) -> U) -> ReceiveTransition<U> {
		match self {
			Self::Rejected => ReceiveTransition::Rejected,
			Self::Accepted(output) => ReceiveTransition::Accepted(map(output)),
		}
	}

	pub(crate) fn into_option(self) -> Option<T> {
		match self {
			Self::Rejected => None,
			Self::Accepted(output) => Some(output),
		}
	}
}

/// An inert, serialization-only view of ratchet state.
///
/// This value has no operational methods and cannot be deserialized into a live ratchet.
pub struct RatchetSnapshot {
	json: Zeroizing<String>,
}

impl RatchetSnapshot {
	pub(crate) fn try_capture(ratchet: &RatchetManager) -> serde_json::Result<Self> {
		Ok(Self {
			json: Zeroizing::new(serde_json::to_string(ratchet)?),
		})
	}

	pub(crate) fn capture(ratchet: &RatchetManager) -> Option<Self> {
		Self::try_capture(ratchet).ok()
	}

	pub fn as_str(&self) -> &str {
		self.json.as_str()
	}
}

pub struct StateUpdate<Role: roles::ChainKey> {
	pub kid: u64,
	/// The sequence number of the key consumed by this operation.
	pub seq: u64,
	/// Inert serialized state for observation or transport; this cannot be made operational.
	pub state: RatchetSnapshot,
	pub data: Vec<u8>,
	pub(crate) _role: PhantomData<Role>,
}

impl<Role: roles::ChainKey> StateUpdate<Role> {
	pub(crate) fn try_render_json(&self) -> serde_json::Result<String> {
		serde_json::to_string(self)
	}
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
	/// and an inert serialized view of the ratchet for `kid`.
	///
	/// This update is not an activatable persistence snapshot. Use [`crate::PersistentServer`] when
	/// results must be committed durably before release.
	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState>;
	/// Return the same inert update encoded as JSON.
	fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String>;
	/// Decrypt a message using the recv keychain associated with the sender ID in the encrypted frame
	/// and return the plaintext, `kid`, consumed key sequence, and an inert serialized view of the
	/// ratchet for `kid`.
	///
	/// This update is not an activatable persistence snapshot. Use [`crate::PersistentServer`] when
	/// results must be committed durably before release.
	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState>;
	/// Return the same inert update encoded as JSON.
	fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String>;
}

impl Server {
	/// Construct a server, panicking if initialization, seed validation or key generation fails.
	/// Use [`Self::try_new`] for recoverable construction failures.
	pub fn new(server_kid: u64, id_seed: Option<&[u8]>, mldsa_seed: Option<&[u8]>) -> Self {
		Self::try_new(server_kid, id_seed, mldsa_seed).expect("Failed to construct server")
	}

	/// Construct a server without panicking on reported initialization, seed-length or key-generation errors.
	/// A supplied seed must be 32 secret, uniformly generated bytes; this is not a password KDF.
	pub fn try_new(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
	) -> Result<Self, crate::KeyGenError> {
		ensure_init().map_err(|_| crate::KeyGenError)?;
		let identity_key = match id_seed {
			Some(seed) => crypto_sign::KeyPair::from_seed(seed),
			None => crypto_sign::KeyPair::generate(),
		}
		.map_err(|_| crate::KeyGenError)?;
		let mldsa_identity = match mldsa_seed {
			Some(seed) => {
				MldsaIdentity::from_seed(seed.try_into().map_err(|_| crate::KeyGenError)?)
			}
			None => MldsaIdentity::generate()?,
		};
		Ok(Self {
			identity_key,
			mldsa_identity,
			identity_key_kid: server_kid,
			control: verified_pqxdh::ServerState::new(server_kid),
			known_ids: HashMap::new(),
			consumed_registrations: HashSet::new(),
		})
	}
	/// Provision this signing key alongside the Ed25519 server identity.
	pub fn mldsa_public_key(&self) -> [u8; MLDSA_PUBLIC_KEY_LEN] {
		self.mldsa_identity.public_key()
	}

	fn authentication_pin(&self) -> Option<ServerAuthenticationPin> {
		auth::fingerprint_pin(
			verified_pqxdh::ServerBinding {
				identity_public_key: *self.identity_pk().as_bytes(),
				identity_key_id: self.identity_key_kid,
			},
			self.mldsa_public_key(),
		)
	}

	/// Hash of the key authenticated by InitKex; authorization remains the caller's responsibility.
	pub fn mldsa_public_key_hash_by_kid(&self, kid: u64) -> Option<&[u8; 64]> {
		Some(self.known_ids.get(&kid)?.mldsa_public_key_hash())
	}

	#[cfg(test)]
	pub(crate) fn set_identity_kid(&mut self, k: u64) {
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
	#[cfg(test)]
	pub(crate) fn add_known_kid(&mut self, k: u64, pk: crypto_sign::PublicKey) {
		let pin = self.authentication_pin().unwrap();
		let binding = SessionBinding::from_trusted_metadata(
			pin.binding(),
			k,
			*pk.as_bytes(),
			*pin.fingerprint(),
			[0; 64],
		);
		self.known_ids.entry(k).or_insert(EstablishedRemote::new(
			pk,
			RatchetManager::default(),
			binding,
		));
	}
	#[cfg(test)]
	pub(crate) fn delete_known_kid(&mut self, k: u64) {
		self.known_ids.remove(&k);
	}
	#[cfg(test)]
	pub(crate) fn new_remote_kid(&mut self) -> Option<u64> {
		let n = verified_pqxdh::server_next_key_id(self.control).ok()?;
		if self.known_ids.contains_key(&n) {
			return None;
		}
		self.control = verified_pqxdh::ServerState::new(n);
		Some(n)
	}
	pub fn pk_by_kid(&self, k: u64) -> Option<&crypto_sign::PublicKey> {
		self.known_ids.get(&k).map(EstablishedRemote::pk)
	}
	pub fn ratchet_status(&self, k: u64) -> Option<RatchetStatus> {
		Some(self.ratchet_manager(k)?.status())
	}
	pub(crate) fn registration_response_fits(&self, data: Option<&[u8]>) -> bool {
		let next_key_id = self.control.last_key_id().saturating_add(1);
		registration_response_len(data.unwrap_or(REGISTRATION_WITNESS).len(), next_key_id).is_some()
	}
	pub(crate) fn ratchet_manager(&self, k: u64) -> Option<&RatchetManager> {
		self.known_ids.get(&k).map(EstablishedRemote::ratchet)
	}
	pub(crate) fn ratchet_manager_mut(&mut self, k: u64) -> Option<&mut RatchetManager> {
		self.known_ids
			.get_mut(&k)
			.map(EstablishedRemote::ratchet_mut)
	}
	pub(crate) fn associated_data(&self, k: u64) -> Option<[u8; AD_SIZE]> {
		Some(*self.known_ids.get(&k)?.binding().associated_data())
	}
	pub fn encrypt_message(&mut self, b: &[u8], k: u64) -> Option<crate::Encrypted> {
		let ad = self.associated_data(k)?;
		let sender = self.identity_key_kid;
		encrypt_message_with_ratchet(b, k, sender, &ad, self.ratchet_manager_mut(k)?)
	}
	pub fn decrypt_message(&mut self, b: &[u8]) -> Option<crate::Decrypted> {
		self.decrypt_message_transition(b).into_option()
	}

	pub(crate) fn decrypt_message_transition(
		&mut self,
		b: &[u8],
	) -> ReceiveTransition<crate::Decrypted> {
		let Some(k) = crate::ratchet::encrypted_frame_sender(b) else {
			return ReceiveTransition::Rejected;
		};
		let Some(ad) = self.associated_data(k) else {
			return ReceiveTransition::Rejected;
		};
		let Some(ratchet) = self.ratchet_manager_mut(k) else {
			return ReceiveTransition::Rejected;
		};
		match decrypt_message_with_ratchet(b, k, &ad, ratchet) {
			Some(decrypted) => ReceiveTransition::Accepted(decrypted),
			None => ReceiveTransition::Rejected,
		}
	}

	pub(crate) fn try_receive_update(
		&self,
		decrypted: crate::Decrypted,
	) -> serde_json::Result<RecvState> {
		let kid = decrypted.key_id;
		let ratchet = self
			.ratchet_manager(kid)
			.expect("an accepted receive retains its established peer");
		let state = RatchetSnapshot::try_capture(ratchet)?;
		Ok(RecvState {
			kid,
			seq: decrypted.seq,
			state,
			data: decrypted.plaintext,
			_role: PhantomData,
		})
	}

	fn decrypt_and_update_transition(&mut self, bytes: &[u8]) -> ReceiveTransition<RecvState> {
		let transition = self.decrypt_message_transition(bytes);
		transition.map(|decrypted| {
			self.try_receive_update(decrypted)
				.expect("an accepted receive state must have a serializable snapshot")
		})
	}

	pub(crate) fn serialize_state(&self) -> Option<String> {
		serialize_server_state(
			&self.identity_key,
			self.identity_key_kid,
			self.control.last_key_id(),
			&self.known_ids,
			&self.consumed_registrations,
			&self.mldsa_identity,
		)
	}

	pub(crate) fn deserialize_state(server_state: &str) -> Option<Self> {
		ensure_init().ok()?;
		let (
			id_keypair,
			identity_key_kid,
			server_kid,
			known_ids,
			consumed_registrations,
			mldsa_identity,
		) = deserialize_server_state(server_state)?;
		Some(Self {
			identity_key: id_keypair,
			mldsa_identity,
			identity_key_kid,
			control: verified_pqxdh::ServerState::new(server_kid),
			known_ids,
			consumed_registrations,
		})
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
					beaconcrypt_core::ratchet::ReceiveDisposition::Consumed
				) | (
					false,
					beaconcrypt_core::ratchet::ReceiveDisposition::Retained
				)
			)
		})
	}
}

impl ProviderServer for Server {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		use beaconcrypt_core::agreement::{self, AgreementEffect};
		use beaconcrypt_core::registration::InitPacket;
		let control = self.control;
		let registration = decode_init(buffer)?;
		let packet = InitPacket::from_slices(
			registration.identity_key,
			registration.pre_key,
			registration.one_time_key,
			registration.pq_key,
			registration.mldsa_public_key,
			registration.signature,
		)?;
		let authenticated = auth::authenticate_init(self.authentication_pin()?, packet)?;
		let registration_id = *authenticated.registration_id().as_bytes();
		let status = if self.consumed_registrations.contains(&registration_id) {
			verified_pqxdh::RegistrationStatus::Consumed
		} else {
			verified_pqxdh::RegistrationStatus::Fresh
		};
		verified_pqxdh::validate_registration_status(status).ok()?;
		self.consumed_registrations.try_reserve(1).ok()?;
		let effect = crate::pqxdh::execute_agreement(
			agreement::begin_server_agreement(control, status, authenticated),
			crate::pqxdh::RegistrationKeys {
				identity_secret: self.identity_sk(),
				beacon_prekey: None,
				beacon_one_time: None,
				beacon_kem: None,
			},
		);
		let agreement = match effect {
			AgreementEffect::ServerComplete(agreement) => agreement,
			_ => return None,
		};
		debug_assert_eq!(agreement.registration_id().as_bytes(), &registration_id);
		let inserted = self.consumed_registrations.insert(registration_id);
		debug_assert!(inserted);
		Some(RegistrationOutput { agreement })
	}

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse> {
		use beaconcrypt_core::registration;
		let control = self.control;
		let plaintext = data.unwrap_or(REGISTRATION_WITNESS);
		let next_key_id = verified_pqxdh::server_next_key_id(control).ok()?;
		registration_response_len(plaintext.len(), next_key_id)?;
		let RegistrationOutput { agreement } = reg_out;
		let availability = if self.known_ids.contains_key(&next_key_id) {
			verified_pqxdh::KeyIdAvailability::Occupied
		} else {
			verified_pqxdh::KeyIdAvailability::Available
		};
		let pending = registration::begin_server_completion(
			control,
			&self.authentication_pin()?,
			availability,
			agreement,
			plaintext,
		)
		.ok()?;
		self.known_ids.try_reserve(1).ok()?;
		let response = verified_pqxdh::InitialRatchetKdfResponse::from_bytes(
			crate::ratchet::initial_ratchet_hkdf(pending.request()),
		);
		let mut pending = pending.resume(Some(response)).ok()?;
		let mut ratchet = RatchetManager::from_kernel(pending.take_kernel()?);
		let request = pending.request();
		let length = request.plaintext[0]
			.len()
			.checked_add(request.plaintext[1].len())?;
		let mut authenticated_plaintext = Vec::new();
		authenticated_plaintext.try_reserve_exact(length).ok()?;
		for part in request.plaintext {
			authenticated_plaintext.extend_from_slice(part);
		}
		let encrypted = encrypt_registration_message_with_ratchet(
			&authenticated_plaintext,
			request.target_key_id,
			request.sender_key_id,
			request.associated_data,
			&mut ratchet,
		);
		authenticated_plaintext.zeroize();
		let sequence = encrypted.as_ref().map_or(0, |encrypted| encrypted.seq);
		let pending = pending
			.resume(
				ratchet.into_kernel(),
				sequence,
				encrypted
					.as_ref()
					.map(|encrypted| encrypted.ciphertext.as_slice()),
			)
			.ok()?;
		let hash = auth::execute_hash(&pending.request());
		let pending = pending.resume(hash).ok()?;
		let signature = self.mldsa_identity.sign_requested(&pending.request());
		let ready = pending.resume(signature.as_deref()).ok()?;
		let message = ready.message();
		let buffer = crate::wire::encode_response(KexResponse {
			identity_key: message.identity_key,
			ephemeral_key: message.ephemeral_key,
			kem_cipher_text: message.kem_cipher_text,
			key_id: message.key_id,
			app_cipher_text: message.application_ciphertext,
			signature: message.signature,
		});
		let (next_control, binding, kernel, buffer) = ready.publish(buffer).ok()?.into_parts();
		let remote_kid = binding.assigned_key_id();
		let public_key =
			crypto_sign::PublicKey::from_bytes(binding.beacon_identity_public_key()).ok()?;
		debug_assert_eq!(remote_kid, next_key_id);
		let old = self.known_ids.insert(
			remote_kid,
			EstablishedRemote::new(public_key, RatchetManager::from_kernel(kernel), binding),
		);
		debug_assert!(old.is_none());
		self.control = next_control;
		Some(RegResponse {
			serialized: buffer,
			kid: remote_kid,
		})
	}

	fn encrypt_and_update(&mut self, bytes: &[u8], kid: u64) -> Option<SendState> {
		let encrypted = self.encrypt_message(bytes, kid)?;
		let state = RatchetSnapshot::capture(self.ratchet_manager(kid)?)?;
		Some(SendState {
			kid,
			seq: encrypted.seq,
			state,
			data: encrypted.ciphertext,
			_role: PhantomData,
		})
	}

	fn encrypt_and_update_json(&mut self, bytes: &[u8], kid: u64) -> Option<String> {
		serde_json::to_string(&self.encrypt_and_update(bytes, kid)?).ok()
	}

	fn decrypt_and_update(&mut self, bytes: &[u8]) -> Option<RecvState> {
		self.decrypt_and_update_transition(bytes).into_option()
	}

	fn decrypt_and_update_json(&mut self, bytes: &[u8]) -> Option<String> {
		self.decrypt_and_update_transition(bytes)
			.map(|update| {
				update
					.try_render_json()
					.expect("an accepted receive update must be serializable as JSON")
			})
			.into_option()
	}
}

#[cfg(test)]
mod size_tests {
	use super::*;
	use beaconcrypt_parse::MAX_MESSAGE_SIZE;

	#[test]
	#[cfg(feature = "beacon")]
	fn established_peer_retains_its_record_binding_across_restore() {
		let mut server = Server::new(42, Some(&[7; 32]), Some(&[8; 32]));
		let mut beacon = crate::Beacon::new(
			42,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let init = crate::ProviderBeacon::get_registration_bundle(&mut beacon).unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(accepted, None).unwrap();
		crate::ProviderBeacon::finish_registration(&mut beacon, &response.serialized).unwrap();
		let expected = beacon.associated_data().unwrap();
		let peer = server.known_ids.get(&response.kid).unwrap();
		assert_eq!(peer.binding().associated_data(), &expected);
		assert_eq!(peer.binding().assigned_key_id(), response.kid);
		assert_eq!(peer.binding().server_binding().identity_key_id, 42);
		assert_eq!(
			peer.binding().beacon_identity_public_key(),
			beacon.identity_pk().as_bytes()
		);
		let snapshot = server.serialize_state().unwrap();
		let mut restored = Server::deserialize_state(&snapshot).unwrap();
		assert_eq!(restored.serialize_state().unwrap(), snapshot);
		let binding = restored.known_ids.get(&response.kid).unwrap().binding();
		assert_eq!(binding.associated_data(), &expected);
		assert_eq!(binding.assigned_key_id(), response.kid);
		assert_eq!(binding.server_binding(), peer.binding().server_binding());
		assert_eq!(
			binding.beacon_identity_public_key(),
			peer.binding().beacon_identity_public_key()
		);
		assert_eq!(
			binding.server_fingerprint(),
			peer.binding().server_fingerprint()
		);
		assert_eq!(
			binding.beacon_fingerprint(),
			peer.binding().beacon_fingerprint()
		);
		let encrypted = restored
			.encrypt_message(b"restored binding", response.kid)
			.unwrap();
		assert_eq!(
			beacon.decrypt_message(&encrypted).unwrap().plaintext,
			b"restored binding"
		);
		let encrypted = beacon.encrypt_message(b"same restored peer").unwrap();
		assert_eq!(
			restored.decrypt_message(&encrypted).unwrap().plaintext,
			b"same restored peer"
		);
	}

	#[test]
	#[cfg(feature = "beacon")]
	fn established_record_ad_is_stored_instead_of_rehashed_from_current_identity() {
		let mut server = Server::new(42, Some(&[7; 32]), Some(&[8; 32]));
		let mut beacon = crate::Beacon::new(
			42,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let init = crate::ProviderBeacon::get_registration_bundle(&mut beacon).unwrap();
		let accepted = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(accepted, None).unwrap();
		crate::ProviderBeacon::finish_registration(&mut beacon, &response.serialized).unwrap();
		let expected = server.associated_data(response.kid).unwrap();
		// There is no production identity-replacement API. This private change
		// distinguishes a stored session binding from recomputation on each record.
		server.mldsa_identity = MldsaIdentity::from_seed([9; 32]);
		assert_ne!(
			auth::public_key_hash(&server.mldsa_public_key())
				.unwrap()
				.as_slice(),
			&expected[153..217]
		);
		assert_eq!(server.associated_data(response.kid), Some(expected));
		let encrypted = server
			.encrypt_message(b"stored binding", response.kid)
			.unwrap();
		assert_eq!(
			beacon.decrypt_message(&encrypted).unwrap().plaintext,
			b"stored binding"
		);
	}

	#[test]
	fn registration_limit_includes_binding_ciphertext_signature_and_cbor() {
		// Near the limit, the payload contributes 88 bytes beyond the application
		// plaintext (8 binding + 80 authentication), and CBOR adds 4,480 including
		// the mandatory 3,309-byte signature.
		let maximum_application = MAX_MESSAGE_SIZE - 4_568;
		assert_eq!(
			registration_response_len(maximum_application, 1),
			Some(MAX_MESSAGE_SIZE)
		);
		assert_eq!(registration_response_len(maximum_application + 1, 1), None);

		// The full-width assigned identifier adds eight bytes; the sender is implicit.
		let maximum_application = MAX_MESSAGE_SIZE - 4_576;
		assert_eq!(
			registration_response_len(maximum_application, u64::MAX),
			Some(MAX_MESSAGE_SIZE)
		);
		assert_eq!(
			registration_response_len(maximum_application + 1, u64::MAX),
			None
		);
		assert_eq!(registration_response_len(usize::MAX, 1), None);
	}
}
