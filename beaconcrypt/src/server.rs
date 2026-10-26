// SPDX-License-Identifier: 0BSD

#[cfg(not(target_has_atomic = "ptr"))]
use alloc::rc::Rc as SharedIdentity;
#[cfg(target_has_atomic = "ptr")]
use alloc::sync::Arc as SharedIdentity;
use alloc::{string::String, vec::Vec};
use core::marker::PhantomData;

use crate::collections::{HashMap, HashSet, map_with_key, set_with_key};

use crate::auth::{self, MLDSA_PUBLIC_KEY_LEN, MldsaIdentity};
use crate::pqxdh::AD_SIZE;
#[cfg(test)]
use crate::ratchet::KeyMaterial;
use crate::ratchet::{
	RatchetManager, RatchetStatus, decrypt_message_with_ratchet, encrypt_message_with_ratchet,
};
use crate::shared::{EstablishedRemote, deserialize_server_state, roles, serialize_server_state};
use beaconcrypt_core::pqxdh as verified_pqxdh;
use beaconcrypt_core::session::ServerAuthenticationPin;
#[cfg(test)]
use beaconcrypt_core::session::SessionBinding;
use beaconcrypt_crypto::{TryCryptoRng, crypto_sign};
use beaconcrypt_parse::{KexResponse, decode_init};
use zeroize::Zeroizing;

struct ServerIdentity {
	identity_key: crypto_sign::KeyPair,
	mldsa_identity: MldsaIdentity,
	identity_key_kid: u64,
}

pub struct Server {
	identity: SharedIdentity<ServerIdentity>,
	control: verified_pqxdh::ServerState,
	known_ids: HashMap<u64, EstablishedRemote<crypto_sign::PublicKey>>,
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}

pub struct RegResponse {
	pub serialized: Vec<u8>,
	pub kid: u64,
}

pub struct RegistrationOutput {
	registration: beaconcrypt_core::peer::ConsumedRegistration,
	registration_id: [u8; verified_pqxdh::REGISTRATION_ID_SIZE],
}

impl RegistrationOutput {
	pub(crate) fn row_registration_id(&self) -> [u8; verified_pqxdh::REGISTRATION_ID_SIZE] {
		self.registration_id
	}
}

// This interpreter borrows the exact byte view already selected by core.
fn registration_application_bytes<'a>(
	request: &'a beaconcrypt_core::transport::RegistrationApplication<'_>,
) -> &'a [u8] {
	match request {
		beaconcrypt_core::transport::RegistrationApplication::Witness(bytes) => bytes,
		beaconcrypt_core::transport::RegistrationApplication::Provided(bytes) => bytes,
	}
}

fn registration_response_len(application_len: usize, assigned_key_id: u64) -> Option<usize> {
	beaconcrypt_core::transport::registration_response_len(application_len, assigned_key_id)
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
	#[cfg(feature = "std")]
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
	/// Construct a server, panicking if seed validation or key generation fails.
	/// Use [`Self::try_new`] for recoverable construction failures.
	#[cfg(feature = "std")]
	pub fn new(server_kid: u64, id_seed: Option<&[u8]>, mldsa_seed: Option<&[u8]>) -> Self {
		Self::try_new(server_kid, id_seed, mldsa_seed).expect("Failed to construct server")
	}

	/// Construct a server with operating-system entropy, returning input or RNG failures.
	/// A supplied seed must be 32 secret, uniformly generated bytes; this is not a password KDF.
	#[cfg(feature = "std")]
	pub fn try_new(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
	) -> Result<Self, crate::KeyGenError> {
		Self::try_new_with_rng(
			server_kid,
			id_seed,
			mldsa_seed,
			&mut beaconcrypt_crypto::OsRng,
		)
	}

	/// Construct a server with caller-provided cryptographic entropy.
	/// Supplied identity seeds must be secret, uniformly generated 32-byte values.
	pub fn try_new_with_rng<R: TryCryptoRng + ?Sized>(
		server_kid: u64,
		id_seed: Option<&[u8]>,
		mldsa_seed: Option<&[u8]>,
		rng: &mut R,
	) -> Result<Self, crate::KeyGenError> {
		let identity_key = match id_seed {
			Some(seed) => crypto_sign::KeyPair::from_seed(seed),
			None => crypto_sign::KeyPair::generate_with_rng(rng),
		}
		.map_err(|_| crate::KeyGenError)?;
		let mldsa_identity = match mldsa_seed {
			Some(seed) => {
				MldsaIdentity::from_seed(seed.try_into().map_err(|_| crate::KeyGenError)?)
			}
			None => MldsaIdentity::generate_with_rng(rng)?,
		};
		let known_ids = map_with_key(identity_key.secret_key.as_bytes());
		let consumed_registrations = set_with_key(identity_key.secret_key.as_bytes());
		Ok(Self {
			identity: SharedIdentity::new(ServerIdentity {
				identity_key,
				mldsa_identity,
				identity_key_kid: server_kid,
			}),
			control: verified_pqxdh::ServerState::new(server_kid),
			known_ids,
			consumed_registrations,
		})
	}
	/// Provision this signing key alongside the Ed25519 server identity.
	pub fn mldsa_public_key(&self) -> [u8; MLDSA_PUBLIC_KEY_LEN] {
		self.identity.mldsa_identity.public_key()
	}

	fn authentication_pin(&self) -> Option<ServerAuthenticationPin> {
		auth::fingerprint_pin(
			verified_pqxdh::ServerBinding {
				identity_public_key: *self.identity_pk().as_bytes(),
				identity_key_id: self.identity_key_kid(),
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
		SharedIdentity::get_mut(&mut self.identity)
			.expect("test identity has no outstanding row session")
			.identity_key_kid = k
	}
	pub fn identity_key_kid(&self) -> u64 {
		self.identity.identity_key_kid
	}
	pub fn identity_pk(&self) -> &crypto_sign::PublicKey {
		&self.identity.identity_key.public_key
	}
	pub fn identity_sk(&self) -> &crypto_sign::SecretKey {
		&self.identity.identity_key.secret_key
	}
	pub fn server_kid(&self) -> u64 {
		self.control.last_key_id()
	}

	/// Create operation-local state while retaining the already expanded immutable identity.
	/// Peers and registration history are supplied by the surrounding database transaction.
	pub(crate) fn row_session(&self, last_key_id: u64) -> Self {
		Self {
			identity: SharedIdentity::clone(&self.identity),
			control: verified_pqxdh::ServerState::new(last_key_id),
			known_ids: HashMap::with_hasher(self.known_ids.hasher().clone()),
			consumed_registrations: HashSet::with_hasher(
				self.consumed_registrations.hasher().clone(),
			),
		}
	}

	pub(crate) fn put_row_peer(
		&mut self,
		kid: u64,
		peer: EstablishedRemote<crypto_sign::PublicKey>,
	) -> Option<()> {
		self.known_ids.try_reserve(1).ok()?;
		match self.known_ids.entry(kid) {
			hashbrown::hash_map::Entry::Vacant(entry) => {
				entry.insert(peer);
				Some(())
			}
			hashbrown::hash_map::Entry::Occupied(_) => None,
		}
	}

	pub(crate) fn take_row_peer(
		&mut self,
		kid: u64,
	) -> Option<EstablishedRemote<crypto_sign::PublicKey>> {
		self.known_ids.remove(&kid)
	}

	/// Restore a trusted peer row using this identity and the selected row's peer identifier.
	pub(crate) fn deserialize_row_peer(
		&self,
		kid: u64,
		payload: &[u8],
	) -> Option<EstablishedRemote<crypto_sign::PublicKey>> {
		crate::shared::deserialize_row_peer(payload, self.authentication_pin()?, kid)
	}

	/// Encode only the immutable identity using the existing checked snapshot payload codec.
	pub(crate) fn serialize_row_identity(&self) -> Option<String> {
		self.row_session(self.identity_key_kid()).serialize_state()
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
		let application = beaconcrypt_core::transport::normalize_registration_application(data);
		registration_response_len(
			registration_application_bytes(&application).len(),
			next_key_id,
		)
		.is_some()
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
		let sender = self.identity_key_kid();
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
			&self.identity.identity_key,
			self.identity_key_kid(),
			self.control.last_key_id(),
			&self.known_ids,
			&self.consumed_registrations,
			&self.identity.mldsa_identity,
		)
	}

	pub(crate) fn deserialize_state(server_state: &str) -> Option<Self> {
		let (
			id_keypair,
			identity_key_kid,
			server_kid,
			known_ids,
			consumed_registrations,
			mldsa_identity,
		) = deserialize_server_state(server_state)?;
		Some(Self {
			identity: SharedIdentity::new(ServerIdentity {
				identity_key: id_keypair,
				mldsa_identity,
				identity_key_kid,
			}),
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

impl Server {
	/// Validate a bundle using caller-provided entropy and consume its registration identifier.
	pub fn get_shared_secret_with_rng<R: TryCryptoRng + ?Sized>(
		&mut self,
		buffer: &[u8],
		rng: &mut R,
	) -> Option<RegistrationOutput> {
		use beaconcrypt_core::agreement::AgreementEffect;
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
		let lookup = beaconcrypt_core::peer::begin_registration_lookup(control, authenticated);
		let registration_id = *lookup.request().as_bytes();
		let consumed = self.consumed_registrations.contains(&registration_id);
		let effect = lookup.resume(consumed);
		if matches!(effect, AgreementEffect::Rejected(_)) {
			return None;
		}
		self.consumed_registrations.try_reserve(1).ok()?;
		let effect = crate::pqxdh::execute_agreement(
			effect,
			crate::pqxdh::RegistrationKeys {
				identity_secret: self.identity_sk(),
				beacon_prekey: None,
				beacon_one_time: None,
				beacon_kem: None,
			},
			rng,
		);
		let agreement = match effect {
			AgreementEffect::ServerComplete(agreement) => agreement,
			_ => return None,
		};
		let pending = beaconcrypt_core::peer::begin_registration_insert(agreement);
		let registration_id = *pending.request().as_bytes();
		let inserted = self
			.consumed_registrations
			.insert(*pending.request().as_bytes());
		let registration = pending.resume(inserted)?;
		Some(RegistrationOutput {
			registration,
			registration_id,
		})
	}
}

impl ProviderServer for Server {
	#[cfg(feature = "std")]
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		self.get_shared_secret_with_rng(buffer, &mut beaconcrypt_crypto::OsRng)
	}

	fn build_registration_response(
		&mut self,
		reg_out: RegistrationOutput,
		data: Option<&[u8]>,
	) -> Option<RegResponse> {
		let control = self.control;
		let application = beaconcrypt_core::transport::normalize_registration_application(data);
		let plaintext = registration_application_bytes(&application);
		let RegistrationOutput { registration, .. } = reg_out;
		let lookup = beaconcrypt_core::peer::begin_completion_lookup(
			control,
			self.authentication_pin()?,
			registration,
			plaintext,
		)
		.ok()?;
		let next_key_id = lookup.request();
		registration_response_len(plaintext.len(), next_key_id)?;
		let pending = lookup
			.resume(self.known_ids.contains_key(&next_key_id))
			.ok()?;
		self.known_ids.try_reserve(1).ok()?;
		let response = verified_pqxdh::InitialRatchetKdfResponse::from_bytes(
			crate::ratchet::initial_ratchet_hkdf(pending.request()),
		);
		let pending = pending.resume(Some(response)).ok()?;
		let response = crate::ratchet::ratchet_hkdf(pending.request());
		let pending = pending.resume(Some(response)).ok()?;
		let detached = crate::ratchet::execute_seal_request(pending.request());
		let detached_view = detached.as_ref().map(|(body, tag)| (body.as_slice(), *tag));
		let mut pending = pending.resume(detached_view).ok()?;
		let commitment = crate::ratchet::execute_commitment_hash(pending.transcript_mut());
		let pending = pending.resume(commitment).ok()?;
		let ciphertext = crate::ratchet::execute_write_request(pending.request());
		let pending = pending.resume(ciphertext.as_deref()).ok()?;
		let hash = auth::execute_hash(&pending.request());
		let pending = pending.resume(hash).ok()?;
		let signature = self
			.identity
			.mldsa_identity
			.sign_requested(&pending.request());
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
		let pending =
			beaconcrypt_core::peer::begin_peer_insert(control, ready.publish(buffer).ok()?).ok()?;
		let remote_kid = pending.request();
		let (peer, finish) = pending.into_parts();
		let public_key =
			crypto_sign::PublicKey::from_bytes(peer.binding().beacon_identity_public_key()).ok()?;
		let inserted = match self.known_ids.entry(remote_kid) {
			hashbrown::hash_map::Entry::Vacant(entry) => {
				entry.insert(EstablishedRemote::from_peer(public_key, peer));
				true
			}
			hashbrown::hash_map::Entry::Occupied(_) => false,
		};
		let (next_control, remote_kid, buffer) = finish.finish(inserted).ok()?.into_parts();
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
mod row_tests {
	use super::*;

	#[test]
	#[cfg(feature = "beacon")]
	fn restored_row_binding_survives_peer_insertion_collision() {
		use crate::{Beacon, ProviderBeacon};

		#[cfg(target_has_atomic = "ptr")]
		{
			fn assert_send_sync<T: Send + Sync>() {}
			assert_send_sync::<Server>();
		}

		let mut server = Server::new(7, Some(&[11; 32]), Some(&[12; 32]));
		let mut beacon = Beacon::new(
			7,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let registration = beacon.get_registration_bundle().unwrap();
		let pending = server.get_shared_secret(&registration).unwrap();
		let response = server.build_registration_response(pending, None).unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
		let peer = server.take_row_peer(response.kid).unwrap();
		let payload = Zeroizing::new(serde_json::to_vec(&peer).unwrap());
		let restored = server.deserialize_row_peer(response.kid, &payload).unwrap();
		let binding = restored.binding();
		assert_eq!(binding.server_binding(), peer.binding().server_binding());
		assert_eq!(binding.assigned_key_id(), response.kid);
		assert_eq!(
			binding.beacon_identity_public_key(),
			beacon.identity_pk().as_bytes()
		);
		assert_eq!(
			binding.server_fingerprint(),
			peer.binding().server_fingerprint()
		);
		assert_eq!(
			binding.beacon_fingerprint(),
			peer.binding().beacon_fingerprint()
		);
		assert_eq!(
			binding.associated_data(),
			&beacon.associated_data().unwrap()
		);
		let rebound = server
			.deserialize_row_peer(response.kid + 1, &payload)
			.unwrap();
		assert_eq!(rebound.binding().assigned_key_id(), response.kid + 1);

		let mut session = server.row_session(response.kid);
		assert!(session.put_row_peer(response.kid, restored).is_some());
		let mut other_session = server.row_session(response.kid);
		let other_key = crypto_sign::KeyPair::from_seed(&[13; 32]).unwrap();
		other_session.add_known_kid(response.kid, other_key.public_key);
		let replacement = other_session.take_row_peer(response.kid).unwrap();
		assert!(session.put_row_peer(response.kid, replacement).is_none());
		assert_eq!(
			serde_json::to_vec(session.known_ids.get(&response.kid).unwrap()).unwrap(),
			*payload
		);

		let encrypted = session
			.encrypt_message(b"restored row", response.kid)
			.unwrap();
		assert_eq!(
			beacon.decrypt_message(&encrypted).unwrap().plaintext,
			b"restored row"
		);
		let encrypted = beacon.encrypt_message(b"same row binding").unwrap();
		assert_eq!(
			session.decrypt_message(&encrypted).unwrap().plaintext,
			b"same row binding"
		);
	}

	#[test]
	fn row_sessions_retain_identity_without_copying_protocol_state() {
		let mut server = Server::new(7, Some(&[11; 32]), Some(&[12; 32]));
		let peer_key = crypto_sign::KeyPair::from_seed(&[13; 32]).unwrap();
		server.add_known_kid(8, peer_key.public_key.clone());
		server.consumed_registrations.insert([14; 64]);
		server.control = verified_pqxdh::ServerState::new(99);
		let original = server.serialize_state().unwrap();

		let mut session = server.row_session(42);
		assert!(SharedIdentity::ptr_eq(&server.identity, &session.identity));
		assert_eq!(session.server_kid(), 42);
		assert_eq!(session.identity_key_kid(), 7);
		assert!(session.pk_by_kid(8).is_none());
		assert!(session.consumed_registrations.is_empty());
		let peer = server.take_row_peer(8).unwrap();
		assert!(server.take_row_peer(8).is_none());
		assert!(session.put_row_peer(8, peer).is_some());
		assert_eq!(session.pk_by_kid(8), Some(&peer_key.public_key));
		let peer = session.take_row_peer(8).unwrap();
		assert!(server.put_row_peer(8, peer).is_some());
		assert_eq!(server.serialize_state().unwrap(), original);

		let identity = server.serialize_row_identity().unwrap();
		let restored = Server::deserialize_state(&identity).unwrap();
		assert_eq!(restored.identity_key_kid(), 7);
		assert_eq!(restored.server_kid(), 7);
		assert_eq!(restored.identity_pk(), server.identity_pk());
		assert_eq!(
			restored.identity_sk().as_bytes(),
			server.identity_sk().as_bytes()
		);
		assert_eq!(restored.mldsa_public_key(), server.mldsa_public_key());
		assert!(restored.known_ids.is_empty());
		assert!(restored.consumed_registrations.is_empty());
		assert_eq!(restored.serialize_state().unwrap(), identity);
		assert_eq!(server.serialize_state().unwrap(), original);
	}
}

#[cfg(test)]
mod size_tests {
	use super::*;
	use beaconcrypt_parse::MAX_MESSAGE_SIZE;

	#[test]
	#[cfg(feature = "beacon")]
	fn replay_consumption_survives_dropped_or_failed_responses_without_publishing_a_peer() {
		use crate::{Beacon, ProviderBeacon};
		let mut server = Server::new(42, Some(&[7; 32]), Some(&[8; 32]));
		let mut existing = Beacon::new(
			42,
			server.identity_pk().as_bytes(),
			&server.mldsa_public_key(),
		);
		let init = existing.get_registration_bundle().unwrap();
		let pending = server.get_shared_secret(&init).unwrap();
		let response = server.build_registration_response(pending, None).unwrap();
		existing.finish_registration(&response.serialized).unwrap();
		let old_peer = serde_json::to_string(server.known_ids.get(&response.kid).unwrap()).unwrap();
		let counter = server.server_kid();

		let mut requests = Vec::new();
		for _ in 0..3 {
			let mut beacon = Beacon::new(
				42,
				server.identity_pk().as_bytes(),
				&server.mldsa_public_key(),
			);
			requests.push(beacon.get_registration_bundle().unwrap());
		}
		let dropped = server.get_shared_secret(&requests[0]).unwrap();
		drop(dropped);
		let failed = server.get_shared_secret(&requests[1]).unwrap();
		assert!(
			server
				.build_registration_response(failed, Some(b""))
				.is_none()
		);
		assert_eq!(server.server_kid(), counter);
		assert_eq!(server.known_ids.len(), 1);
		assert_eq!(
			serde_json::to_string(server.known_ids.get(&response.kid).unwrap()).unwrap(),
			old_peer
		);
		for request in &requests[..2] {
			assert!(server.get_shared_secret(request).is_none());
		}

		let pending = server.get_shared_secret(&requests[2]).unwrap();
		let new_peer = server
			.build_registration_response(pending, Some(b"new peer"))
			.unwrap();
		assert_eq!(new_peer.kid, counter + 1);
		assert_eq!(server.server_kid(), counter + 1);
		assert_eq!(server.known_ids.len(), 2);
		assert!(server.get_shared_secret(&requests[2]).is_none());
		assert_eq!(
			serde_json::to_string(server.known_ids.get(&response.kid).unwrap()).unwrap(),
			old_peer
		);
		let frame = server
			.encrypt_message(b"existing peer still works", response.kid)
			.unwrap();
		assert_eq!(
			existing.decrypt_message(&frame).unwrap().plaintext,
			b"existing peer still works"
		);
		let restored = Server::deserialize_state(&server.serialize_state().unwrap()).unwrap();
		assert_eq!(restored.server_kid(), counter + 1);
		assert_eq!(
			restored.consumed_registrations,
			server.consumed_registrations
		);
	}

	#[test]
	fn core_application_view_interpreter_preserves_source_selected_bytes() {
		use beaconcrypt_core::transport::{
			RegistrationApplication, normalize_registration_application,
		};
		let omitted = normalize_registration_application(None);
		assert_eq!(registration_application_bytes(&omitted), &[0xff]);
		let empty = [];
		let supplied_empty = normalize_registration_application(Some(&empty));
		assert!(registration_application_bytes(&supplied_empty).is_empty());
		let bytes = [0xff, 0x37, 0];
		let supplied = normalize_registration_application(Some(&bytes));
		assert!(core::ptr::eq(
			registration_application_bytes(&supplied),
			bytes.as_slice()
		));
		let request = RegistrationApplication::Witness([0x37]);
		assert_eq!(registration_application_bytes(&request), &[0x37]);
	}

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
		SharedIdentity::get_mut(&mut server.identity)
			.expect("test identity has no outstanding row session")
			.mldsa_identity = MldsaIdentity::from_seed([9; 32]);
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
