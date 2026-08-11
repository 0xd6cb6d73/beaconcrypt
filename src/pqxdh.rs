// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
use crate::beacon::ProviderBeacon;
#[cfg(feature = "server")]
use crate::server::{RecvState, SendState};
use crate::shared::{
	DhSecret, KEX_KDF_OUT_LEN, KexDerivedSecret, RatchetManager, RemotePrincipal, SYM_RATCHET_INFO,
	SignaturePk,
};
use crate::shared::{decrypt_message_with_ratchet, encrypt_message_with_ratchet};
use crate::{phase1_capnp, phase2_capnp};
#[cfg(feature = "server")]
use crate::{
	server::{ProviderServer, RegResponse, RegistrationOutput},
	shared::{REGISTRATION_WITNESS, deserialize_server_state, serialize_server_state},
};
use beaconcrypt_protocol_core::pqxdh as verified_pqxdh;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{
	crypto_kdf, crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init,
};
#[cfg(feature = "server")]
use std::collections::{HashMap, HashSet};
#[cfg(feature = "server")]
use std::marker::PhantomData;
use std::vec;
use zeroize::Zeroize;

pub const PQXDH_INFO: &[u8; 46] = verified_pqxdh::PQXDH_INFO;
pub const AD_SIZE: usize = verified_pqxdh::ASSOCIATED_DATA_SIZE;

const _: () = assert!(crypto_sign::PUBLICKEYBYTES == verified_pqxdh::SIGN_PUBLIC_KEY_SIZE);
const _: () = assert!(crypto_kx::PUBLICKEYBYTES == verified_pqxdh::X25519_PUBLIC_KEY_SIZE);
const _: () =
	assert!(crypto_kem::mlkem768::PUBLICKEYBYTES == verified_pqxdh::MLKEM768_PUBLIC_KEY_SIZE);
const _: () =
	assert!(crypto_kem::mlkem768::CIPHERTEXTBYTES == verified_pqxdh::MLKEM768_CIPHERTEXT_SIZE);
const _: () =
	assert!(crypto_kem::mlkem768::SHAREDSECRETBYTES == verified_pqxdh::SHARED_SECRET_SIZE);

impl SignaturePk for crypto_sign::PublicKey {}

#[cfg(feature = "beacon")]
enum BeaconState {
	Fresh {
		control: verified_pqxdh::BeaconFresh,
		prekey: crypto_kx::KeyPair,
		pq_key: crypto_kem::mlkem768::KeyPair,
	},
	FreshWithCoins {
		control: verified_pqxdh::BeaconFresh,
		prekey: crypto_kx::KeyPair,
		onetime_key: crypto_kx::KeyPair,
		pq_key: crypto_kem::mlkem768::KeyPair,
	},
	InitSent {
		control: verified_pqxdh::BeaconInitSent,
		prekey: crypto_kx::KeyPair,
		onetime_key: crypto_kx::KeyPair,
		pq_key: crypto_kem::mlkem768::KeyPair,
	},
	Established {
		control: verified_pqxdh::BeaconEstablished,
		associated_data: [u8; AD_SIZE],
	},
	Aborted {
		control: verified_pqxdh::BeaconAborted,
	},
}

#[cfg(feature = "beacon")]
pub struct Beacon {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	state: BeaconState,
	server: RemotePrincipal<crypto_sign::PublicKey>,
}
#[cfg(feature = "server")]
pub struct Server {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	control: verified_pqxdh::ServerState,
	known_ids: HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}
#[cfg(feature = "beacon")]
impl Beacon {
	pub fn new(server_kid: u64, server_id_pk: &[u8]) -> Self {
		ensure_init().expect("Failed to initialize libsodium");
		let id = crypto_sign::PublicKey::from_bytes(server_id_pk).unwrap();
		Self {
			identity_key: crypto_sign::KeyPair::generate().unwrap(),
			identity_key_kid: server_kid,
			state: BeaconState::Fresh {
				control: verified_pqxdh::BeaconFresh::new(verified_pqxdh::ServerBinding {
					identity_public_key: *id.as_bytes(),
					identity_key_id: server_kid,
				}),
				prekey: crypto_kx::KeyPair::generate().unwrap(),
				pq_key: crypto_kem::mlkem768::KeyPair::generate().unwrap(),
			},
			server: RemotePrincipal::new(id, RatchetManager::default()),
		}
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
	pub fn server_id(&self) -> &crypto_sign::PublicKey {
		self.server.pk()
	}
	pub fn server_kid(&self) -> u64 {
		match &self.state {
			BeaconState::Fresh { control, .. } | BeaconState::FreshWithCoins { control, .. } => {
				control.server_key_id()
			}
			BeaconState::InitSent { control, .. } => control.server_key_id(),
			BeaconState::Established { control, .. } => control.server_key_id(),
			BeaconState::Aborted { control } => control.server_key_id(),
		}
	}
	pub fn pq_pk(&self) -> Option<&crypto_kem::mlkem768::PublicKey> {
		match &self.state {
			BeaconState::Fresh { pq_key, .. }
			| BeaconState::FreshWithCoins { pq_key, .. }
			| BeaconState::InitSent { pq_key, .. } => Some(&pq_key.public_key),
			_ => None,
		}
	}
	pub fn pq_sk(&self) -> Option<&crypto_kem::mlkem768::SecretKey> {
		match &self.state {
			BeaconState::Fresh { pq_key, .. }
			| BeaconState::FreshWithCoins { pq_key, .. }
			| BeaconState::InitSent { pq_key, .. } => Some(&pq_key.secret_key),
			_ => None,
		}
	}
	pub fn ratchet_manager(&self) -> &RatchetManager {
		self.server.ratchet()
	}
	pub fn ratchet_manager_mut(&mut self) -> &mut RatchetManager {
		self.server.ratchet_mut()
	}
	pub fn associated_data(&self) -> Option<[u8; AD_SIZE]> {
		match self.state {
			BeaconState::Established {
				associated_data, ..
			} => Some(associated_data),
			_ => None,
		}
	}
	pub fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		if let BeaconState::Established {
			associated_data, ..
		} = &mut self.state
		{
			*associated_data = data
		}
	}
	pub fn encrypt_message(&mut self, b: &[u8]) -> Option<crate::Encrypted> {
		let kid = self.server_kid();
		let sender = self.identity_key_kid;
		let ad = self.associated_data()?;
		encrypt_message_with_ratchet(b, kid, sender, &ad, self.server.ratchet_mut())
	}
	pub fn decrypt_message(&mut self, b: &[u8]) -> Option<crate::Decrypted> {
		let kid = self.server_kid();
		let ad = self.associated_data()?;
		decrypt_message_with_ratchet(b, kid, &ad, self.server.ratchet_mut())
	}

	#[cfg(feature = "beacon")]
	fn abort_registration(&mut self, control: verified_pqxdh::BeaconInitSent) {
		let server_kid = control.server_key_id();
		self.identity_key_kid = server_kid;
		self.server.ratchet_mut().reset();
		self.state = BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_init(control),
		};
	}

	pub fn get_prekey_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.state {
			BeaconState::Fresh { prekey, .. }
			| BeaconState::FreshWithCoins { prekey, .. }
			| BeaconState::InitSent { prekey, .. } => Some(&prekey.public_key),
			_ => None,
		}
	}

	pub fn get_prekey_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.state {
			BeaconState::Fresh { prekey, .. }
			| BeaconState::FreshWithCoins { prekey, .. }
			| BeaconState::InitSent { prekey, .. } => Some(&prekey.secret_key),
			_ => None,
		}
	}

	pub fn get_onetime_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.state {
			BeaconState::FreshWithCoins { onetime_key, .. }
			| BeaconState::InitSent { onetime_key, .. } => Some(&onetime_key.public_key),
			_ => None,
		}
	}

	pub fn get_onetime_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.state {
			BeaconState::FreshWithCoins { onetime_key, .. }
			| BeaconState::InitSent { onetime_key, .. } => Some(&onetime_key.secret_key),
			_ => None,
		}
	}

	/// Pre-generate the explicit one-time registration coins.
	///
	/// This compatibility helper preserves the former public API while keeping
	/// the key in a dedicated fresh phase rather than an unrelated `Option`.
	pub fn new_onetime_keypair(&mut self) -> Option<()> {
		let onetime_key = crypto_kx::KeyPair::generate().ok()?;
		if let BeaconState::FreshWithCoins {
			onetime_key: current,
			..
		} = &mut self.state
		{
			*current = onetime_key;
			return Some(());
		}
		let control = match &self.state {
			BeaconState::Fresh { control, .. } => *control,
			_ => return None,
		};
		let fallback = BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_fresh(control),
		};
		let previous = std::mem::replace(&mut self.state, fallback);
		match previous {
			BeaconState::Fresh { prekey, pq_key, .. } => {
				self.state = BeaconState::FreshWithCoins {
					control,
					prekey,
					onetime_key,
					pq_key,
				};
				Some(())
			}
			other => {
				self.state = other;
				None
			}
		}
	}

	pub fn delete_onetime_keypair(&mut self) {
		let server_kid = self.server_kid();
		let phase = std::mem::replace(
			&mut self.state,
			BeaconState::Aborted {
				control: verified_pqxdh::BeaconAborted::new(server_kid),
			},
		);
		self.state = match phase {
			BeaconState::FreshWithCoins {
				control,
				prekey,
				pq_key,
				..
			} => BeaconState::Fresh {
				control,
				prekey,
				pq_key,
			},
			BeaconState::InitSent { control, .. } => BeaconState::Aborted {
				control: verified_pqxdh::beacon_abort_init(control),
			},
			other => other,
		};
	}

	pub fn delete_pq_keypair(&mut self) {
		let aborted = match &self.state {
			BeaconState::Fresh { control, .. } | BeaconState::FreshWithCoins { control, .. } => {
				Some(verified_pqxdh::beacon_abort_fresh(*control))
			}
			BeaconState::InitSent { control, .. } => {
				Some(verified_pqxdh::beacon_abort_init(*control))
			}
			_ => None,
		};
		if let Some(control) = aborted {
			self.state = BeaconState::Aborted { control };
		}
	}
}
#[cfg(feature = "server")]
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
		let k = crate::shared::encrypted_frame_sender(b)?;
		let ad = self.associated_data(k)?;
		decrypt_message_with_ratchet(b, k, &ad, self.ratchet_manager_mut(k)?)
	}
	pub fn ratchet_recv_until(&mut self, i: &[u8], u: u64, k: u64) -> Option<u64> {
		self.ratchet_manager_mut(k)?.ratchet_recv_until(i, u)
	}
	pub fn recv_key(&self, s: u64, k: u64) -> Option<&crate::shared::KeyMaterial> {
		self.ratchet_manager(k)?.recv_key(s)
	}
	pub fn delete_recv_key(&mut self, s: u64, k: u64) {
		if let Some(r) = self.ratchet_manager_mut(k) {
			r.delete_recv_key(s)
		}
	}
	pub fn complete_recv_key(&mut self, s: u64, k: u64, a: bool) -> bool {
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
#[cfg(feature = "beacon")]
impl ProviderBeacon for Beacon {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>> {
		let mut generated_onetime = if matches!(&self.state, BeaconState::Fresh { .. }) {
			Some(crypto_kx::KeyPair::generate().ok()?)
		} else {
			None
		};
		let (control, prekey_public, pq_public, onetime_public) = match &self.state {
			BeaconState::Fresh {
				control,
				prekey,
				pq_key,
			} => (
				*control,
				prekey.public_key.as_bytes().try_into().ok()?,
				*pq_key.public_key.as_bytes(),
				generated_onetime
					.as_ref()?
					.public_key
					.as_bytes()
					.try_into()
					.ok()?,
			),
			BeaconState::FreshWithCoins {
				control,
				prekey,
				onetime_key,
				pq_key,
			} => (
				*control,
				prekey.public_key.as_bytes().try_into().ok()?,
				*pq_key.public_key.as_bytes(),
				onetime_key.public_key.as_bytes().try_into().ok()?,
			),
			_ => return None,
		};
		let started = verified_pqxdh::beacon_start(
			control,
			verified_pqxdh::BeaconStartInputs {
				identity_public_key: *self.identity_pk().as_bytes(),
				prekey_public_key: prekey_public,
				pq_public_key: pq_public,
			},
			verified_pqxdh::BeaconCoins {
				one_time_public_key: onetime_public,
			},
		);
		let mut msg = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
		let mut bundle = msg.init_root();
		bundle.set_identity_key(started.message.identity_key());
		let prekey_sig = crypto_sign::sign(started.message.prekey(), self.identity_sk()).ok()?;
		bundle.set_pre_key(&prekey_sig);
		let onetime_sig =
			crypto_sign::sign(started.message.one_time_key(), self.identity_sk()).ok()?;
		bundle.set_one_time_key(&onetime_sig);
		let pq_sig = crypto_sign::sign(started.message.pq_key(), self.identity_sk()).ok()?;
		bundle.set_pq_key(&pq_sig);
		let mut buffer = vec![];
		capnp::serialize::write_message(&mut buffer, msg.borrow_inner()).ok()?;

		let fallback = BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_fresh(control),
		};
		let previous = std::mem::replace(&mut self.state, fallback);
		match previous {
			BeaconState::Fresh { prekey, pq_key, .. } => {
				let Some(onetime_key) = generated_onetime.take() else {
					self.state = BeaconState::Fresh {
						control,
						prekey,
						pq_key,
					};
					return None;
				};
				self.state = BeaconState::InitSent {
					control: started.state,
					prekey,
					onetime_key,
					pq_key,
				};
			}
			BeaconState::FreshWithCoins {
				prekey,
				onetime_key,
				pq_key,
				..
			} => {
				self.state = BeaconState::InitSent {
					control: started.state,
					prekey,
					onetime_key,
					pq_key,
				};
			}
			other => {
				self.state = other;
				return None;
			}
		}
		Some(buffer)
	}

	/// Returns the server's intitial message or a single 0xFF byte if the server didn't provide one. A return value of `None` MUST be treated as a protocol failure
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let control = match &self.state {
			BeaconState::InitSent { control, .. } => *control,
			_ => return None,
		};

		let staged = (|| {
			let (prekey_secret, onetime_secret, pq_secret) = match &self.state {
				BeaconState::InitSent {
					prekey,
					onetime_key,
					pq_key,
					..
				} => (
					&prekey.secret_key,
					&onetime_key.secret_key,
					&pq_key.secret_key,
				),
				_ => return None,
			};
			let reader = capnp::serialize_packed::read_message(bytes, ReaderOptions::new()).ok()?;
			let typed_reader = TypedReader::<_, phase2_capnp::kex_response::Owned>::new(reader);
			let response = typed_reader.get().ok()?;
			let kem_ciphertext =
				crypto_kem::mlkem768::Ciphertext::from_bytes(response.get_kem_cipher_text().ok()?)
					.ok()?;
			let ephemeral =
				crypto_kx::PublicKey::from_bytes(response.get_ephemeral_key().ok()?).ok()?;
			let response_server =
				crypto_sign::PublicKey::from_bytes(response.get_identity_key().ok()?).ok()?;
			let server_kex_id = crypto_sign::ed25519_pk_to_curve25519(&response_server).ok()?;
			let beacon_kex_id = crypto_sign::ed25519_sk_to_curve25519(self.identity_sk()).ok()?;
			let kem_shared = crypto_kem::mlkem768::decapsulate(&kem_ciphertext, pq_secret).ok()?;
			let dh1: DhSecret =
				crypto_scalarmult::scalarmult(prekey_secret.as_bytes(), &server_kex_id)
					.ok()?
					.into();
			let dh2: DhSecret = crypto_scalarmult::scalarmult(&beacon_kex_id, ephemeral.as_bytes())
				.ok()?
				.into();
			let dh3: DhSecret =
				crypto_scalarmult::scalarmult(prekey_secret.as_bytes(), ephemeral.as_bytes())
					.ok()?
					.into();
			let dh4: DhSecret =
				crypto_scalarmult::scalarmult(onetime_secret.as_bytes(), ephemeral.as_bytes())
					.ok()?
					.into();
			let mut finish_inputs = verified_pqxdh::BeaconFinishInputs {
				response_server_identity: *response_server.as_bytes(),
				assigned_key_id: response.get_key_id(),
				shared_secrets: shared_secrets(dh1, dh2, dh3, dh4, &kem_shared)?,
			};
			let prepared = verified_pqxdh::beacon_prepare_finish(control, &finish_inputs);
			zeroize_shared_secrets(&mut finish_inputs.shared_secrets);
			let mut candidate = prepared.ok()?;
			let derived_secret = derive_root_key_input(candidate.root_key_input_mut())?;
			let mut ratchet = RatchetManager::default();
			if !ratchet.init_ratchets(
				derived_secret.as_slice(),
				SYM_RATCHET_INFO,
				candidate.ratchet_initialization(),
			) {
				return None;
			}
			let associated_data = *candidate.associated_data();
			let decrypted = decrypt_message_with_ratchet(
				response.get_app_cipher_text().ok()?,
				candidate.server_key_id(),
				&associated_data,
				&mut ratchet,
			)?;
			let authenticated_server_key_id = decrypted.key_id;
			let mut authenticated_plaintext = decrypted.plaintext;
			if authenticated_plaintext.len() <= verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE {
				return None;
			}
			let plaintext =
				authenticated_plaintext.split_off(verified_pqxdh::REGISTRATION_KEY_ID_BINDING_SIZE);
			let binding = authenticated_plaintext.as_slice().try_into().ok()?;
			let authenticated = verified_pqxdh::authenticate_registration_key_id_binding(
				candidate,
				authenticated_server_key_id,
				binding,
			)
			.ok()?;
			Some((authenticated, associated_data, ratchet, plaintext))
		})();

		let Some((authenticated, associated_data, ratchet, plaintext)) = staged else {
			self.abort_registration(control);
			return None;
		};

		let server_binding = authenticated.server_binding();
		let server_kid = server_binding.identity_key_id;
		if self.server_kid() != server_kid {
			self.abort_registration(control);
			return None;
		}
		if self.server.pk().as_bytes() != &server_binding.identity_public_key {
			self.abort_registration(control);
			return None;
		}
		let remote = &mut self.server;
		*remote.ratchet_mut() = ratchet;
		self.identity_key_kid = authenticated.assigned_key_id();
		self.state = BeaconState::Established {
			control: verified_pqxdh::beacon_commit(authenticated),
			associated_data,
		};
		Some(plaintext)
	}
}

#[cfg(feature = "server")]
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
		let mut ratchet = RatchetManager::default();
		if !ratchet.init_ratchets(
			derived_secret.inner().as_slice(),
			SYM_RATCHET_INFO,
			candidate.ratchet_initialization(),
		) {
			return None;
		}
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

fn shared_secrets(
	dh1: DhSecret,
	dh2: DhSecret,
	dh3: DhSecret,
	dh4: DhSecret,
	kem_shared: &crypto_kem::mlkem768::SharedSecret,
) -> Option<verified_pqxdh::PqxdhSharedSecrets> {
	Some(verified_pqxdh::PqxdhSharedSecrets {
		dh1: dh1.as_slice().try_into().ok()?,
		dh2: dh2.as_slice().try_into().ok()?,
		dh3: dh3.as_slice().try_into().ok()?,
		dh4: dh4.as_slice().try_into().ok()?,
		kem_shared_secret: *kem_shared.as_bytes(),
	})
}

fn zeroize_shared_secrets(secrets: &mut verified_pqxdh::PqxdhSharedSecrets) {
	secrets.dh1.zeroize();
	secrets.dh2.zeroize();
	secrets.dh3.zeroize();
	secrets.dh4.zeroize();
	secrets.kem_shared_secret.zeroize();
}

fn derive_root_key_input(input: &mut verified_pqxdh::RootKeyInput) -> Option<KexDerivedSecret> {
	let derived = (|| {
		let prk = crypto_kdf::hkdf::sha512::extract(None, input.as_bytes()).ok()?;
		Some(
			crypto_kdf::hkdf::sha512::expand(KEX_KDF_OUT_LEN, Some(PQXDH_INFO), &prk)
				.ok()?
				.into(),
		)
	})();
	input.as_mut_bytes().zeroize();
	derived
}

#[cfg(feature = "server")]
pub fn build_associated_data(
	server_id: crypto_sign::PublicKey,
	beacon_id: crypto_sign::PublicKey,
) -> [u8; AD_SIZE] {
	verified_pqxdh::build_associated_data(*server_id.as_bytes(), *beacon_id.as_bytes())
}

#[cfg(all(test, feature = "beacon", feature = "server"))]
mod tests {
	use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
	use libsodium_rs::{crypto_kdf, crypto_kem, crypto_kx, crypto_sign};

	use super::{
		AD_SIZE, Beacon, PQXDH_INFO, Server, build_associated_data, derive_root_key_input,
		verified_pqxdh, zeroize_shared_secrets,
	};
	use crate::{
		DH_OUT_LEN, ED25519_SEED_SIZE, KDF_STATE_SIZE, ProviderBeacon, ProviderServer, SignType,
		phase1_capnp,
		shared::{DhSecret, KemType, KexDerivedSecret, SYM_RATCHET_INFO, decode_kem, decode_sign},
	};

	fn register(server: &mut Server, beacon: &mut Beacon) {
		let bundle = beacon.get_registration_bundle().unwrap();
		let output = server.get_shared_secret(&bundle).unwrap();
		let response = server.build_registration_response(output, None).unwrap();
		beacon.finish_registration(&response.serialized).unwrap();
	}

	#[test]
	fn fresh_beacon_has_registration_material_and_server_binding() {
		let server = Server::new(7, None);
		let beacon = Beacon::new(7, server.identity_pk().as_bytes());
		assert_eq!(beacon.identity_key_kid(), 7);
		assert_eq!(beacon.server_id(), server.identity_pk());
		assert!(beacon.get_prekey_pk().is_some());
		assert!(beacon.get_prekey_sk().is_some());
		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_pk().is_some());
		assert!(beacon.pq_sk().is_some());
	}

	#[test]
	fn fresh_server_has_identity_counter_and_no_remotes() {
		let seed = [0x5a; ED25519_SEED_SIZE];
		let expected = crypto_sign::KeyPair::from_seed(&seed).unwrap();
		let server = Server::new(41, Some(&seed));
		assert_eq!(server.identity_pk(), &expected.public_key);
		assert_eq!(server.identity_sk(), &expected.secret_key);
		assert_eq!(server.server_kid(), 41);
		assert!(server.pk_by_kid(42).is_none());
		assert!(server.ratchet_manager(42).is_none());
	}

	#[test]
	fn server_mutators_update_only_server_owned_state() {
		let mut server = Server::new(41, None);
		server.set_identity_kid(17);
		assert_eq!(server.identity_key_kid(), 17);
		assert_eq!(server.new_remote_kid(), Some(42));
		let peer = crypto_sign::KeyPair::generate().unwrap().public_key;
		server.add_known_kid(9, peer.clone());
		assert_eq!(server.pk_by_kid(9), Some(&peer));
		assert_eq!(server.encrypt_message(b"before reset", 9).unwrap().seq, 1);
		server.reset_known_kid(9);
		assert_eq!(server.encrypt_message(b"after reset", 9).unwrap().seq, 1);
		server.delete_known_kid(9);
		assert!(server.pk_by_kid(9).is_none());
	}

	#[test]
	fn beacon_registration_material_follows_state_transitions() {
		let server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		assert!(beacon.get_onetime_pk().is_none());
		beacon.new_onetime_keypair().unwrap();
		assert!(beacon.get_onetime_pk().is_some());
		assert!(beacon.get_onetime_sk().is_some());
		beacon.delete_onetime_keypair();
		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.get_registration_bundle().is_some());
		assert!(beacon.get_onetime_pk().is_some());
		assert!(beacon.get_onetime_sk().is_some());
		assert!(beacon.get_registration_bundle().is_none());
	}

	#[test]
	fn pregenerated_registration_coins_advance_to_init_sent() {
		let server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		beacon.new_onetime_keypair().unwrap();
		let expected = beacon.get_onetime_pk().unwrap().as_bytes().to_vec();
		assert!(beacon.get_onetime_sk().is_some());

		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();
		let signed = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		assert_eq!(signed[0], u8::from(KemType::X25519));
		assert_eq!(signed[1], verified_pqxdh::KEY_ROLE_ONE_TIME);
		assert_eq!(&signed[2..], expected);
		assert_eq!(beacon.get_onetime_pk().unwrap().as_bytes(), expected);
		assert!(beacon.get_onetime_sk().is_some());
		assert!(beacon.get_registration_bundle().is_none());
	}

	#[test]
	fn deleting_pq_keypair_aborts_every_registration_material_phase() {
		fn assert_aborted(beacon: &mut Beacon) {
			assert!(beacon.get_prekey_pk().is_none());
			assert!(beacon.get_prekey_sk().is_none());
			assert!(beacon.get_onetime_pk().is_none());
			assert!(beacon.get_onetime_sk().is_none());
			assert!(beacon.pq_pk().is_none());
			assert!(beacon.pq_sk().is_none());
			assert!(beacon.get_registration_bundle().is_none());
		}

		let server = Server::new(0, None);
		let server_identity = server.identity_pk().as_bytes();

		let mut fresh = Beacon::new(0, server_identity);
		fresh.delete_pq_keypair();
		assert_aborted(&mut fresh);

		let mut fresh_with_coins = Beacon::new(0, server_identity);
		fresh_with_coins.new_onetime_keypair().unwrap();
		fresh_with_coins.delete_pq_keypair();
		assert_aborted(&mut fresh_with_coins);

		let mut init_sent = Beacon::new(0, server_identity);
		assert!(init_sent.get_registration_bundle().is_some());
		init_sent.delete_pq_keypair();
		assert_aborted(&mut init_sent);
	}

	#[test]
	fn deleting_onetime_keypair_after_init_is_terminal() {
		let server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		assert!(beacon.get_registration_bundle().is_some());

		beacon.delete_onetime_keypair();

		assert!(beacon.get_prekey_pk().is_none());
		assert!(beacon.get_prekey_sk().is_none());
		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_pk().is_none());
		assert!(beacon.pq_sk().is_none());
		assert!(beacon.get_registration_bundle().is_none());
	}

	#[test]
	fn successful_registration_discards_registration_secret_keys() {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());

		register(&mut server, &mut beacon);

		assert!(beacon.get_prekey_pk().is_none());
		assert!(beacon.get_prekey_sk().is_none());
		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_onetime_sk().is_none());
		assert!(beacon.pq_pk().is_none());
		assert!(beacon.pq_sk().is_none());
	}

	#[test]
	fn server_receive_ratchet_delegations_preserve_one_use_semantics() {
		let mut server = Server::new(0, None);
		let peer = crypto_sign::KeyPair::generate().unwrap().public_key;
		server.add_known_kid(9, peer);

		assert_eq!(server.ratchet_recv_until(SYM_RATCHET_INFO, 2, 9), Some(2));
		assert!(server.recv_key(1, 9).is_some());
		assert!(server.recv_key(2, 9).is_some());
		assert!(server.complete_recv_key(1, 9, false));
		assert!(server.recv_key(1, 9).is_some());
		assert!(server.complete_recv_key(1, 9, true));
		assert!(server.recv_key(1, 9).is_none());
		assert!(!server.complete_recv_key(1, 9, true));
		server.delete_recv_key(2, 9);
		assert!(server.recv_key(2, 9).is_none());

		assert!(server.encrypt_message(b"unknown peer", 99).is_none());
		assert_eq!(server.ratchet_recv_until(SYM_RATCHET_INFO, 1, 99), None);
		assert!(server.recv_key(1, 99).is_none());
		assert!(!server.complete_recv_key(1, 99, true));
	}

	#[test]
	fn established_beacon_replaces_singular_associated_data() {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		register(&mut server, &mut beacon);
		let replacement = [0xa5; AD_SIZE];
		beacon.set_associated_data(replacement);
		assert_eq!(beacon.associated_data(), Some(replacement));
	}

	#[test]
	fn beacon_and_server_ratchets_advance_through_role_specific_accessors() {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		register(&mut server, &mut beacon);
		let beacon_kid = beacon.identity_key_kid();
		let encrypted = server.encrypt_message(b"ratchet", beacon_kid).unwrap();
		assert_eq!(encrypted.seq, 2);
		assert_eq!(
			beacon.decrypt_message(&encrypted).unwrap().plaintext,
			b"ratchet"
		);
		assert_eq!(
			server
				.ratchet_manager(beacon_kid)
				.unwrap()
				.send_state()
				.as_slice(),
			beacon.ratchet_manager().recv_state().as_slice()
		);
	}

	#[test]
	fn registration_bundle_authenticates_each_declared_public_key() {
		let server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();

		let identity = registration.get_identity_key().unwrap();
		assert_eq!(identity[0], u8::from(SignType::Ed25519));
		assert_eq!(
			decode_sign(identity, SignType::Ed25519).unwrap(),
			beacon.identity_pk().as_bytes()
		);

		let prekey =
			crypto_sign::verify(registration.get_pre_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(prekey[0], u8::from(KemType::X25519));
		assert_eq!(prekey[1], verified_pqxdh::KEY_ROLE_PREKEY);
		assert_eq!(&prekey[2..], beacon.get_prekey_pk().unwrap().as_bytes());

		let onetime = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		assert_eq!(onetime[0], u8::from(KemType::X25519));
		assert_eq!(onetime[1], verified_pqxdh::KEY_ROLE_ONE_TIME);
		assert_eq!(&onetime[2..], beacon.get_onetime_pk().unwrap().as_bytes());

		let pq =
			crypto_sign::verify(registration.get_pq_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(pq[0], u8::from(KemType::MlKem768));
		assert_eq!(
			decode_kem(&pq, KemType::MlKem768).unwrap(),
			beacon.pq_pk().unwrap().as_bytes()
		);
	}

	#[test]
	fn server_rejects_tampering_of_each_signed_registration_key() {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
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

		assert!(server.get_shared_secret(&serialized).is_some());
	}

	#[test]
	fn server_rejects_swapped_or_duplicated_signed_x25519_roles() {
		let server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();
		let identity = registration.get_identity_key().unwrap().to_vec();
		let prekey = registration.get_pre_key().unwrap().to_vec();
		let onetime = registration.get_one_time_key().unwrap().to_vec();
		let pq = registration.get_pq_key().unwrap().to_vec();

		for duplicate_prekey in [false, true] {
			let mut tampered = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
			let mut root = tampered.init_root();
			root.set_identity_key(&identity);
			root.set_pre_key(if duplicate_prekey { &prekey } else { &onetime });
			root.set_one_time_key(&prekey);
			root.set_pq_key(&pq);
			let mut tampered_serialized = vec![];
			capnp::serialize::write_message(&mut tampered_serialized, tampered.borrow_inner())
				.unwrap();

			let mut server = Server::new(0, None);
			assert!(
				server.get_shared_secret(&tampered_serialized).is_none(),
				"server accepted {} signed X25519 roles",
				if duplicate_prekey {
					"duplicated"
				} else {
					"swapped"
				}
			);
		}

		let mut server = Server::new(0, None);
		assert!(server.get_shared_secret(&serialized).is_some());
	}

	#[test]
	fn server_rejects_signed_registration_keys_with_wrong_type_prefixes() {
		let mut server = Server::new(0, None);
		let mut beacon = Beacon::new(0, server.identity_pk().as_bytes());
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

		assert!(server.get_shared_secret(&serialized).is_some());
	}

	#[test]
	fn root_key_derivation_matches_the_pqxdh_transcript() {
		let dh1 = DhSecret::from([0x11; DH_OUT_LEN]);
		let dh2 = DhSecret::from([0x22; DH_OUT_LEN]);
		let dh3 = DhSecret::from([0x33; DH_OUT_LEN]);
		let dh4 = DhSecret::from([0x44; DH_OUT_LEN]);
		let shared_bytes = [0x55; crypto_kem::mlkem768::SHAREDSECRETBYTES];
		let secrets = verified_pqxdh::PqxdhSharedSecrets {
			dh1: dh1.as_slice().try_into().unwrap(),
			dh2: dh2.as_slice().try_into().unwrap(),
			dh3: dh3.as_slice().try_into().unwrap(),
			dh4: dh4.as_slice().try_into().unwrap(),
			kem_shared_secret: shared_bytes,
		};
		let mut transcript = verified_pqxdh::build_root_key_input(&secrets).unwrap();
		let actual = derive_root_key_input(&mut transcript).unwrap();
		let mut ikm = vec![0xff; crypto_kx::PUBLICKEYBYTES];
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
		assert_eq!(actual.as_slice(), known_answer);
	}

	#[test]
	fn root_key_transcript_and_shared_secrets_are_zeroized() {
		let mut secrets = verified_pqxdh::PqxdhSharedSecrets {
			dh1: [0x11; DH_OUT_LEN],
			dh2: [0x22; DH_OUT_LEN],
			dh3: [0x33; DH_OUT_LEN],
			dh4: [0x44; DH_OUT_LEN],
			kem_shared_secret: [0x55; crypto_kem::mlkem768::SHAREDSECRETBYTES],
		};
		let mut input = verified_pqxdh::build_root_key_input(&secrets).unwrap();
		assert!(derive_root_key_input(&mut input).is_some());
		assert_eq!(input.as_bytes(), &[0; verified_pqxdh::ROOT_KEY_INPUT_SIZE]);
		zeroize_shared_secrets(&mut secrets);
		assert_eq!(secrets.dh1, [0; DH_OUT_LEN]);
		assert_eq!(secrets.dh2, [0; DH_OUT_LEN]);
		assert_eq!(secrets.dh3, [0; DH_OUT_LEN]);
		assert_eq!(secrets.dh4, [0; DH_OUT_LEN]);
		assert_eq!(
			secrets.kem_shared_secret,
			[0; crypto_kem::mlkem768::SHAREDSECRETBYTES]
		);
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
	}
}
