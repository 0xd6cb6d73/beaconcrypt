// SPDX-License-Identifier: 0BSD

#[cfg(feature = "beacon")]
use crate::beacon::ProviderBeacon;
#[cfg(feature = "server")]
use crate::server::{RecvState, SendState};
#[cfg(feature = "beacon")]
use crate::shared::decrypt_message_with_ratchet;
#[cfg(feature = "server")]
use crate::shared::encrypt_message_with_ratchet;
use crate::shared::{
	DhSecret, ED25519_SEED_SIZE, KEX_KDF_OUT_LEN, KexDerivedSecret, RatchetManager,
	RemotePrincipal, SYM_RATCHET_INFO, SignaturePk,
};
use crate::{CryptoProvider, phase1_capnp, phase2_capnp};
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

#[cfg_attr(not(feature = "beacon"), allow(dead_code))]
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

// Beacon registration deliberately keeps its secret-bearing key material
// inline with the provider. Boxing only the large role would add a separate
// allocation and make its memory lifecycle differ from the other live state.
#[allow(clippy::large_enum_variant)]
enum ProviderRole {
	Beacon(BeaconState),
	Server(verified_pqxdh::ServerState),
}

pub struct BeaconCryptPqxdh {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	role: ProviderRole,
	// Stores the server key ID for a beacon and the last allocated remote ID for a server.
	server_kid: u64,
	known_ids: HashMap<u64, RemotePrincipal<crypto_sign::PublicKey>>,
	#[cfg_attr(not(feature = "server"), allow(dead_code))]
	consumed_registrations: HashSet<[u8; verified_pqxdh::REGISTRATION_ID_SIZE]>,
}

impl CryptoProvider for BeaconCryptPqxdh {
	type SignaturePublicKey = crypto_sign::PublicKey;
	type SignatureSecretKey = crypto_sign::SecretKey;
	type KemPublicKey = crypto_kem::mlkem768::PublicKey;
	type KemSecretKey = crypto_kem::mlkem768::SecretKey;

	fn default() -> Self {
		Self {
			identity_key: crypto_sign::KeyPair::from_seed(&[0u8; ED25519_SEED_SIZE]).unwrap(),
			identity_key_kid: 0,
			role: ProviderRole::Beacon(BeaconState::Aborted {
				control: verified_pqxdh::BeaconAborted::new(0),
			}),
			server_kid: 0,
			known_ids: HashMap::new(),
			consumed_registrations: HashSet::new(),
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
		let configured_server = if is_beacon {
			server_id_pk.map(|pk| crypto_sign::PublicKey::from_bytes(pk).unwrap())
		} else {
			None
		};
		let mut known_ids = HashMap::new();
		if let Some(server_identity) = &configured_server {
			known_ids.insert(
				server_kid,
				RemotePrincipal::new(server_identity.clone(), RatchetManager::default()),
			);
		}

		let role = if is_beacon {
			if let Some(server_identity) = configured_server {
				ProviderRole::Beacon(BeaconState::Fresh {
					control: verified_pqxdh::BeaconFresh::new(verified_pqxdh::ServerBinding {
						identity_public_key: *server_identity.as_bytes(),
						identity_key_id: server_kid,
					}),
					prekey: crypto_kx::KeyPair::generate().unwrap(),
					pq_key: crypto_kem::mlkem768::KeyPair::generate().unwrap(),
				})
			} else {
				ProviderRole::Beacon(BeaconState::Aborted {
					control: verified_pqxdh::BeaconAborted::new(server_kid),
				})
			}
		} else {
			ProviderRole::Server(verified_pqxdh::ServerState::new(server_kid))
		};

		Self {
			identity_key: id_keypair,
			identity_key_kid: server_kid,
			role,
			server_kid,
			known_ids,
			consumed_registrations: HashSet::new(),
		}
	}

	fn is_beacon(&self) -> bool {
		matches!(&self.role, ProviderRole::Beacon(_))
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
			.or_insert(RemotePrincipal::new(pk, RatchetManager::default()));
	}

	fn delete_known_kid(&mut self, key_id: u64) {
		self.known_ids.remove(&key_id);
	}

	fn reset_known_kid(&mut self, key_id: u64) {
		if let Some(to_reset) = self.ratchet_manager_mut(key_id) {
			to_reset.reset()
		}
	}

	fn new_remote_kid(&mut self) -> Option<u64> {
		let ProviderRole::Server(control) = &mut self.role else {
			return Some(self.server_kid);
		};
		let next = verified_pqxdh::server_next_key_id(*control).ok()?;
		if self.known_ids.contains_key(&next) {
			return None;
		}
		self.server_kid = next;
		*control = verified_pqxdh::ServerState::new(next);
		Some(next)
	}

	fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		if let ProviderRole::Beacon(BeaconState::Established {
			associated_data, ..
		}) = &mut self.role
		{
			*associated_data = data;
		}
	}

	fn associated_data(&self, kid: u64) -> Option<[u8; AD_SIZE]> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::Established {
				associated_data, ..
			}) => Some(*associated_data),
			ProviderRole::Beacon(_) => None,
			ProviderRole::Server(_) => {
				let k = self.pk_by_kid(kid)?;
				Some(build_associated_data(self.identity_pk().clone(), k.clone()))
			}
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
		match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { control, .. }) => control.server_key_id(),
			ProviderRole::Beacon(BeaconState::FreshWithCoins { control, .. }) => {
				control.server_key_id()
			}
			ProviderRole::Beacon(BeaconState::InitSent { control, .. }) => control.server_key_id(),
			ProviderRole::Beacon(BeaconState::Established { control, .. }) => {
				control.server_key_id()
			}
			ProviderRole::Beacon(BeaconState::Aborted { control }) => control.server_key_id(),
			ProviderRole::Server(_) => self.server_kid,
		}
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
		match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { pq_key, .. })
			| ProviderRole::Beacon(BeaconState::FreshWithCoins { pq_key, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { pq_key, .. }) => Some(&pq_key.public_key),
			_ => None,
		}
	}

	fn pq_sk(&self) -> Option<&crypto_kem::mlkem768::SecretKey> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { pq_key, .. })
			| ProviderRole::Beacon(BeaconState::FreshWithCoins { pq_key, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { pq_key, .. }) => Some(&pq_key.secret_key),
			_ => None,
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
	#[cfg(feature = "beacon")]
	fn abort_registration(&mut self, control: verified_pqxdh::BeaconInitSent) {
		let server_kid = control.server_key_id();
		self.identity_key_kid = server_kid;
		if let Some(remote) = self.known_ids.get_mut(&server_kid) {
			remote.ratchet_mut().reset();
		}
		self.role = ProviderRole::Beacon(BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_init(control),
		});
	}

	pub fn get_prekey_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { prekey, .. })
			| ProviderRole::Beacon(BeaconState::FreshWithCoins { prekey, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { prekey, .. }) => Some(&prekey.public_key),
			_ => None,
		}
	}

	pub fn get_prekey_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { prekey, .. })
			| ProviderRole::Beacon(BeaconState::FreshWithCoins { prekey, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { prekey, .. }) => Some(&prekey.secret_key),
			_ => None,
		}
	}

	pub fn get_onetime_pk(&self) -> Option<&crypto_kx::PublicKey> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::FreshWithCoins { onetime_key, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { onetime_key, .. }) => {
				Some(&onetime_key.public_key)
			}
			_ => None,
		}
	}

	pub fn get_onetime_sk(&self) -> Option<&crypto_kx::SecretKey> {
		match &self.role {
			ProviderRole::Beacon(BeaconState::FreshWithCoins { onetime_key, .. })
			| ProviderRole::Beacon(BeaconState::InitSent { onetime_key, .. }) => {
				Some(&onetime_key.secret_key)
			}
			_ => None,
		}
	}

	/// Pre-generate the explicit one-time registration coins.
	///
	/// This compatibility helper preserves the former public API while keeping
	/// the key in a dedicated fresh phase rather than an unrelated `Option`.
	pub fn new_onetime_keypair(&mut self) -> Option<()> {
		let onetime_key = crypto_kx::KeyPair::generate().ok()?;
		if let ProviderRole::Beacon(BeaconState::FreshWithCoins {
			onetime_key: current,
			..
		}) = &mut self.role
		{
			*current = onetime_key;
			return Some(());
		}
		let control = match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { control, .. }) => *control,
			_ => return None,
		};
		let fallback = ProviderRole::Beacon(BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_fresh(control),
		});
		let previous = std::mem::replace(&mut self.role, fallback);
		match previous {
			ProviderRole::Beacon(BeaconState::Fresh { prekey, pq_key, .. }) => {
				self.role = ProviderRole::Beacon(BeaconState::FreshWithCoins {
					control,
					prekey,
					onetime_key,
					pq_key,
				});
				Some(())
			}
			other => {
				self.role = other;
				None
			}
		}
	}

	pub fn delete_onetime_keypair(&mut self) {
		let phase = std::mem::replace(
			&mut self.role,
			ProviderRole::Beacon(BeaconState::Aborted {
				control: verified_pqxdh::BeaconAborted::new(self.server_kid),
			}),
		);
		self.role = match phase {
			ProviderRole::Beacon(BeaconState::FreshWithCoins {
				control,
				prekey,
				pq_key,
				..
			}) => ProviderRole::Beacon(BeaconState::Fresh {
				control,
				prekey,
				pq_key,
			}),
			ProviderRole::Beacon(BeaconState::InitSent { control, .. }) => {
				ProviderRole::Beacon(BeaconState::Aborted {
					control: verified_pqxdh::beacon_abort_init(control),
				})
			}
			other => other,
		};
	}

	pub fn delete_pq_keypair(&mut self) {
		let aborted = match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh { control, .. })
			| ProviderRole::Beacon(BeaconState::FreshWithCoins { control, .. }) => {
				Some(verified_pqxdh::beacon_abort_fresh(*control))
			}
			ProviderRole::Beacon(BeaconState::InitSent { control, .. }) => {
				Some(verified_pqxdh::beacon_abort_init(*control))
			}
			_ => None,
		};
		if let Some(control) = aborted {
			self.role = ProviderRole::Beacon(BeaconState::Aborted { control });
		}
	}
}

#[cfg(feature = "beacon")]
impl ProviderBeacon for BeaconCryptPqxdh {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>> {
		let mut generated_onetime =
			if matches!(&self.role, ProviderRole::Beacon(BeaconState::Fresh { .. })) {
				Some(crypto_kx::KeyPair::generate().ok()?)
			} else {
				None
			};
		let (control, prekey_public, pq_public, onetime_public) = match &self.role {
			ProviderRole::Beacon(BeaconState::Fresh {
				control,
				prekey,
				pq_key,
			}) => (
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
			ProviderRole::Beacon(BeaconState::FreshWithCoins {
				control,
				prekey,
				onetime_key,
				pq_key,
			}) => (
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

		let fallback = ProviderRole::Beacon(BeaconState::Aborted {
			control: verified_pqxdh::beacon_abort_fresh(control),
		});
		let previous = std::mem::replace(&mut self.role, fallback);
		match previous {
			ProviderRole::Beacon(BeaconState::Fresh { prekey, pq_key, .. }) => {
				let Some(onetime_key) = generated_onetime.take() else {
					self.role = ProviderRole::Beacon(BeaconState::Fresh {
						control,
						prekey,
						pq_key,
					});
					return None;
				};
				self.role = ProviderRole::Beacon(BeaconState::InitSent {
					control: started.state,
					prekey,
					onetime_key,
					pq_key,
				});
			}
			ProviderRole::Beacon(BeaconState::FreshWithCoins {
				prekey,
				onetime_key,
				pq_key,
				..
			}) => {
				self.role = ProviderRole::Beacon(BeaconState::InitSent {
					control: started.state,
					prekey,
					onetime_key,
					pq_key,
				});
			}
			other => {
				self.role = other;
				return None;
			}
		}
		Some(buffer)
	}

	/// Returns the server's intitial message or a single 0xFF byte if the server didn't provide one. A return value of `None` MUST be treated as a protocol failure
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		let control = match &self.role {
			ProviderRole::Beacon(BeaconState::InitSent { control, .. }) => *control,
			_ => return None,
		};

		let staged = (|| {
			let (prekey_secret, onetime_secret, pq_secret) = match &self.role {
				ProviderRole::Beacon(BeaconState::InitSent {
					prekey,
					onetime_key,
					pq_key,
					..
				}) => (
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
		if !self
			.known_ids
			.get(&server_kid)
			.is_some_and(|remote| remote.pk().as_bytes() == &server_binding.identity_public_key)
		{
			self.abort_registration(control);
			return None;
		}
		let Some(remote) = self.known_ids.get_mut(&server_kid) else {
			self.abort_registration(control);
			return None;
		};
		*remote.ratchet_mut() = ratchet;
		self.identity_key_kid = authenticated.assigned_key_id();
		self.role = ProviderRole::Beacon(BeaconState::Established {
			control: verified_pqxdh::beacon_commit(authenticated),
			associated_data,
		});
		Some(plaintext)
	}
}

#[cfg(feature = "server")]
impl ProviderServer for BeaconCryptPqxdh {
	fn get_shared_secret(&mut self, buffer: &[u8]) -> Option<RegistrationOutput> {
		let control = match self.role {
			ProviderRole::Server(control) => control,
			ProviderRole::Beacon(_) => return None,
		};
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
		let control = match self.role {
			ProviderRole::Server(control) => control,
			ProviderRole::Beacon(_) => return None,
		};
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
		self.server_kid = next_control.last_key_id();
		self.role = ProviderRole::Server(next_control);
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
			self.server_kid,
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
			role: ProviderRole::Server(verified_pqxdh::ServerState::new(server_kid)),
			server_kid,
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

#[cfg(test)]
pub fn derive_root_key(
	dh1: DhSecret,
	dh2: DhSecret,
	dh3: DhSecret,
	dh4: DhSecret,
	shared_secret: crypto_kem::mlkem768::SharedSecret,
) -> Option<KexDerivedSecret> {
	let mut secrets = shared_secrets(dh1, dh2, dh3, dh4, &shared_secret)?;
	let input = verified_pqxdh::build_root_key_input(&secrets);
	zeroize_shared_secrets(&mut secrets);
	let mut input = input.ok()?;
	derive_root_key_input(&mut input)
}

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
		AD_SIZE, PQXDH_INFO, build_associated_data, derive_root_key, derive_root_key_input,
		verified_pqxdh, zeroize_shared_secrets,
	};
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

	fn unregistered_test_beacon() -> BeaconCryptPqxdh {
		BeaconCryptPqxdh::new(true, 0, Some(&[0; crypto_sign::PUBLICKEYBYTES]), None)
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

		let dec_b1_m2 = b1.decrypt_message(&b1_m2.ciphertext).unwrap();
		let dec_b1_m1 = b1.decrypt_message(&b1_m1.ciphertext).unwrap();
		assert_eq!(dec_b1_m1.plaintext, dec_b1_m2.plaintext);
		assert_eq!(dec_b1_m1.key_id, dec_b1_m2.key_id);
	}

	#[test]
	fn beacon_deletes_registration_keys_after_registration() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();

		// The beacon doesn't generate its one-time key until it generates its registration bundle.
		let mut b1 = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		assert!(b1.get_onetime_pk().is_none());
		assert!(b1.get_onetime_sk().is_none());
		assert!(b1.pq_pk().is_some());
		assert!(b1.pq_sk().is_some());
		let _ = test_register_beacon(&mut server, &mut b1);
		assert!(b1.get_prekey_pk().is_none());
		assert!(b1.get_prekey_sk().is_none());
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
	fn pre_generated_onetime_key_is_the_one_in_the_registration_bundle() {
		let mut beacon = unregistered_test_beacon();
		beacon.new_onetime_keypair().unwrap();
		let expected = beacon.get_onetime_pk().unwrap().as_bytes().to_vec();

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
	}

	#[test]
	fn deleting_pre_generated_onetime_key_returns_to_fresh() {
		let mut beacon = unregistered_test_beacon();
		beacon.new_onetime_keypair().unwrap();
		assert!(beacon.get_onetime_pk().is_some());

		beacon.delete_onetime_keypair();

		assert!(beacon.get_onetime_pk().is_none());
		assert!(beacon.get_registration_bundle().is_some());
		assert!(beacon.get_registration_bundle().is_none());
	}

	#[test]
	fn deleting_registration_material_after_init_is_terminal() {
		let mut deletes_onetime = unregistered_test_beacon();
		assert!(deletes_onetime.get_registration_bundle().is_some());
		deletes_onetime.delete_onetime_keypair();
		assert!(deletes_onetime.get_prekey_pk().is_none());
		assert!(deletes_onetime.get_onetime_pk().is_none());
		assert!(deletes_onetime.pq_pk().is_none());
		assert!(deletes_onetime.get_registration_bundle().is_none());

		let mut deletes_pq = unregistered_test_beacon();
		deletes_pq.delete_pq_keypair();
		assert!(deletes_pq.get_prekey_pk().is_none());
		assert!(deletes_pq.get_onetime_pk().is_none());
		assert!(deletes_pq.pq_pk().is_none());
		assert!(deletes_pq.get_registration_bundle().is_none());

		let mut deletes_pq_after_init = unregistered_test_beacon();
		assert!(deletes_pq_after_init.get_registration_bundle().is_some());
		deletes_pq_after_init.delete_pq_keypair();
		assert!(deletes_pq_after_init.get_prekey_pk().is_none());
		assert!(deletes_pq_after_init.get_onetime_pk().is_none());
		assert!(deletes_pq_after_init.pq_pk().is_none());
		assert!(deletes_pq_after_init.get_registration_bundle().is_none());
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
	fn provider_control_mutators_update_observable_state() {
		let mut provider = BeaconCryptPqxdh::new(false, 41, None, None);
		provider.set_identity_kid(17);
		assert_eq!(provider.identity_key_kid(), 17);
		assert_eq!(provider.new_remote_kid(), Some(42));
		assert_eq!(provider.server_kid(), 42);

		let peer = crypto_sign::KeyPair::generate().unwrap().public_key;
		provider.add_known_kid(9, peer);
		assert_eq!(provider.encrypt_message(b"before reset", 9).unwrap().seq, 1);
		provider.reset_known_kid(9);
		assert_eq!(provider.encrypt_message(b"after reset", 9).unwrap().seq, 1);

		let server = crypto_sign::KeyPair::generate().unwrap().public_key;
		provider.add_server_pk(server.clone());
		assert_eq!(provider.pk_by_kid(42), Some(&server));
	}

	#[test]
	fn provider_receive_ratchet_delegations_preserve_one_use_semantics() {
		let mut provider = BeaconCryptPqxdh::new(false, 0, None, None);
		let peer = crypto_sign::KeyPair::generate().unwrap().public_key;
		provider.add_known_kid(9, peer);

		assert_eq!(provider.ratchet_recv_until(SYM_RATCHET_INFO, 2, 9), Some(2));
		assert!(provider.recv_key(1, 9).is_some());
		assert!(provider.recv_key(2, 9).is_some());
		assert!(provider.complete_recv_key(1, 9, false));
		assert!(provider.recv_key(1, 9).is_some());
		assert!(provider.complete_recv_key(1, 9, true));
		assert!(provider.recv_key(1, 9).is_none());
		assert!(!provider.complete_recv_key(1, 9, true));
		provider.delete_recv_key(2, 9);
		assert!(provider.recv_key(2, 9).is_none());

		assert!(provider.encrypt_message(b"unknown peer", 99).is_none());
		assert_eq!(provider.ratchet_recv_until(SYM_RATCHET_INFO, 1, 99), None);
		assert!(provider.recv_key(1, 99).is_none());
		assert!(!provider.complete_recv_key(1, 99, true));
	}

	#[test]
	fn established_beacon_associated_data_can_be_replaced() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let server_id = server.identity_pk().to_owned();
		let mut beacon = BeaconCryptPqxdh::new(true, 0, Some(server_id.as_bytes()), None);
		test_register_beacon(&mut server, &mut beacon);
		let replacement = [0xA5; AD_SIZE];

		beacon.set_associated_data(replacement);

		assert_eq!(beacon.associated_data(0), Some(replacement));
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
		let mut beacon = unregistered_test_beacon();
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
		assert_eq!(prekey[0], 4);
		assert_eq!(prekey[1], verified_pqxdh::KEY_ROLE_PREKEY);
		assert_eq!(&prekey[2..], beacon.get_prekey_pk().unwrap().as_bytes());

		let onetime = crypto_sign::verify(
			registration.get_one_time_key().unwrap(),
			beacon.identity_pk(),
		)
		.unwrap();
		assert_eq!(onetime[0], 4);
		assert_eq!(onetime[1], verified_pqxdh::KEY_ROLE_ONE_TIME);
		assert_eq!(&onetime[2..], beacon.get_onetime_pk().unwrap().as_bytes());

		let pq =
			crypto_sign::verify(registration.get_pq_key().unwrap(), beacon.identity_pk()).unwrap();
		assert_eq!(pq[0], 3);
		assert_eq!(
			decode_kem(&pq, KemType::MlKem768).unwrap(),
			beacon.pq_pk().unwrap().as_bytes()
		);
	}

	#[test]
	fn server_rejects_a_registration_with_a_tampered_signed_key() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = unregistered_test_beacon();
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
	fn server_rejects_swapped_or_duplicated_signed_x25519_roles() {
		let mut beacon = unregistered_test_beacon();
		let serialized = beacon.get_registration_bundle().unwrap();
		let message =
			capnp::serialize::read_message(&serialized[..], ReaderOptions::new()).unwrap();
		let typed = TypedReader::<_, phase1_capnp::init_kex::Owned>::new(message);
		let registration = typed.get().unwrap();
		let identity = registration.get_identity_key().unwrap().to_vec();
		let prekey = registration.get_pre_key().unwrap().to_vec();
		let one_time = registration.get_one_time_key().unwrap().to_vec();
		let pq = registration.get_pq_key().unwrap().to_vec();

		for duplicate_prekey in [false, true] {
			let mut tampered = TypedBuilder::<phase1_capnp::init_kex::Owned>::new_default();
			let mut root = tampered.init_root();
			root.set_identity_key(&identity);
			root.set_pre_key(if duplicate_prekey { &prekey } else { &one_time });
			root.set_one_time_key(&prekey);
			root.set_pq_key(&pq);
			let mut tampered_serialized = vec![];
			capnp::serialize::write_message(&mut tampered_serialized, tampered.borrow_inner())
				.unwrap();

			let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
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

		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		assert!(server.get_shared_secret(&serialized).is_some());
	}

	#[test]
	fn server_rejects_tampering_of_each_signed_registration_key() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = unregistered_test_beacon();
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
	fn server_rejects_signed_registration_keys_with_wrong_type_prefixes() {
		let mut server = BeaconCryptPqxdh::new(false, 0, None, None);
		let mut beacon = unregistered_test_beacon();
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
		// Reproduced independently by `python scripts/generate_kat_vectors.py` and
		// `go run scripts/generate_kat_vectors.go` (`[pqxdh-root-key]`).
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
	fn root_key_transcript_is_zeroized_after_the_opaque_kdf_call() {
		let secrets = verified_pqxdh::PqxdhSharedSecrets {
			dh1: [0x11; DH_OUT_LEN],
			dh2: [0x22; DH_OUT_LEN],
			dh3: [0x33; DH_OUT_LEN],
			dh4: [0x44; DH_OUT_LEN],
			kem_shared_secret: [0x55; crypto_kem::mlkem768::SHAREDSECRETBYTES],
		};
		let mut input = verified_pqxdh::build_root_key_input(&secrets).unwrap();

		assert!(derive_root_key_input(&mut input).is_some());
		assert_eq!(input.as_bytes(), &[0; verified_pqxdh::ROOT_KEY_INPUT_SIZE]);
	}

	#[test]
	fn shared_secret_components_are_zeroized_after_transcript_construction() {
		let mut secrets = verified_pqxdh::PqxdhSharedSecrets {
			dh1: [0x11; DH_OUT_LEN],
			dh2: [0x22; DH_OUT_LEN],
			dh3: [0x33; DH_OUT_LEN],
			dh4: [0x44; DH_OUT_LEN],
			kem_shared_secret: [0x55; crypto_kem::mlkem768::SHAREDSECRETBYTES],
		};

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
		assert_ne!(
			actual,
			build_associated_data(beacon.public_key, server.public_key),
		);
	}
}
