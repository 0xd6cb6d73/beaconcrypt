// SPDX-License-Identifier: 0BSD

use crate::pqxdh::{AD_SIZE, derive_root_key_input, shared_secrets, zeroize_shared_secrets};
use crate::ratchet::{
	RatchetManager, RatchetStatus, decrypt_message_with_ratchet, encrypt_message_with_ratchet,
	initial_ratchet_hkdf, ratchet_hkdf,
};
use crate::shared::DhSecret;
use crate::{phase1_capnp, phase2_capnp};
use beaconcrypt_core::pqxdh as verified_pqxdh;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::{crypto_kem, crypto_kx, crypto_scalarmult, crypto_sign, ensure_init};
use std::vec;

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
		ratchet: RatchetManager,
	},
	Aborted {
		control: verified_pqxdh::BeaconAborted,
	},
}

/// Opaque beacon handle exposed by the C API and owned by its caller.
pub struct Beacon {
	identity_key: crypto_sign::KeyPair,
	identity_key_kid: u64,
	state: BeaconState,
	server_id: crypto_sign::PublicKey,
}

pub trait ProviderBeacon {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}

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
			server_id: id,
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
		&self.server_id
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
	#[cfg(test)]
	pub(crate) fn ratchet_manager(&self) -> Option<&RatchetManager> {
		match &self.state {
			BeaconState::Established { ratchet, .. } => Some(ratchet),
			_ => None,
		}
	}
	pub fn associated_data(&self) -> Option<[u8; AD_SIZE]> {
		match self.state {
			BeaconState::Established {
				associated_data, ..
			} => Some(associated_data),
			_ => None,
		}
	}
	pub fn ratchet_status(&self) -> Option<RatchetStatus> {
		match &self.state {
			BeaconState::Established { ratchet, .. } => Some(ratchet.status()),
			_ => None,
		}
	}
	#[cfg(test)]
	pub(crate) fn set_associated_data(&mut self, data: [u8; AD_SIZE]) {
		if let BeaconState::Established {
			associated_data, ..
		} = &mut self.state
		{
			*associated_data = data
		}
	}
	pub fn encrypt_message(&mut self, b: &[u8]) -> Option<crate::Encrypted> {
		let sender = self.identity_key_kid;
		let BeaconState::Established {
			control,
			associated_data,
			ratchet,
		} = &mut self.state
		else {
			return None;
		};
		encrypt_message_with_ratchet(b, control.server_key_id(), sender, associated_data, ratchet)
	}
	pub fn decrypt_message(&mut self, b: &[u8]) -> Option<crate::Decrypted> {
		let BeaconState::Established {
			control,
			associated_data,
			ratchet,
		} = &mut self.state
		else {
			return None;
		};
		decrypt_message_with_ratchet(b, control.server_key_id(), associated_data, ratchet)
	}

	fn abort_registration(&mut self, control: verified_pqxdh::BeaconInitSent) {
		let server_kid = control.server_key_id();
		self.identity_key_kid = server_kid;
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
			let mut ratchet = RatchetManager::from_kernel(candidate.derive_ratchet_kernel(
				derived_secret.as_array(),
				initial_ratchet_hkdf,
				ratchet_hkdf,
			));
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
		if self.server_id.as_bytes() != &server_binding.identity_public_key {
			self.abort_registration(control);
			return None;
		}
		self.identity_key_kid = authenticated.assigned_key_id();
		self.state = BeaconState::Established {
			control: verified_pqxdh::beacon_commit(authenticated),
			associated_data,
			ratchet,
		};
		Some(plaintext)
	}
}
