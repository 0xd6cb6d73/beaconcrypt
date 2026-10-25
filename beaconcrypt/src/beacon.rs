// SPDX-License-Identifier: 0BSD

#[cfg(test)]
use crate::auth::AuthRole;
use crate::auth::{self, MLDSA_PUBLIC_KEY_LEN, MldsaIdentity};
use crate::pqxdh::AD_SIZE;
#[cfg(test)]
use crate::pqxdh::mldsa_associated_data;
#[cfg(test)]
use crate::pqxdh::{derive_root_key_input, shared_secrets, zeroize_shared_secrets};
#[cfg(test)]
use crate::ratchet::finish_initial_ratchet_kdf;
use crate::ratchet::{
	RatchetManager, RatchetStatus, decrypt_message_with_ratchet,
	decrypt_registration_message_with_ratchet, encrypt_message_with_ratchet,
};

struct RegistrationAuthentication {
	identity: MldsaIdentity,
	server_pin: ServerAuthenticationPin,
}

use beaconcrypt_core::pqxdh as verified_pqxdh;
use beaconcrypt_core::registration::BeaconPending;
use beaconcrypt_core::session::{ServerAuthenticationPin, SessionBinding};
use beaconcrypt_parse::{InitKex, decode_response};
#[cfg(test)]
use libsodium_rs::crypto_scalarmult;
use libsodium_rs::{crypto_kem, crypto_kx, crypto_sign, ensure_init};

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
		pending: BeaconPending,
		prekey: crypto_kx::KeyPair,
		onetime_key: crypto_kx::KeyPair,
		pq_key: crypto_kem::mlkem768::KeyPair,
	},
	Established {
		control: verified_pqxdh::BeaconEstablished,
		binding: SessionBinding,
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
	authentication: RegistrationAuthentication,
}

pub trait ProviderBeacon {
	fn get_registration_bundle(&mut self) -> Option<Vec<u8>>;
	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>>;
}

impl Beacon {
	/// Construct a beacon, panicking if initialization, input validation or key generation fails.
	/// Use [`Self::try_new`] when inputs or dependency failures must be recoverable.
	pub fn new(server_kid: u64, server_id_pk: &[u8], server_mldsa_pk: &[u8]) -> Self {
		Self::try_new(server_kid, server_id_pk, server_mldsa_pk)
			.expect("Failed to construct beacon")
	}

	/// Construct a beacon without panicking on reported initialization, key-length or key-generation errors.
	/// Allocation failure and failures inside the native RNG remain process-level failures.
	pub fn try_new(
		server_kid: u64,
		server_id_pk: &[u8],
		server_mldsa_pk: &[u8],
	) -> Result<Self, crate::KeyGenError> {
		ensure_init().map_err(|_| crate::KeyGenError)?;
		let id =
			crypto_sign::PublicKey::from_bytes(server_id_pk).map_err(|_| crate::KeyGenError)?;
		let server_public_key = server_mldsa_pk.try_into().map_err(|_| crate::KeyGenError)?;
		let server_binding = verified_pqxdh::ServerBinding {
			identity_public_key: *id.as_bytes(),
			identity_key_id: server_kid,
		};
		let authentication = RegistrationAuthentication {
			identity: MldsaIdentity::generate()?,
			server_pin: auth::fingerprint_pin(server_binding, server_public_key)
				.ok_or(crate::KeyGenError)?,
		};
		Ok(Self {
			identity_key: crypto_sign::KeyPair::generate().map_err(|_| crate::KeyGenError)?,
			identity_key_kid: server_kid,
			state: BeaconState::Fresh {
				control: verified_pqxdh::BeaconFresh::new(server_binding),
				prekey: crypto_kx::KeyPair::generate().map_err(|_| crate::KeyGenError)?,
				pq_key: crypto_kem::mlkem768::KeyPair::generate()
					.map_err(|_| crate::KeyGenError)?,
			},
			server_id: id,
			authentication,
		})
	}
	/// The signing identity authenticated in InitKex; the server key is pinned at construction.
	pub fn mldsa_public_key(&self) -> [u8; MLDSA_PUBLIC_KEY_LEN] {
		self.authentication.identity.public_key()
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
			BeaconState::InitSent { pending, .. } => pending.server_key_id(),
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
		match &self.state {
			BeaconState::Established { binding, .. } => Some(*binding.associated_data()),
			_ => None,
		}
	}
	pub fn ratchet_status(&self) -> Option<RatchetStatus> {
		match &self.state {
			BeaconState::Established { ratchet, .. } => Some(ratchet.status()),
			_ => None,
		}
	}
	pub fn encrypt_message(&mut self, b: &[u8]) -> Option<crate::Encrypted> {
		let sender = self.identity_key_kid;
		let BeaconState::Established {
			control,
			binding,
			ratchet,
		} = &mut self.state
		else {
			return None;
		};
		encrypt_message_with_ratchet(
			b,
			control.server_key_id(),
			sender,
			binding.associated_data(),
			ratchet,
		)
	}
	pub fn decrypt_message(&mut self, b: &[u8]) -> Option<crate::Decrypted> {
		let BeaconState::Established {
			control,
			binding,
			ratchet,
		} = &mut self.state
		else {
			return None;
		};
		decrypt_message_with_ratchet(
			b,
			control.server_key_id(),
			binding.associated_data(),
			ratchet,
		)
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
			BeaconState::InitSent { pending, .. } => BeaconState::Aborted {
				control: pending.abort(),
			},
			other => other,
		};
	}

	pub fn delete_pq_keypair(&mut self) {
		let aborted = match &self.state {
			BeaconState::Fresh { control, .. } | BeaconState::FreshWithCoins { control, .. } => {
				Some(verified_pqxdh::beacon_abort_fresh(*control))
			}
			BeaconState::InitSent { pending, .. } => Some(pending.aborted_state()),
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
		use beaconcrypt_core::registration::{self as registration, BeaconInitEffect};
		let mut effect = registration::begin_beacon_init(
			control,
			verified_pqxdh::BeaconStartInputs {
				identity_public_key: *self.identity_pk().as_bytes(),
				prekey_public_key: prekey_public,
				pq_public_key: pq_public,
			},
			verified_pqxdh::BeaconCoins {
				one_time_public_key: onetime_public,
			},
			self.authentication.server_pin,
			self.mldsa_public_key(),
		);
		let ready = loop {
			effect = match effect {
				BeaconInitEffect::Rejected(_) => return None,
				BeaconInitEffect::Ready(ready) => break ready,
				BeaconInitEffect::Ed25519SigningRequested(pending) => {
					let request = pending.request();
					let signed = if self.identity_pk().as_bytes() == request.public_key {
						crypto_sign::sign(request.message, self.identity_sk()).ok()
					} else {
						None
					};
					pending.resume(signed.as_deref())
				}
				BeaconInitEffect::FingerprintRequested(pending) => {
					let fingerprint = auth::execute_hash(&pending.request());
					pending.resume(fingerprint)
				}
				BeaconInitEffect::HashRequested(pending) => {
					let hash = auth::execute_hash(&pending.request());
					pending.resume(hash)
				}
				BeaconInitEffect::MldsaSigningRequested(pending) => {
					let signature = self
						.authentication
						.identity
						.sign_requested(&pending.request());
					pending.resume(signature.as_deref())
				}
			};
		};
		let message = ready.message();
		let buffer = crate::wire::encode_init(InitKex {
			identity_key: message.fields.identity_key,
			pre_key: message.fields.pre_key,
			one_time_key: message.fields.one_time_key,
			pq_key: message.fields.pq_key,
			mldsa_public_key: message.fields.mldsa_public_key,
			signature: message.signature,
		});
		let (pending, buffer) = ready.publish(buffer).ok()?.into_parts();
		let fallback = BeaconState::Aborted {
			control: pending.aborted_state(),
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
					pending,
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
					pending,
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

	fn finish_registration(&mut self, bytes: &[u8]) -> Option<Vec<u8>> {
		use beaconcrypt_core::agreement::{self, AgreementEffect};
		use beaconcrypt_core::registration::{self as registration, InitialOpened, ResponsePacket};
		let aborted = match &self.state {
			BeaconState::InitSent { pending, .. } => pending.aborted_state(),
			_ => return None,
		};
		let previous =
			std::mem::replace(&mut self.state, BeaconState::Aborted { control: aborted });
		let BeaconState::InitSent {
			pending,
			prekey,
			onetime_key,
			pq_key,
		} = previous
		else {
			return None;
		};
		let packet = decode_response(bytes).and_then(|response| {
			ResponsePacket::from_slices(
				response.identity_key,
				response.ephemeral_key,
				response.kem_cipher_text,
				response.key_id,
				response.app_cipher_text,
				response.signature,
			)
		});
		let authenticated = match auth::authenticate_response(pending, packet) {
			Ok(authenticated) => authenticated,
			Err(control) => {
				self.state = BeaconState::Aborted { control };
				return None;
			}
		};
		let effect = crate::pqxdh::execute_agreement(
			agreement::begin_beacon_agreement(authenticated),
			crate::pqxdh::RegistrationKeys {
				identity_secret: self.identity_sk(),
				beacon_prekey: Some(&prekey.secret_key),
				beacon_one_time: Some(&onetime_key.secret_key),
				beacon_kem: Some(&pq_key.secret_key),
			},
		);
		let agreement = match effect {
			AgreementEffect::BeaconComplete(agreement) => agreement,
			AgreementEffect::Rejected(Some(control)) => {
				self.state = BeaconState::Aborted { control };
				return None;
			}
			_ => return None,
		};
		let pending = registration::begin_beacon_completion(agreement);
		let response = verified_pqxdh::InitialRatchetKdfResponse::from_bytes(
			crate::ratchet::initial_ratchet_hkdf(pending.request()),
		);
		let mut pending = match pending.resume(Some(response)) {
			Ok(pending) => pending,
			Err(control) => {
				self.state = BeaconState::Aborted { control };
				return None;
			}
		};
		let mut ratchet = RatchetManager::from_kernel(pending.take_kernel()?);
		let request = pending.request();
		let opened = decrypt_registration_message_with_ratchet(
			request.ciphertext,
			request.sender_key_id,
			request.associated_data,
			&mut ratchet,
		);
		let result = pending.resume(
			ratchet.into_kernel(),
			opened.as_ref().map(|opened| InitialOpened {
				plaintext: &opened.plaintext,
				sequence: opened.seq,
				sender_key_id: opened.key_id,
			}),
		);
		let completed = match result {
			Ok(completed) => completed,
			Err(control) => {
				self.state = BeaconState::Aborted { control };
				return None;
			}
		};
		let (control, binding, kernel, application) = completed.into_parts();
		let plaintext = application.to_vec();
		self.identity_key_kid = binding.assigned_key_id();
		self.state = BeaconState::Established {
			control,
			binding,
			ratchet: RatchetManager::from_kernel(kernel),
		};
		Some(plaintext)
	}
}

#[cfg(all(test, feature = "server"))]
mod tests {
	use super::*;
	use crate::{ProviderServer, Server};

	#[test]
	fn first_sequence_still_requires_nonempty_bound_plaintext() {
		for case in 0..10 {
			let mldsa_seed = [0x5a; 32];
			let mut server = Server::new(0, None, Some(&mldsa_seed));
			let mut beacon = Beacon::new(
				0,
				server.identity_pk().as_bytes(),
				&server.mldsa_public_key(),
			);
			let init = beacon.get_registration_bundle().unwrap();
			let accepted = server.get_shared_secret(&init).unwrap();
			let original = server.build_registration_response(accepted, None).unwrap();
			let response = decode_response(&original.serialized).unwrap();
			// Reconstruct the honest root from the receiver's retained test keys rather than exporting the opaque server agreement.
			let server_kex = crypto_sign::ed25519_pk_to_curve25519(server.identity_pk()).unwrap();
			let beacon_kex = crypto_sign::ed25519_sk_to_curve25519(beacon.identity_sk()).unwrap();
			let ciphertext =
				crypto_kem::mlkem768::Ciphertext::from_bytes(response.kem_cipher_text).unwrap();
			let kem =
				crypto_kem::mlkem768::decapsulate(&ciphertext, beacon.pq_sk().unwrap()).unwrap();
			let mut secrets = shared_secrets(
				crypto_scalarmult::scalarmult(
					beacon.get_prekey_sk().unwrap().as_bytes(),
					&server_kex,
				)
				.unwrap()
				.into(),
				crypto_scalarmult::scalarmult(&beacon_kex, response.ephemeral_key)
					.unwrap()
					.into(),
				crypto_scalarmult::scalarmult(
					beacon.get_prekey_sk().unwrap().as_bytes(),
					response.ephemeral_key,
				)
				.unwrap()
				.into(),
				crypto_scalarmult::scalarmult(
					beacon.get_onetime_sk().unwrap().as_bytes(),
					response.ephemeral_key,
				)
				.unwrap()
				.into(),
				&kem,
			)
			.unwrap();
			let mut input = verified_pqxdh::build_root_key_input(&secrets).unwrap();
			zeroize_shared_secrets(&mut secrets);
			let root = derive_root_key_input(&mut input).unwrap();
			let pending = verified_pqxdh::start_server_ratchet_kdf(root.as_array());
			let mut sender = RatchetManager::from_kernel(finish_initial_ratchet_kdf(pending));
			let ad = mldsa_associated_data(
				&verified_pqxdh::build_associated_data(
					*server.identity_pk().as_bytes(),
					*beacon.identity_pk().as_bytes(),
				),
				&auth::public_key_hash(&server.mldsa_public_key()).unwrap(),
				&auth::public_key_hash(&beacon.mldsa_public_key()).unwrap(),
			);
			let payload = if case < 8 {
				original.kid.to_le_bytes()[..case + 1].to_vec()
			} else {
				let claimed = if case == 8 {
					original.kid + 1
				} else {
					original.kid
				};
				let mut payload = claimed.to_le_bytes().to_vec();
				payload.push(0x7e);
				payload
			};
			let frame =
				encrypt_message_with_ratchet(&payload, original.kid, 0, &ad, &mut sender).unwrap();
			assert_eq!(sender.status().send_sequence(), 1);
			let raw_frame = beaconcrypt_parse::decode_frame(&frame.ciphertext).unwrap();
			let response = decode_response(&original.serialized).unwrap();
			let rewritten = beaconcrypt_parse::KexResponse {
				identity_key: response.identity_key,
				ephemeral_key: response.ephemeral_key,
				kem_cipher_text: response.kem_cipher_text,
				key_id: original.kid,
				app_cipher_text: raw_frame.cipher_text,
				signature: &[],
			};
			let init_hash = auth::init_transcript_hash(
				&beaconcrypt_parse::decode_init(&init).unwrap(),
				server.identity_key_kid(),
				server.identity_pk().as_bytes(),
				&server.mldsa_public_key(),
			)
			.unwrap();
			let hash = auth::response_transcript_hash(&init_hash, &rewritten).unwrap();
			let signature = MldsaIdentity::from_seed(mldsa_seed)
				.sign(AuthRole::Server, &hash)
				.unwrap();
			let serialized = crate::wire::encode_response(beaconcrypt_parse::KexResponse {
				signature: &signature,
				..rewritten
			})
			.unwrap();
			let opened = beacon.finish_registration(&serialized);
			if case == 9 {
				assert_eq!(opened, Some(vec![0x7e]));
				assert_eq!(beacon.ratchet_status().unwrap().receive_sequence(), 1);
			} else {
				assert!(opened.is_none(), "malformed plaintext case {case}");
				assert!(beacon.ratchet_status().is_none());
				assert!(beacon.finish_registration(&original.serialized).is_none());
			}
		}
	}
}
