// SPDX-License-Identifier: 0BSD

use crate::shared::{DhSecret, KEX_KDF_OUT_LEN, KexDerivedSecret, SignaturePk};
use beaconcrypt_protocol_core::pqxdh as verified_pqxdh;
use libsodium_rs::{crypto_kdf, crypto_kem, crypto_kx, crypto_sign};
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

pub(crate) fn shared_secrets(
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

pub(crate) fn zeroize_shared_secrets(secrets: &mut verified_pqxdh::PqxdhSharedSecrets) {
	secrets.dh1.zeroize();
	secrets.dh2.zeroize();
	secrets.dh3.zeroize();
	secrets.dh4.zeroize();
	secrets.kem_shared_secret.zeroize();
}

pub(crate) fn derive_root_key_input(
	input: &mut verified_pqxdh::RootKeyInput,
) -> Option<KexDerivedSecret> {
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
		AD_SIZE, PQXDH_INFO, build_associated_data, derive_root_key_input, verified_pqxdh,
		zeroize_shared_secrets,
	};
	use crate::{
		Beacon, DH_OUT_LEN, ED25519_SEED_SIZE, KDF_STATE_SIZE, ProviderBeacon, ProviderServer,
		Server, SignType, phase1_capnp,
		shared::{DhSecret, KemType, KexDerivedSecret, decode_kem, decode_sign},
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

		assert_eq!(server.ratchet_recv_until(2, 9), Some(2));
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
		assert_eq!(server.ratchet_recv_until(1, 99), None);
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
		expected.extend_from_slice(verified_pqxdh::SYM_RATCHET_INFO);
		assert_eq!(actual.as_slice(), expected);
	}
}
