// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use beaconcrypt::{Beacon, ProviderBeacon, ProviderServer, Server};
use beaconcrypt_crypto::{CryptoError, TryCryptoRng, TryRng, crypto_sign};
use beaconcrypt_parse::{CryptoFrame, InitKex};

mod common;

// Deliberately disclose/reuse the classical identity while varying all later entropy.
struct Coins {
	identity: u8,
	session: u8,
	draw: u8,
}

impl TryRng for Coins {
	type Error = CryptoError;

	fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
		let mut bytes = [0; 4];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u32::from_le_bytes(bytes))
	}

	fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
		let mut bytes = [0; 8];
		self.try_fill_bytes(&mut bytes)?;
		Ok(u64::from_le_bytes(bytes))
	}

	fn try_fill_bytes(&mut self, bytes: &mut [u8]) -> Result<(), Self::Error> {
		bytes.fill(if self.draw == 0 {
			self.identity
		} else {
			self.session.wrapping_add(self.draw)
		});
		self.draw += 1;
		Ok(())
	}
}

impl TryCryptoRng for Coins {}

fn beacon(server: &Server, identity: u8, session: u8) -> Beacon {
	Beacon::try_new_with_rng(
		7,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
		&mut Coins {
			identity,
			session,
			draw: 0,
		},
	)
	.unwrap()
}

fn register(server: &mut Server, beacon: &mut Beacon, payload: &[u8]) -> u64 {
	let request = beacon.get_registration_bundle().unwrap();
	let accepted = server.get_shared_secret(&request).unwrap();
	let response = server
		.build_registration_response(accepted, Some(payload))
		.unwrap();
	assert_eq!(
		beacon.finish_registration(&response.serialized).unwrap(),
		payload
	);
	response.kid
}

#[test]
fn attacker_registrations_with_a_disclosed_classical_identity_remain_separate() {
	let mut server = Server::new(7, Some(&[1; 32]), Some(&[2; 32]));
	let mut honest = beacon(&server, 11, 20);
	let mut second = beacon(&server, 12, 30);
	let mut attacker = beacon(&server, 11, 40);
	assert_eq!(honest.identity_pk(), attacker.identity_pk());
	assert_ne!(honest.pq_pk(), attacker.pq_pk());
	let honest_id = register(&mut server, &mut honest, b"honest secret");
	let second_id = register(&mut server, &mut second, b"second secret");
	let attacker_id = register(&mut server, &mut attacker, b"public canary");
	assert_ne!(honest.associated_data(), attacker.associated_data());
	assert_ne!(honest.associated_data(), second.associated_data());

	let from_honest = honest.encrypt_message(b"honest record").unwrap();
	let decoded = beaconcrypt_parse::decode_frame(&from_honest).unwrap();
	for target in [second_id, attacker_id] {
		let retargeted = common::encode_frame(CryptoFrame {
			key_id: target,
			..decoded
		});
		let before = server.ratchet_status(target).unwrap();
		assert!(server.decrypt_message(&retargeted).is_none());
		assert_eq!(server.ratchet_status(target), Some(before));
	}
	assert_eq!(
		server.decrypt_message(&from_honest).unwrap().plaintext,
		b"honest record"
	);

	let from_server = server.encrypt_message(b"for honest", honest_id).unwrap();
	for receiver in [&mut second, &mut attacker] {
		let before = receiver.ratchet_status();
		assert!(receiver.decrypt_message(&from_server).is_none());
		assert_eq!(receiver.ratchet_status(), before);
	}
	assert_eq!(
		honest.decrypt_message(&from_server).unwrap().plaintext,
		b"for honest"
	);
	let canary = attacker.encrypt_message(b"attacker traffic").unwrap();
	assert_eq!(
		server.decrypt_message(&canary).unwrap().plaintext,
		b"attacker traffic"
	);
	let canary = server
		.encrypt_message(b"attacker reply", attacker_id)
		.unwrap();
	assert_eq!(
		attacker.decrypt_message(&canary).unwrap().plaintext,
		b"attacker reply"
	);
}

#[test]
fn copied_honest_kem_public_key_does_not_give_an_attacker_the_honest_session() {
	let mut server = Server::new(7, Some(&[1; 32]), Some(&[2; 32]));
	let mut honest = beacon(&server, 11, 20);
	let mut attacker = beacon(&server, 11, 40);
	let honest_request = honest.get_registration_bundle().unwrap();
	let attacker_request = attacker.get_registration_bundle().unwrap();
	let honest_fields = beaconcrypt_parse::decode_init(&honest_request).unwrap();
	let attacker_fields = beaconcrypt_parse::decode_init(&attacker_request).unwrap();
	let public_kem = crypto_sign::verify(honest_fields.pq_key, honest.identity_pk()).unwrap();
	let copied_kem = crypto_sign::sign(&public_kem, attacker.identity_sk()).unwrap();
	let substituted = common::encode_unchecked_init(InitKex {
		pq_key: &copied_kem,
		..attacker_fields
	});
	let accepted = server.get_shared_secret(&substituted).unwrap();
	let attacker_response = server
		.build_registration_response(accepted, Some(b"canary"))
		.unwrap();
	// Finish hashes the original published request, even if the copied KEM is otherwise valid.
	assert!(
		attacker
			.finish_registration(&attacker_response.serialized)
			.is_none()
	);
	assert!(attacker.ratchet_status().is_none());
	assert!(server.get_shared_secret(&substituted).is_none());

	let accepted = server.get_shared_secret(&honest_request).unwrap();
	let honest_response = server
		.build_registration_response(accepted, Some(b"honest secret"))
		.unwrap();
	assert_eq!(
		honest
			.finish_registration(&honest_response.serialized)
			.unwrap(),
		b"honest secret"
	);
	let record = server
		.encrypt_message(b"still isolated", honest_response.kid)
		.unwrap();
	assert_eq!(
		honest.decrypt_message(&record).unwrap().plaintext,
		b"still isolated"
	);
}

// A rejected initial response must release nothing, establish nothing and erase the one-use attempt.
fn assert_aborted(beacon: &mut Beacon, genuine: &[u8]) {
	assert!(beacon.ratchet_status().is_none());
	assert!(beacon.associated_data().is_none());
	assert!(beacon.pq_sk().is_none());
	assert!(beacon.get_prekey_sk().is_none());
	assert!(beacon.get_onetime_sk().is_none());
	assert!(beacon.finish_registration(genuine).is_none());
	assert!(beacon.encrypt_message(b"aborted").is_none());
}

fn respond(server: &mut Server, request: &[u8], payload: &[u8]) -> (Vec<u8>, u64) {
	let accepted = server.get_shared_secret(request).unwrap();
	let response = server
		.build_registration_response(accepted, Some(payload))
		.unwrap();
	(response.serialized, response.kid)
}

#[test]
fn honest_kem_owner_rejects_the_response_to_a_copied_kem_request() {
	let mut server = Server::new(7, Some(&[1; 32]), Some(&[2; 32]));
	let mut honest = beacon(&server, 11, 20);
	let mut attacker = beacon(&server, 11, 40);
	let honest_request = honest.get_registration_bundle().unwrap();
	let attacker_request = attacker.get_registration_bundle().unwrap();
	let honest_fields = beaconcrypt_parse::decode_init(&honest_request).unwrap();
	let attacker_fields = beaconcrypt_parse::decode_init(&attacker_request).unwrap();
	let public_kem = crypto_sign::verify(honest_fields.pq_key, honest.identity_pk()).unwrap();
	let copied_kem = crypto_sign::sign(&public_kem, attacker.identity_sk()).unwrap();
	let substituted = common::encode_unchecked_init(InitKex {
		pq_key: &copied_kem,
		..attacker_fields
	});
	// The honest Beacon shares the copied Ed identity and owns the KEM secret for this response.
	let (attacker_response, attacker_id) = respond(&mut server, &substituted, b"attacker canary");
	let (honest_response, honest_id) = respond(&mut server, &honest_request, b"honest secret");
	let attacker_status = server.ratchet_status(attacker_id).unwrap();
	let honest_status = server.ratchet_status(honest_id).unwrap();

	assert!(honest.finish_registration(&attacker_response).is_none());
	assert_aborted(&mut honest, &honest_response);
	assert_eq!(server.ratchet_status(attacker_id), Some(attacker_status));
	assert_eq!(server.ratchet_status(honest_id), Some(honest_status));
	assert!(server.get_shared_secret(&substituted).is_none());
	assert!(server.get_shared_secret(&honest_request).is_none());
}

#[test]
fn initial_responses_moved_between_sessions_release_nothing() {
	let mut server = Server::new(7, Some(&[1; 32]), Some(&[2; 32]));
	let mut first = beacon(&server, 11, 20);
	let mut second = beacon(&server, 12, 30);
	// The attacker copies the first session's classical identity.
	let mut attacker = beacon(&server, 11, 40);
	let first_request = first.get_registration_bundle().unwrap();
	let second_request = second.get_registration_bundle().unwrap();
	let attacker_request = attacker.get_registration_bundle().unwrap();
	let (first_response, first_id) = respond(&mut server, &first_request, b"first secret");
	let (second_response, second_id) = respond(&mut server, &second_request, b"second secret");
	let (attacker_response, attacker_id) =
		respond(&mut server, &attacker_request, b"attacker canary");
	let statuses = [first_id, second_id, attacker_id].map(|id| server.ratchet_status(id).unwrap());

	for (receiver, moved, genuine) in [
		(&mut first, &second_response, &first_response),
		(&mut second, &first_response, &second_response),
		(&mut attacker, &first_response, &attacker_response),
	] {
		assert!(receiver.finish_registration(moved).is_none());
		assert_aborted(receiver, genuine);
	}
	assert_eq!(
		[first_id, second_id, attacker_id].map(|id| server.ratchet_status(id).unwrap()),
		statuses
	);

	// A fresh session with the copied identity still registers and receives its own payload.
	let mut retry = beacon(&server, 11, 50);
	let retry_id = register(&mut server, &mut retry, b"attacker retry");
	let record = server.encrypt_message(b"attacker reply", retry_id).unwrap();
	assert_eq!(
		retry.decrypt_message(&record).unwrap().plaintext,
		b"attacker reply"
	);
}
