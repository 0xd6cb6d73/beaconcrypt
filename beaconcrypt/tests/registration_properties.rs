// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use beaconcrypt::*;
use beaconcrypt_core::authentication as transcript;
use beaconcrypt_crypto::crypto_generichash;
use beaconcrypt_parse::{KexResponse, decode_frame, decode_init, decode_response};
use ml_dsa::{Keypair, MlDsa65, SigningKey};
use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;

mod common;

const SERVER_MLDSA_SEED: [u8; 32] = [0x74; 32];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase {
	Pending,
	Established,
	Aborted,
}

struct Peer {
	beacon: Beacon,
	init: Vec<u8>,
	response: RegResponse,
	payload: Vec<u8>,
	phase: Phase,
}

#[derive(Clone, Debug)]
enum Command {
	Complete(usize, u8, usize),
	ReplayInit(usize),
	RequestBundle(usize),
	Exchange(usize, Vec<u8>),
}

fn command() -> impl Strategy<Value = Command> {
	prop_oneof![
		4 => (0usize..3, 0u8..8, 0usize..256).prop_map(|(peer, kind, index)| Command::Complete(peer, kind, index)),
		2 => (0usize..3).prop_map(Command::ReplayInit),
		1 => (0usize..3).prop_map(Command::RequestBundle),
		4 => (0usize..3, proptest::collection::vec(any::<u8>(), 1..65)).prop_map(|(peer, payload)| Command::Exchange(peer, payload)),
	]
}

fn check(peer: &Peer, server_kid: u64) {
	let established = peer.phase == Phase::Established;
	assert_eq!(peer.beacon.ratchet_status().is_some(), established);
	assert_eq!(peer.beacon.associated_data().is_some(), established);
	assert_eq!(
		peer.beacon.identity_key_kid(),
		if established {
			peer.response.kid
		} else {
			server_kid
		},
	);
	let pending = peer.phase == Phase::Pending;
	assert_eq!(peer.beacon.get_prekey_sk().is_some(), pending);
	assert_eq!(peer.beacon.get_onetime_sk().is_some(), pending);
	assert_eq!(peer.beacon.pq_sk().is_some(), pending);
}

fn server_statuses(server: &Server, peers: &[Peer]) -> Vec<RatchetStatus> {
	peers
		.iter()
		.map(|peer| server.ratchet_status(peer.response.kid).unwrap())
		.collect()
}

fn response_with_ciphertext(response: &RegResponse, ciphertext: &[u8], kid: u64) -> Vec<u8> {
	let original = decode_response(&response.serialized).unwrap();
	common::encode_response(KexResponse {
		app_cipher_text: ciphertext,
		key_id: kid,
		..original
	})
}

// Re-sign selected malformed responses so generated histories also reach the inner CTX checks.
// Other command kinds retain the original signature and exercise the mandatory authentication gate.
fn authenticate_response(server: &Server, init: &[u8], response: &[u8]) -> Vec<u8> {
	let init = decode_init(init).unwrap();
	let init_bytes = transcript::build_init_transcript(
		transcript::InitFields {
			identity_key: init.identity_key.try_into().unwrap(),
			pre_key: init.pre_key.try_into().unwrap(),
			one_time_key: init.one_time_key.try_into().unwrap(),
			pq_key: init.pq_key.try_into().unwrap(),
			mldsa_public_key: init.mldsa_public_key.try_into().unwrap(),
		},
		server.identity_key_kid(),
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init_hash: [u8; 64] = crypto_generichash::generichash(&init_bytes, None, 64)
		.unwrap()
		.try_into()
		.unwrap();
	let response = decode_response(response).unwrap();
	let body = transcript::build_response_transcript(
		&init_hash,
		transcript::ResponseFields {
			identity_key: response.identity_key.try_into().unwrap(),
			ephemeral_key: response.ephemeral_key.try_into().unwrap(),
			kem_cipher_text: response.kem_cipher_text.try_into().unwrap(),
			app_cipher_text: response.app_cipher_text,
			key_id: response.key_id,
		},
	)
	.unwrap();
	let response_hash: [u8; 64] = crypto_generichash::generichash(&body.parts().concat(), None, 64)
		.unwrap()
		.try_into()
		.unwrap();
	let signer = SigningKey::<MlDsa65>::from_seed((&SERVER_MLDSA_SEED).into());
	assert_eq!(
		signer.verifying_key().encode().as_slice(),
		server.mldsa_public_key()
	);
	let input = transcript::build_signature_input(transcript::AuthRole::Server, &response_hash);
	let signature = signer
		.expanded_key()
		.sign_deterministic(&input, &transcript::SIGNING_CONTEXT)
		.unwrap()
		.encode();
	assert!(signer.verifying_key().verify_with_context(
		&input,
		&transcript::SIGNING_CONTEXT,
		&ml_dsa::Signature::<MlDsa65>::try_from(signature.as_slice()).unwrap(),
	));
	common::encode_response(KexResponse {
		signature: signature.as_slice(),
		..response
	})
}

#[test]
fn test_signer_preserves_an_accepted_registration_response() {
	let mut server = Server::new(19, Some(&[0x73; 32]), Some(&SERVER_MLDSA_SEED));
	let mut beacon = Beacon::new(
		19,
		server.identity_pk().as_bytes(),
		&server.mldsa_public_key(),
	);
	let init = beacon.get_registration_bundle().unwrap();
	let registration = server.get_shared_secret(&init).unwrap();
	let response = server
		.build_registration_response(registration, Some(b"signer control"))
		.unwrap();
	let signed = authenticate_response(&server, &init, &response.serialized);
	assert_eq!(
		beacon.finish_registration(&signed).unwrap(),
		b"signer control"
	);
}

fn complete(server: &mut Server, peers: &mut [Peer], selected: usize, kind: u8, index: usize) {
	let other = (selected + 1) % peers.len();
	let peer = &peers[selected];
	let response = decode_response(&peer.response.serialized).unwrap();
	let candidate = match kind {
		0 => peer.response.serialized.clone(),
		1 => peers[other].response.serialized.clone(),
		2 | 5 => {
			let mut ciphertext = response.app_cipher_text.to_vec();
			let index = index % ciphertext.len();
			ciphertext[index] ^= 1;
			response_with_ciphertext(&peer.response, &ciphertext, peer.response.kid)
		}
		3 | 6 => response_with_ciphertext(
			&peer.response,
			response.app_cipher_text,
			peer.response.kid ^ (1 << 63),
		),
		_ => {
			// Kinds 4 and 7 replace the initial ciphertext with a later ratchet ciphertext.
			// Kind 7 is re-signed below, so rejection also exercises implicit sequence one.
			let mut payload = peer.response.kid.to_le_bytes().to_vec();
			payload.extend_from_slice(&peer.payload);
			let later = server.encrypt_message(&payload, peer.response.kid).unwrap();
			response_with_ciphertext(
				&peer.response,
				decode_frame(&later).unwrap().cipher_text,
				peer.response.kid,
			)
		}
	};
	let candidate = if kind >= 5 {
		authenticate_response(server, &peers[selected].init, &candidate)
	} else {
		candidate
	};
	let before_server = server_statuses(server, peers);
	let before_beacons: Vec<_> = peers
		.iter()
		.map(|peer| peer.beacon.ratchet_status())
		.collect();
	let before_ad = peers[selected].beacon.associated_data();
	let peer = &mut peers[selected];
	let expected = (peer.phase == Phase::Pending && kind == 0).then(|| peer.payload.clone());
	assert_eq!(peer.beacon.finish_registration(&candidate), expected);
	if peer.phase == Phase::Pending {
		peer.phase = if kind == 0 {
			Phase::Established
		} else {
			Phase::Aborted
		};
		if peer.phase == Phase::Established {
			let status = peer.beacon.ratchet_status().unwrap();
			assert_eq!(status.send_sequence(), 0);
			assert_eq!(status.receive_sequence(), 1);
			assert_eq!(status.receive_cache_len(), 0);
		}
	} else {
		assert_eq!(peer.beacon.ratchet_status(), before_beacons[selected]);
		assert_eq!(peer.beacon.associated_data(), before_ad);
	}
	assert_eq!(server_statuses(server, peers), before_server);
	for (index, peer) in peers.iter().enumerate() {
		if index != selected {
			assert_eq!(peer.beacon.ratchet_status(), before_beacons[index]);
		}
	}
}

fn replay_init(server: &mut Server, peers: &[Peer], selected: usize) {
	let before = server_statuses(server, peers);
	assert!(server.get_shared_secret(&peers[selected].init).is_none());
	assert_eq!(server_statuses(server, peers), before);
	for peer in peers {
		assert_eq!(
			server.pk_by_kid(peer.response.kid),
			Some(peer.beacon.identity_pk())
		);
	}
}

fn exchange(server: &mut Server, peers: &mut [Peer], selected: usize, payload: &[u8]) {
	if peers[selected].phase != Phase::Established {
		let before = server_statuses(server, peers);
		assert!(peers[selected].beacon.encrypt_message(payload).is_none());
		assert!(
			peers[selected]
				.beacon
				.decrypt_message(b"invalid frame")
				.is_none()
		);
		assert_eq!(server_statuses(server, peers), before);
		return;
	}
	let kid = peers[selected].response.kid;
	let outbound = peers[selected].beacon.encrypt_message(payload).unwrap();
	let received = server.decrypt_message(&outbound).unwrap();
	assert_eq!(received.plaintext, payload);
	assert_eq!(received.key_id, kid);
	let before_replay = server_statuses(server, peers);
	assert!(server.decrypt_message(&outbound).is_none());
	assert_eq!(server_statuses(server, peers), before_replay);
	let inbound = server.encrypt_message(payload, kid).unwrap();
	for (index, peer) in peers.iter_mut().enumerate() {
		if index != selected {
			let before = peer.beacon.ratchet_status();
			assert!(peer.beacon.decrypt_message(&inbound).is_none());
			assert_eq!(peer.beacon.ratchet_status(), before);
		}
	}
	assert_eq!(
		peers[selected]
			.beacon
			.decrypt_message(&inbound)
			.unwrap()
			.plaintext,
		payload
	);
	let before_replay = peers[selected].beacon.ratchet_status();
	assert!(peers[selected].beacon.decrypt_message(&inbound).is_none());
	assert_eq!(peers[selected].beacon.ratchet_status(), before_replay);
}

fn config() -> ProptestConfig {
	ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok()
			.and_then(|cases| cases.parse().ok())
			.unwrap_or(24),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/proptest-regressions/registration_properties.txt"
		)))),
		..ProptestConfig::default()
	}
}

proptest! {
	#![proptest_config(config())]

	#[test]
	fn registration_histories_bind_peers_and_make_failure_terminal(
		commands in proptest::collection::vec(command(), 0..25),
		payloads in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 1..65), 3),
		server_kid in prop_oneof![Just(0u64), Just(23), Just(256), Just(u64::MAX - 3)],
		valid in 0usize..3,
		invalid in 1u8..8,
		corruption_index in 0usize..256,
	) {
		let mut server = Server::new(server_kid, Some(&[0x73; ED25519_SEED_SIZE]), Some(&SERVER_MLDSA_SEED));
		let mut peers: Vec<_> = payloads.into_iter().map(|payload| {
			let mut beacon = Beacon::new(server_kid, server.identity_pk().as_bytes(), &server.mldsa_public_key());
			assert!(beacon.encrypt_message(b"before registration").is_none());
			let init = beacon.get_registration_bundle().unwrap();
			let registration = server.get_shared_secret(&init).unwrap();
			let response = server.build_registration_response(registration, Some(&payload)).unwrap();
			Peer { beacon, init, response, payload, phase: Phase::Pending }
		}).collect();
		// Every generated history includes one working session and one terminal failed completion.
		complete(&mut server, &mut peers, valid, 0, 0);
		complete(&mut server, &mut peers, (valid + 1) % 3, invalid, corruption_index);
		for command in commands {
			match command {
				Command::Complete(peer, kind, index) => complete(&mut server, &mut peers, peer, kind, index),
				Command::ReplayInit(peer) => replay_init(&mut server, &peers, peer),
				Command::RequestBundle(peer) => assert!(peers[peer].beacon.get_registration_bundle().is_none()),
				Command::Exchange(peer, payload) => exchange(&mut server, &mut peers, peer, &payload),
			}
			for peer in &peers { check(peer, server_kid); }
		}
		for selected in 0..peers.len() {
			if peers[selected].phase == Phase::Pending {
				complete(&mut server, &mut peers, selected, 0, 0);
			}
			replay_init(&mut server, &peers, selected);
			complete(&mut server, &mut peers, selected, 0, 0);
			exchange(&mut server, &mut peers, selected, b"after lifecycle history");
			assert!(peers[selected].beacon.get_registration_bundle().is_none());
			check(&peers[selected], server_kid);
		}
	}
}
