// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use std::sync::{Arc, Mutex};

use beaconcrypt::*;
use beaconcrypt_parse::{CryptoFrame, decode_frame};
use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;

mod common;

#[derive(Default)]
struct Stored {
	bytes: Option<Vec<u8>>,
	head: Option<SnapshotHead>,
	attempts: usize,
	fail_next: bool,
}

#[derive(Clone, Default)]
struct Store(Arc<Mutex<Stored>>);

impl SnapshotStore for Store {
	fn load(&self) -> Option<ServerSnapshot> {
		self.0
			.lock()
			.unwrap()
			.bytes
			.clone()
			.map(ServerSnapshot::from_bytes)
	}

	fn compare_and_swap(
		&mut self,
		expected: Option<&SnapshotHead>,
		replacement: &ServerSnapshot,
	) -> bool {
		let mut stored = self.0.lock().unwrap();
		stored.attempts += 1;
		if std::mem::take(&mut stored.fail_next) || stored.head.as_ref() != expected {
			return false;
		}
		let Ok(head) = replacement.validate_successor(expected) else {
			return false;
		};
		stored.bytes = Some(replacement.as_bytes().to_vec());
		stored.head = Some(head);
		true
	}
}

#[derive(Clone, Copy, Debug)]
enum Direction {
	ToServer,
	ToBeacon,
}

#[derive(Clone, Debug)]
enum Command {
	Send(usize, Direction, Vec<u8>),
	Deliver(usize, Direction, usize, bool, u8),
	Restore(usize),
}

fn command() -> impl Strategy<Value = Command> {
	let direction = || prop_oneof![Just(Direction::ToServer), Just(Direction::ToBeacon)];
	prop_oneof![
		4 => (0usize..2, direction(), proptest::collection::vec(any::<u8>(), 1..65))
			.prop_map(|(peer, direction, payload)| Command::Send(peer, direction, payload)),
		6 => (0usize..2, direction(), 0usize..64, any::<bool>(), 0u8..3)
			.prop_map(|(peer, direction, index, corrupt, api)|
				Command::Deliver(peer, direction, index, corrupt, api)),
		1 => (0usize..2).prop_map(Command::Restore),
	]
}

struct Record {
	frame: Vec<u8>,
	plaintext: Vec<u8>,
	consumed: bool,
}

struct Peer {
	beacon: Beacon,
	kid: u64,
	to_server: Vec<Record>,
	to_beacon: Vec<Record>,
}

impl Peer {
	fn records(&self, direction: Direction) -> &[Record] {
		match direction {
			Direction::ToServer => &self.to_server,
			Direction::ToBeacon => &self.to_beacon,
		}
	}

	fn records_mut(&mut self, direction: Direction) -> &mut Vec<Record> {
		match direction {
			Direction::ToServer => &mut self.to_server,
			Direction::ToBeacon => &mut self.to_beacon,
		}
	}
}

struct History {
	server: PersistentServer<Store>,
	store: Store,
	peers: Vec<Peer>,
	// The model counts committed effects and attempts independently of snapshot contents.
	generation: u64,
	attempts: usize,
}

fn corrupt(frame: &[u8]) -> Vec<u8> {
	let original = decode_frame(frame).unwrap();
	let mut ciphertext = original.cipher_text.to_vec();
	ciphertext[0] ^= 1;
	common::encode_frame(CryptoFrame {
		cipher_text: &ciphertext,
		..original
	})
}

fn receive(
	server: &mut PersistentServer<Store>,
	frame: &[u8],
	api: u8,
) -> Result<Option<Vec<u8>>, PersistenceError> {
	match api % 3 {
		0 => server
			.decrypt_message(frame)
			.map(|output| output.map(|message| message.plaintext)),
		1 => server
			.decrypt_and_update(frame)
			.map(|output| output.map(|update| update.data)),
		_ => server.decrypt_and_update_json(frame).map(|output| {
			output.map(|json| {
				let value: serde_json::Value = serde_json::from_str(&json).unwrap();
				serde_json::from_value(value["data"].clone()).unwrap()
			})
		}),
	}
}

impl History {
	fn new() -> Self {
		let store = Store::default();
		let mut server = PersistentServer::create_with_lineage(
			7,
			Some(&[0x71; ED25519_SEED_SIZE]),
			Some(&[0x73; 32]),
			store.clone(),
			SnapshotLineage::from_bytes([0x72; 32]),
		)
		.unwrap();
		let peers = (0..2)
			.map(|_| {
				let mut beacon = Beacon::new(
					7,
					server.identity_pk().as_bytes(),
					&server.mldsa_public_key(),
				);
				let init = beacon.get_registration_bundle().unwrap();
				let registration = server.get_shared_secret(&init).unwrap().unwrap();
				let response = server
					.build_registration_response(registration, Some(b"registration"))
					.unwrap()
					.unwrap();
				assert_eq!(
					beacon.finish_registration(&response.serialized).unwrap(),
					b"registration"
				);
				Peer {
					beacon,
					kid: response.kid,
					to_server: vec![],
					to_beacon: vec![],
				}
			})
			.collect();
		let history = Self {
			server,
			store,
			peers,
			generation: 4,
			attempts: 5,
		};
		history.check();
		history
	}

	fn check(&self) {
		assert!(!self.server.is_poisoned());
		assert_eq!(self.server.head().generation(), self.generation);
		let stored = self.store.0.lock().unwrap();
		assert_eq!(stored.head, Some(self.server.head()));
		assert_eq!(stored.attempts, self.attempts);
		assert!(!stored.fail_next);
		let bytes = stored.bytes.clone().unwrap();
		drop(stored);
		assert_eq!(self.server.snapshot().unwrap().as_bytes(), bytes);
		for peer in &self.peers {
			let server = self.server.ratchet_status(peer.kid).unwrap();
			let beacon = peer.beacon.ratchet_status().unwrap();
			assert_eq!(server.send_sequence(), peer.to_beacon.len() as u64 + 1);
			assert_eq!(beacon.send_sequence(), peer.to_server.len() as u64);
			for (status, records, base) in
				[(server, &peer.to_server, 0), (beacon, &peer.to_beacon, 1)]
			{
				let highest = records
					.iter()
					.rposition(|record| record.consumed)
					.map_or(0, |i| i + 1);
				let skipped = records[..highest]
					.iter()
					.filter(|record| !record.consumed)
					.count();
				assert_eq!(status.receive_sequence(), highest as u64 + base);
				assert_eq!(usize::from(status.receive_cache_len()), skipped);
			}
		}
	}

	fn send(&mut self, peer: usize, direction: Direction, plaintext: &[u8]) {
		let peer = &mut self.peers[peer];
		let encrypted = match direction {
			Direction::ToServer => peer.beacon.encrypt_message(plaintext).unwrap(),
			Direction::ToBeacon => {
				let encrypted = self
					.server
					.encrypt_message(plaintext, peer.kid)
					.unwrap()
					.unwrap();
				self.generation += 1;
				self.attempts += 1;
				encrypted
			}
		};
		peer.records_mut(direction).push(Record {
			frame: encrypted.ciphertext,
			plaintext: plaintext.to_vec(),
			consumed: false,
		});
	}

	fn deliver(
		&mut self,
		peer: usize,
		direction: Direction,
		index: usize,
		tampered: bool,
		api: u8,
	) {
		let peer = &mut self.peers[peer];
		let length = peer.records(direction).len();
		if length == 0 {
			return;
		}
		let index = index % length;
		let record = &peer.records(direction)[index];
		// Histories stay below 50 outstanding records; capacity pressure has its own ratchet model.
		let expected = (!tampered && !record.consumed).then(|| record.plaintext.clone());
		let frame = if tampered {
			corrupt(&record.frame)
		} else {
			record.frame.clone()
		};
		let before_head = self.server.head();
		let before_snapshot = self.store.load().unwrap().as_bytes().to_vec();
		let output = match direction {
			Direction::ToServer => receive(&mut self.server, &frame, api).unwrap(),
			Direction::ToBeacon => peer
				.beacon
				.decrypt_message(&frame)
				.map(|message| message.plaintext),
		};
		assert_eq!(output, expected);
		if output.is_some() {
			peer.records_mut(direction)[index].consumed = true;
			if matches!(direction, Direction::ToServer) {
				self.generation += 1;
				self.attempts += 1;
			}
		}
		if output.is_none() || matches!(direction, Direction::ToBeacon) {
			assert_eq!(self.server.head(), before_head);
			assert_eq!(self.store.load().unwrap().as_bytes(), before_snapshot);
		}
	}

	fn restore_and_fence(&mut self, peer: usize) {
		let active = PersistentServer::restore(self.store.clone()).unwrap();
		self.generation += 1;
		self.attempts += 1;
		let old_head = self.server.head();
		let authoritative = active.head();
		let bytes = self.store.load().unwrap().as_bytes().to_vec();
		assert_eq!(
			self.server.snapshot().err(),
			Some(PersistenceError::StaleGeneration)
		);
		// Even a stale owner rejects malformed input without touching the trusted store.
		assert!(
			self.server
				.decrypt_message(b"invalid frame")
				.unwrap()
				.is_none()
		);
		assert!(!self.server.is_poisoned());
		assert_eq!(self.store.0.lock().unwrap().attempts, self.attempts);
		assert!(matches!(
			self.server
				.encrypt_message(b"withheld stale result", self.peers[peer].kid),
			Err(PersistenceError::StaleGeneration)
		));
		self.attempts += 1;
		assert!(self.server.is_poisoned());
		assert_eq!(self.server.head(), old_head);
		assert_eq!(self.store.0.lock().unwrap().head, Some(authoritative));
		assert_eq!(self.store.load().unwrap().as_bytes(), bytes);
		assert!(matches!(
			self.server.decrypt_message(b"invalid frame"),
			Err(PersistenceError::Poisoned)
		));
		self.server = active;
	}

	fn failed_commit_and_recover(
		&mut self,
		peer: usize,
		direction: Direction,
		payload: &[u8],
		api: u8,
	) {
		if matches!(direction, Direction::ToServer) {
			self.send(peer, direction, payload);
		}
		let before_head = self.server.head();
		let bytes = self.store.load().unwrap().as_bytes().to_vec();
		let statuses: Vec<_> = self
			.peers
			.iter()
			.map(|peer| self.server.ratchet_status(peer.kid))
			.collect();
		self.store.0.lock().unwrap().fail_next = true;
		// Rejection must leave an armed failure for the next accepted operation.
		let invalid = self.peers[peer]
			.to_server
			.last()
			.map_or_else(|| b"invalid".to_vec(), |record| corrupt(&record.frame));
		assert!(receive(&mut self.server, &invalid, api).unwrap().is_none());
		assert_eq!(self.server.head(), before_head);
		assert_eq!(self.store.0.lock().unwrap().attempts, self.attempts);
		assert!(self.store.0.lock().unwrap().fail_next);
		for (peer, status) in self.peers.iter().zip(&statuses) {
			assert_eq!(self.server.ratchet_status(peer.kid), *status);
		}
		let failed = match direction {
			Direction::ToServer => receive(
				&mut self.server,
				&self.peers[peer].to_server.last().unwrap().frame,
				api,
			)
			.map(|output| output.is_some()),
			Direction::ToBeacon => self
				.server
				.encrypt_message(payload, self.peers[peer].kid)
				.map(|output| output.is_some()),
		};
		assert_eq!(failed, Err(PersistenceError::StaleGeneration));
		self.attempts += 1;
		assert!(self.server.is_poisoned());
		assert_eq!(self.server.head(), before_head);
		assert_eq!(self.store.0.lock().unwrap().head, Some(before_head));
		assert_eq!(self.store.load().unwrap().as_bytes(), bytes);
		assert!(matches!(
			self.server.encrypt_message(payload, self.peers[peer].kid),
			Err(PersistenceError::Poisoned)
		));
		self.server = PersistentServer::restore(self.store.clone()).unwrap();
		self.generation += 1;
		self.attempts += 1;
		for (peer, status) in self.peers.iter().zip(statuses) {
			assert_eq!(self.server.ratchet_status(peer.kid), status);
		}
		// Recovery must resume the committed session, including the key withheld by failed CAS.
		match direction {
			Direction::ToServer => self.deliver(
				peer,
				direction,
				self.peers[peer].to_server.len() - 1,
				false,
				api,
			),
			Direction::ToBeacon => self.send(peer, direction, payload),
		}
		self.check();
	}
}

fn config() -> ProptestConfig {
	ProptestConfig {
		cases: std::env::var("PROPTEST_CASES")
			.ok()
			.and_then(|cases| cases.parse().ok())
			.unwrap_or(24),
		failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/proptest-regressions/persistence_properties.txt"
		)))),
		..ProptestConfig::default()
	}
}

proptest! {
	#![proptest_config(config())]

	#[test]
	fn committed_histories_survive_restoration_and_failed_cas(
		commands in proptest::collection::vec(command(), 0..25),
		payload in proptest::collection::vec(any::<u8>(), 1..65),
		peer in 0usize..2,
		api in 0u8..3,
	) {
		let mut history = History::new();
		// Every history starts with delayed records in both directions for both peers.
		for peer in 0..2 {
			for direction in [Direction::ToServer, Direction::ToBeacon] {
				for label in [b"first".as_slice(), b"second", b"third"] {
					history.send(peer, direction, label);
				}
				history.deliver(peer, direction, 2, false, api);
			}
		}
		for command in commands {
			match command {
				Command::Send(peer, direction, payload) => history.send(peer, direction, &payload),
				Command::Deliver(peer, direction, index, corrupt, api) => history.deliver(peer, direction, index, corrupt, api),
				Command::Restore(peer) => history.restore_and_fence(peer),
			}
			history.check();
		}
		history.failed_commit_and_recover(peer, Direction::ToServer, &payload, api);
		history.failed_commit_and_recover(1 - peer, Direction::ToBeacon, &payload, api);
		history.restore_and_fence(peer);
		history.check();
		for peer in 0..2 {
			for direction in [Direction::ToServer, Direction::ToBeacon] {
				for index in (0..history.peers[peer].records(direction).len()).rev() {
					history.deliver(peer, direction, index, false, api);
					history.deliver(peer, direction, index, false, api);
					history.check();
				}
			}
		}
		// Fresh traffic checks the live directional chains after consuming all saved receive keys.
		for after_restore in [false, true] {
			if after_restore {
				history.restore_and_fence(peer);
			}
			for peer in 0..2 {
				for direction in [Direction::ToServer, Direction::ToBeacon] {
					history.send(peer, direction, &payload);
					let index = history.peers[peer].records(direction).len() - 1;
					history.deliver(peer, direction, index, false, api);
					history.check();
				}
			}
		}
	}
}
