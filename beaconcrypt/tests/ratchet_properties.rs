// SPDX-License-Identifier: 0BSD

#![cfg(all(feature = "pqxdh", feature = "beacon", feature = "server"))]

use std::collections::{BTreeMap, BTreeSet};

use beaconcrypt::{Beacon, Decrypted, ProviderBeacon, ProviderServer, RatchetStatus, Server};
use beaconcrypt_parse::{CryptoFrame, decode_frame, encode_frame};
use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;

const SERVER_KID: u64 = 23;
const PEERS: usize = 2;
// These are protocol limits, deliberately independent of the implementation's planning helpers.
const SKIPPED_KEY_LIMIT: usize = 50;
const TAG_SIZE: usize = 16;
const COMMITMENT_SIZE: usize = 64;

#[derive(Clone, Copy, Debug)]
enum Direction {
	ToServer,
	ToBeacon,
}

impl Direction {
	fn index(self) -> usize {
		match self {
			Self::ToServer => 0,
			Self::ToBeacon => 1,
		}
	}
}

#[derive(Clone, Debug)]
enum Damage {
	Ciphertext { byte: usize, bit: u8 },
	Tag { byte: usize, bit: u8 },
	Commitment { byte: usize, bit: u8 },
	ZeroSequence,
	RelabelSequence,
	UnknownSender,
	Truncate(usize),
	Append(u8),
}

#[derive(Clone, Debug)]
enum Command {
	Send {
		peer: usize,
		direction: Direction,
		count: usize,
		payload: Vec<u8>,
	},
	Deliver {
		peer: usize,
		direction: Direction,
		frame: usize,
	},
	DamageAndRetry {
		peer: usize,
		direction: Direction,
		frame: usize,
		damage: Damage,
	},
	MisrouteAndRetry {
		peer: usize,
		direction: Direction,
		frame: usize,
	},
	ReflectAndRetry {
		peer: usize,
		direction: Direction,
		frame: usize,
	},
	Drain {
		peer: usize,
		direction: Direction,
		reverse: bool,
	},
}

#[derive(Clone)]
struct Frame {
	sequence: u64,
	plaintext: Vec<u8>,
	bytes: Vec<u8>,
}

// This model stores sequence sets, not keys or the production ratchet's slot layout.
struct Channel {
	sent: u64,
	high_water: u64,
	cached: BTreeSet<u64>,
	consumed: BTreeSet<u64>,
	frames: BTreeMap<u64, Frame>,
}

impl Channel {
	fn new(registration_record: bool) -> Self {
		let initial = u64::from(registration_record);
		Self {
			sent: initial,
			high_water: initial,
			cached: BTreeSet::new(),
			consumed: if registration_record {
				BTreeSet::from([1])
			} else {
				BTreeSet::new()
			},
			frames: BTreeMap::new(),
		}
	}

	fn can_deliver(&self, sequence: u64) -> bool {
		if self.consumed.contains(&sequence) {
			return false;
		}
		if sequence <= self.high_water {
			return self.cached.contains(&sequence);
		}
		// The future target itself is opened directly; only the skipped records need cache slots.
		let skipped = (sequence - self.high_water - 1) as usize;
		skipped <= SKIPPED_KEY_LIMIT && self.cached.len() + skipped <= SKIPPED_KEY_LIMIT
	}

	fn consume(&mut self, sequence: u64) {
		assert!(self.can_deliver(sequence));
		if sequence > self.high_water {
			self.cached.extend(self.high_water + 1..sequence);
			self.high_water = sequence;
		} else {
			assert!(self.cached.remove(&sequence));
		}
		assert!(self.consumed.insert(sequence));
	}

	fn select(&self, selector: usize) -> Option<Frame> {
		// Modulo keeps references usable when proptest removes sends while shrinking a history.
		let index = selector.checked_rem(self.frames.len())?;
		self.frames.values().nth(index).cloned()
	}
}

struct Network {
	server: Server,
	beacons: Vec<Beacon>,
	kids: Vec<u64>,
	channels: Vec<[Channel; 2]>,
}

impl Network {
	fn new() -> Self {
		let mut server = Server::new(SERVER_KID, Some(&[0x42; 32]));
		let mut beacons = Vec::new();
		let mut kids = Vec::new();
		for _ in 0..PEERS {
			let mut beacon = Beacon::new(SERVER_KID, server.identity_pk().as_bytes());
			let bundle = beacon.get_registration_bundle().unwrap();
			let pending = server.get_shared_secret(&bundle).unwrap();
			let response = server
				.build_registration_response(pending, Some(b"registered"))
				.unwrap();
			assert_eq!(
				beacon.finish_registration(&response.serialized).unwrap(),
				b"registered"
			);
			kids.push(response.kid);
			beacons.push(beacon);
		}
		let network = Self {
			server,
			beacons,
			kids,
			channels: (0..PEERS)
				.map(|_| [Channel::new(false), Channel::new(true)])
				.collect(),
		};
		network.check("registration");
		network
	}

	fn observations(&self) -> Vec<(RatchetStatus, RatchetStatus)> {
		(0..PEERS)
			.map(|peer| {
				(
					self.server.ratchet_status(self.kids[peer]).unwrap(),
					self.beacons[peer].ratchet_status().unwrap(),
				)
			})
			.collect()
	}

	fn check(&self, context: &str) {
		for (peer, (server, beacon)) in self.observations().into_iter().enumerate() {
			let [incoming, outgoing] = &self.channels[peer];
			for (status, send, receive) in
				[(server, outgoing, incoming), (beacon, incoming, outgoing)]
			{
				assert_eq!(
					status.send_sequence(),
					send.sent,
					"{context}: peer {peer}, send counter"
				);
				assert_eq!(
					status.receive_sequence(),
					receive.high_water,
					"{context}: peer {peer}, receive counter"
				);
				assert_eq!(
					usize::from(status.receive_cache_len()),
					receive.cached.len(),
					"{context}: peer {peer}, receive cache"
				);
				assert!(receive.cached.is_disjoint(&receive.consumed), "{context}");
			}
		}
	}

	fn send(
		&mut self,
		peer: usize,
		direction: Direction,
		count: usize,
		payload: &[u8],
		context: &str,
	) {
		for _ in 0..count {
			let encrypted = match direction {
				Direction::ToServer => self.beacons[peer].encrypt_message(payload),
				Direction::ToBeacon => self.server.encrypt_message(payload, self.kids[peer]),
			};
			if payload.is_empty() {
				assert!(
					encrypted.is_none(),
					"{context}: empty plaintext was accepted"
				);
			} else {
				let encrypted = encrypted.expect("bounded nonempty plaintext must encrypt");
				let channel = &mut self.channels[peer][direction.index()];
				channel.sent += 1;
				assert_eq!(encrypted.seq, channel.sent, "{context}");
				assert!(
					channel
						.frames
						.insert(
							encrypted.seq,
							Frame {
								sequence: encrypted.seq,
								plaintext: payload.to_vec(),
								bytes: encrypted.ciphertext,
							}
						)
						.is_none(),
					"{context}: reused send sequence"
				);
			}
			self.check(context);
		}
	}

	fn receive(&mut self, peer: usize, direction: Direction, bytes: &[u8]) -> Option<Decrypted> {
		match direction {
			Direction::ToServer => self.server.decrypt_message(bytes),
			Direction::ToBeacon => self.beacons[peer].decrypt_message(bytes),
		}
	}

	fn reject(&mut self, peer: usize, direction: Direction, bytes: &[u8], context: &str) {
		let before = self.observations();
		assert!(
			self.receive(peer, direction, bytes).is_none(),
			"{context}: invalid frame accepted"
		);
		assert_eq!(
			self.observations(),
			before,
			"{context}: rejection changed a peer's state"
		);
		self.check(context);
	}

	fn deliver(&mut self, peer: usize, direction: Direction, frame: &Frame, context: &str) {
		let expected = self.channels[peer][direction.index()].can_deliver(frame.sequence);
		let before = self.observations();
		let actual = self.receive(peer, direction, &frame.bytes);
		assert_eq!(
			actual.is_some(),
			expected,
			"{context}: authentic sequence {}",
			frame.sequence
		);
		if let Some(opened) = actual {
			assert_eq!(opened.seq, frame.sequence, "{context}");
			assert_eq!(opened.plaintext, frame.plaintext, "{context}");
			let sender = match direction {
				Direction::ToServer => self.kids[peer],
				Direction::ToBeacon => SERVER_KID,
			};
			assert_eq!(opened.key_id, sender, "{context}");
			self.channels[peer][direction.index()].consume(frame.sequence);
		} else {
			assert_eq!(
				self.observations(),
				before,
				"{context}: replay or gap rejection changed state"
			);
		}
		self.check(context);
	}

	fn drain(&mut self, peer: usize, direction: Direction, reverse: bool, context: &str) {
		let mut frames: Vec<_> = self.channels[peer][direction.index()]
			.frames
			.values()
			.cloned()
			.collect();
		if reverse {
			frames.reverse();
		}
		for frame in frames {
			self.deliver(peer, direction, &frame, context);
		}
	}

	fn run(&mut self, command: &Command, context: &str) {
		match command {
			Command::Send {
				peer,
				direction,
				count,
				payload,
			} => self.send(*peer, *direction, *count, payload, context),
			Command::Drain {
				peer,
				direction,
				reverse,
			} => self.drain(*peer, *direction, *reverse, context),
			Command::Deliver {
				peer,
				direction,
				frame,
			}
			| Command::DamageAndRetry {
				peer,
				direction,
				frame,
				..
			}
			| Command::MisrouteAndRetry {
				peer,
				direction,
				frame,
			}
			| Command::ReflectAndRetry {
				peer,
				direction,
				frame,
			} => {
				let Some(frame) = self.channels[*peer][direction.index()].select(*frame) else {
					return;
				};
				match command {
					Command::DamageAndRetry { damage, .. } => {
						self.reject(
							*peer,
							*direction,
							&damage_frame(&frame.bytes, damage),
							context,
						);
					}
					Command::MisrouteAndRetry { .. } => {
						let other = (*peer + 1) % PEERS;
						let bytes = match direction {
							Direction::ToServer => {
								let parsed = decode_frame(&frame.bytes).unwrap();
								encode(CryptoFrame {
									key_id: self.kids[other],
									..parsed
								})
							}
							Direction::ToBeacon => frame.bytes.clone(),
						};
						self.reject(other, *direction, &bytes, context);
					}
					Command::ReflectAndRetry { .. } => {
						let reflected = match direction {
							Direction::ToServer => Direction::ToBeacon,
							Direction::ToBeacon => Direction::ToServer,
						};
						self.reject(*peer, reflected, &frame.bytes, context);
						let parsed = decode_frame(&frame.bytes).unwrap();
						let destination = &self.channels[*peer][reflected.index()];
						let seq = if destination.can_deliver(parsed.seq) {
							parsed.seq
						} else {
							destination.high_water + 1
						};
						let key_id = match reflected {
							Direction::ToServer => self.kids[*peer],
							Direction::ToBeacon => SERVER_KID,
						};
						// Route to the opposite ratchet with an admissible sequence, so sender or
						// replay prechecks cannot hide missing directional authentication.
						let routed = encode(CryptoFrame {
							seq,
							key_id,
							..parsed
						});
						self.reject(*peer, reflected, &routed, context);
					}
					_ => {}
				}
				self.deliver(*peer, *direction, &frame, context);
			}
		}
	}

	fn finish(mut self) {
		// In sequence order every outstanding authentic frame must remain recoverable, including
		// keys whose bytes could have been damaged without changing the public status counters.
		for peer in 0..PEERS {
			for direction in [Direction::ToServer, Direction::ToBeacon] {
				self.drain(peer, direction, false, "final authentic retries");
				let channel = &self.channels[peer][direction.index()];
				assert!(channel.cached.is_empty());
				assert!(
					channel
						.frames
						.keys()
						.all(|seq| channel.consumed.contains(seq))
				);
				self.drain(peer, direction, true, "final replay checks");
			}
		}
		// Old frames exercise cached material. Fresh traffic also checks the live send and
		// receive chains after every rejection and replay in the generated history.
		for peer in 0..PEERS {
			for direction in [Direction::ToServer, Direction::ToBeacon] {
				self.send(
					peer,
					direction,
					1,
					b"continued operation",
					"fresh send after history",
				);
				let frame = self.channels[peer][direction.index()]
					.frames
					.last_key_value()
					.unwrap()
					.1
					.clone();
				self.deliver(peer, direction, &frame, "fresh delivery after history");
			}
		}
	}
}

fn encode(frame: CryptoFrame<'_>) -> Vec<u8> {
	let mut bytes = vec![0; frame.cipher_text.len() + 64];
	let written = encode_frame(frame, &mut bytes);
	assert_ne!(written, 0);
	bytes.truncate(written);
	bytes
}

fn damage_frame(bytes: &[u8], damage: &Damage) -> Vec<u8> {
	let mut frame = decode_frame(bytes).unwrap();
	let mut payload = frame.cipher_text.to_vec();
	let plaintext_len = payload.len() - TAG_SIZE - COMMITMENT_SIZE;
	match *damage {
		Damage::Ciphertext { byte, bit } => payload[byte % plaintext_len] ^= 1 << bit,
		Damage::Tag { byte, bit } => payload[plaintext_len + byte % TAG_SIZE] ^= 1 << bit,
		Damage::Commitment { byte, bit } => {
			payload[plaintext_len + TAG_SIZE + byte % COMMITMENT_SIZE] ^= 1 << bit
		}
		Damage::ZeroSequence => frame.seq = 0,
		Damage::RelabelSequence => frame.seq += 1,
		Damage::UnknownSender => frame.key_id = u64::MAX,
		Damage::Truncate(cut) => return bytes[..cut % bytes.len()].to_vec(),
		Damage::Append(byte) => {
			let mut appended = bytes.to_vec();
			appended.push(byte);
			return appended;
		}
	}
	frame.cipher_text = &payload;
	encode(frame)
}

fn direction() -> impl Strategy<Value = Direction> {
	prop_oneof![Just(Direction::ToServer), Just(Direction::ToBeacon)]
}

fn damage() -> impl Strategy<Value = Damage> {
	prop_oneof![
		(any::<u16>(), 0u8..8).prop_map(|(byte, bit)| Damage::Ciphertext {
			byte: usize::from(byte),
			bit
		}),
		(any::<u16>(), 0u8..8).prop_map(|(byte, bit)| Damage::Tag {
			byte: usize::from(byte),
			bit
		}),
		(any::<u16>(), 0u8..8).prop_map(|(byte, bit)| Damage::Commitment {
			byte: usize::from(byte),
			bit
		}),
		Just(Damage::ZeroSequence),
		Just(Damage::RelabelSequence),
		Just(Damage::UnknownSender),
		any::<u16>().prop_map(|cut| Damage::Truncate(usize::from(cut))),
		any::<u8>().prop_map(Damage::Append),
	]
}

fn command() -> impl Strategy<Value = Command> {
	let target = || (0..PEERS, direction(), any::<u16>().prop_map(usize::from));
	prop_oneof![
		5 => (0..PEERS, direction(), prop_oneof![8 => 1usize..4, 1 => 49usize..53], proptest::collection::vec(any::<u8>(), 0..65))
			.prop_map(|(peer, direction, count, payload)| Command::Send { peer, direction, count, payload }),
		4 => target().prop_map(|(peer, direction, frame)| Command::Deliver { peer, direction, frame }),
		4 => (target(), damage()).prop_map(|((peer, direction, frame), damage)| Command::DamageAndRetry { peer, direction, frame, damage }),
		2 => target().prop_map(|(peer, direction, frame)| Command::MisrouteAndRetry { peer, direction, frame }),
		1 => target().prop_map(|(peer, direction, frame)| Command::ReflectAndRetry { peer, direction, frame }),
		2 => (0..PEERS, direction(), any::<bool>()).prop_map(|(peer, direction, reverse)| Command::Drain { peer, direction, reverse }),
	]
}

fn config() -> ProptestConfig {
	let mut config = ProptestConfig::default();
	if std::env::var_os("PROPTEST_CASES").is_none() {
		config.cases = 24;
	}
	config.failure_persistence = Some(Box::new(FileFailurePersistence::Direct(concat!(
		env!("CARGO_MANIFEST_DIR"),
		"/proptest-regressions/ratchet_properties.txt"
	))));
	config
}

proptest! {
	#![proptest_config(config())]

	#[test]
	fn generated_network_histories_match_the_sequence_set_model(commands in proptest::collection::vec(command(), 1..49)) {
		let mut network = Network::new();
		for peer in 0..PEERS {
			for direction in [Direction::ToServer, Direction::ToBeacon] {
				network.send(peer, direction, 1, b"first application frame", "initial sends");
			}
		}
		for (step, command) in commands.iter().enumerate() {
			network.run(command, &format!("step {step}: {command:?}"));
		}
		network.finish();
	}

	#[test]
	fn receive_capacity_boundaries_preserve_retry_and_cached_keys(
		peer in 0..PEERS,
		direction in direction(),
		skipped in 49usize..52,
		payload in proptest::collection::vec(any::<u8>(), 1..65),
		damage in damage(),
	) {
		let mut network = Network::new();
		network.send(peer, direction, skipped + 3, &payload, "boundary burst");
		let initial = network.channels[peer][direction.index()].high_water;
		let target = network.channels[peer][direction.index()].frames[&(initial + skipped as u64 + 1)].clone();
		network.reject(peer, direction, &damage_frame(&target.bytes, &damage), "damaged boundary frame");
		network.deliver(peer, direction, &target, "boundary delivery");
		if skipped > SKIPPED_KEY_LIMIT {
			let first = network.channels[peer][direction.index()].frames[&(initial + 1)].clone();
			network.deliver(peer, direction, &first, "advance to admit the previously excessive gap");
			network.deliver(peer, direction, &target, "retry boundary delivery");
		}
		// At a full skipped-key cache, the next target remains admissible without another slot.
		let next = network.channels[peer][direction.index()].frames[&(target.sequence + 1)].clone();
		network.deliver(peer, direction, &next, "next target with populated cache");
		network.send(peer, direction, 1, &payload, "one further target");
		let further = network.channels[peer][direction.index()].frames[&(target.sequence + 3)].clone();
		network.deliver(peer, direction, &further, "one additional skipped key");
		if skipped >= SKIPPED_KEY_LIMIT {
			let cached = *network.channels[peer][direction.index()].cached.first().unwrap();
			let cached = network.channels[peer][direction.index()].frames[&cached].clone();
			network.deliver(peer, direction, &cached, "free a skipped-key slot");
			network.deliver(peer, direction, &further, "retry after freeing capacity");
		}
		network.finish();
	}
}
