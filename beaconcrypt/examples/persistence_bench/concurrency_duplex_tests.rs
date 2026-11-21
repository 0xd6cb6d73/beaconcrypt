// SPDX-License-Identifier: 0BSD

use super::super::{Arm, Config, Fixture};

#[test]
fn pregenerated_receives_remain_valid_during_interleaved_server_sends() {
	for arm in [Arm::Snapshot, Arm::Row, Arm::Cached] {
		let directory = tempfile::tempdir().unwrap();
		let config = Config {
			active_peers: Some(2),
			warmup_messages: 1,
			..Config::default()
		};
		let mut fixture =
			Fixture::new(arm, directory.path().join("duplex.sqlite"), 2, &config).unwrap();
		let send_sequences = fixture.send_sequences.clone();
		let receive_sequences = fixture.receive_sequences.clone();
		let mut inputs = Vec::new();
		for peer in 0..2 {
			let mut frames = Vec::new();
			for index in 0..32 {
				let plaintext =
					vec![(index + peer) as u8; if index % 8 == 0 { 65_536 } else { 64 }];
				let frame = fixture.beacons[peer].encrypt_message(&plaintext).unwrap();
				assert_eq!(frame.seq, receive_sequences[peer] + index as u64 + 1);
				frames.push((frame.ciphertext, plaintext));
			}
			inputs.push(frames);
		}
		let mut outgoing = Vec::new();
		for index in 0..32 {
			for peer in 0..2 {
				let plaintext =
					vec![(index + peer + 73) as u8; if index % 8 == 0 { 65_536 } else { 64 }];
				let sent = fixture
					.server
					.encrypt(&plaintext, fixture.kids[peer])
					.unwrap();
				assert_eq!(sent.key_id, fixture.kids[peer]);
				assert_eq!(sent.seq, send_sequences[peer] + index as u64 + 1);
				outgoing.push((peer, sent, plaintext));
				let received = fixture.server.decrypt(&inputs[peer][index].0).unwrap();
				assert_eq!(received.key_id, fixture.kids[peer]);
				assert_eq!(received.seq, receive_sequences[peer] + index as u64 + 1);
				assert_eq!(received.plaintext, inputs[peer][index].1);
			}
		}
		// Delaying this client-side verification cannot change the prepared receive chain.
		for (peer, sent, plaintext) in outgoing {
			let received = fixture.beacons[peer]
				.decrypt_message(&sent.ciphertext)
				.unwrap();
			assert_eq!(received.plaintext, plaintext);
			assert_eq!(received.seq, sent.seq);
		}
	}
}
