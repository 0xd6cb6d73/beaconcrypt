// SPDX-License-Identifier: 0BSD

use beaconcrypt_parse::{
	CryptoFrame, MAX_MESSAGE_SIZE, decode_frame, encode_frame, encode_frame_parts,
	encoded_frame_len,
};
use proptest::prelude::*;

const INTEGERS: &[u64] = &[
	0,
	1,
	23,
	24,
	255,
	256,
	65_535,
	65_536,
	u32::MAX as u64,
	u32::MAX as u64 + 1,
	u64::MAX,
];

fn generated_frame(sequence: u64, key_id: u64, payload: &[u8]) -> Vec<u8> {
	let mut output = vec![0; encoded_frame_len(sequence, key_id, payload.len()).unwrap()];
	let length = encode_frame(
		CryptoFrame {
			seq: sequence,
			key_id,
			cipher_text: payload,
		},
		&mut output,
	);
	assert_eq!(length, output.len());
	output
}

fn assert_parts(sequence: u64, key_id: u64, payload: &[u8], split: usize) {
	let expected = generated_frame(sequence, key_id, payload);
	let mut output = vec![0xa7; expected.len() + 5];
	let parts = [
		&[][..],
		&payload[..split],
		&[][..],
		&payload[split..],
		&[][..],
	];
	assert_eq!(
		encode_frame_parts(sequence, key_id, &parts, &mut output),
		expected.len()
	);
	assert_eq!(&output[..expected.len()], expected);
	assert_eq!(&output[expected.len()..], &[0xa7; 5]);
	let decoded = decode_frame(&output[..expected.len()]).unwrap();
	assert_eq!(decoded.seq, sequence);
	assert_eq!(decoded.key_id, key_id);
	assert_eq!(decoded.cipher_text, payload);
}

#[test]
fn borrowed_parts_match_generated_frames_at_every_integer_and_length_boundary() {
	for length in [0usize, 1, 23, 24, 255, 256, 65_535, 65_536] {
		let payload: Vec<u8> = (0..length).map(|index| index as u8).collect();
		for &sequence in INTEGERS {
			for &key_id in INTEGERS {
				for split in [0, length / 2, length.saturating_sub(16), length] {
					assert_parts(sequence, key_id, &payload, split);
				}
			}
		}
	}
	for length in 0..=81 {
		let payload = vec![0x57; length];
		for split in 0..=length {
			assert_parts(24, 256, &payload, split);
		}
	}
}

#[test]
fn undersized_or_oversized_frames_leave_output_untouched() {
	let payload = [0x37; 81];
	let length = encoded_frame_len(u64::MAX, u64::MAX, payload.len()).unwrap();
	for capacity in 0..length {
		let mut output = vec![0x9a; capacity];
		assert_eq!(
			encode_frame_parts(
				u64::MAX,
				u64::MAX,
				&[&payload[..16], &payload[16..]],
				&mut output
			),
			0
		);
		assert_eq!(output, vec![0x9a; capacity]);
	}
	let chunk = [0; 1024];
	let parts = vec![chunk.as_slice(); MAX_MESSAGE_SIZE / chunk.len() + 1];
	let mut output = [0x9a; 16];
	assert_eq!(encode_frame_parts(0, 0, &parts, &mut output), 0);
	assert_eq!(output, [0x9a; 16]);
}

#[test]
fn empty_parts_encode_the_same_empty_byte_string_as_generated_frames() {
	let expected = generated_frame(0, 0, &[]);
	let mut output = vec![0; expected.len()];
	assert_eq!(encode_frame_parts(0, 0, &[], &mut output), expected.len());
	assert_eq!(output, expected);
}

#[test]
fn complete_message_limit_is_inclusive_for_borrowed_parts() {
	// The prefix, two small integers, and five-byte byte-string header occupy ten bytes.
	let payload = vec![0x57; MAX_MESSAGE_SIZE - 10];
	let expected = generated_frame(0, 0, &payload);
	assert_eq!(expected.len(), MAX_MESSAGE_SIZE);
	let split = payload.len() - 80;
	let mut output = vec![0xa7; expected.len()];
	assert_eq!(
		encode_frame_parts(0, 0, &[&payload[..split], &payload[split..]], &mut output),
		MAX_MESSAGE_SIZE
	);
	assert_eq!(output, expected);
	let mut untouched = [0xa7; 16];
	assert_eq!(
		encode_frame_parts(0, 0, &[&payload, &[1]], &mut untouched),
		0
	);
	assert_eq!(untouched, [0xa7; 16]);
}

proptest! {
	#![proptest_config(ProptestConfig::with_cases(64))]
	#[test]
	fn random_partitioning_preserves_generated_encoding(
		sequence in any::<u64>(),
		key_id in any::<u64>(),
		payload in prop::collection::vec(any::<u8>(), 0..4097),
		cuts in prop::collection::vec(any::<usize>(), 0..16),
	) {
		let mut cuts: Vec<_> = cuts.into_iter().map(|cut| cut % (payload.len() + 1)).collect();
		cuts.extend([0, payload.len()]);
		cuts.sort_unstable();
		let parts: Vec<_> = cuts.windows(2).map(|pair| &payload[pair[0]..pair[1]]).collect();
		let expected = generated_frame(sequence, key_id, &payload);
		let mut actual = vec![0; expected.len()];
		prop_assert_eq!(encode_frame_parts(sequence, key_id, &parts, &mut actual), expected.len());
		prop_assert_eq!(actual, expected);
	}
}
