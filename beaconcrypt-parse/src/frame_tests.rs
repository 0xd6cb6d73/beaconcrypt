// SPDX-License-Identifier: 0BSD

extern crate std;

use std::{vec, vec::Vec};

use proptest::prelude::*;

use super::{
	CryptoFrame, MAX_MESSAGE_SIZE, decode_frame, encode_frame, encoded_frame_len, transport,
};

const BOUNDARIES: &[u64] = &[
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

/// Preserve the previous production decoder as a private differential reference.
fn generated_decode(input: &[u8]) -> Option<CryptoFrame<'_>> {
	super::preflight(input, &[0x85, 1, 2], &[0, 0, 2])?;
	match transport::validate_and_parse_cryptoframe(input) {
		transport::option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t·::Some {
			v: (frame, []),
		} => Some(CryptoFrame {
			seq: frame.seq,
			key_id: frame.key_id,
			cipher_text: frame.cipher_text,
		}),
		_ => None,
	}
}

fn generated_encode(frame: CryptoFrame<'_>) -> Vec<u8> {
	let length = encoded_frame_len(frame.seq, frame.key_id, frame.cipher_text.len()).unwrap();
	let mut output = vec![0; length];
	assert_eq!(
		transport::serialize_cryptoframe(
			transport::cryptoframe {
				seq: frame.seq,
				key_id: frame.key_id,
				cipher_text: frame.cipher_text,
			},
			&mut output,
		),
		length
	);
	output
}

fn compare(frame: CryptoFrame<'_>) -> Vec<u8> {
	let expected = generated_encode(frame);
	let mut output = vec![0xa7; expected.len() + 3];
	assert_eq!(encode_frame(frame, &mut output), expected.len());
	assert_eq!(&output[..expected.len()], expected);
	assert_eq!(&output[expected.len()..], &[0xa7; 3]);
	assert!(decode_frame(&expected) == Some(frame));
	assert!(decode_frame(&expected) == generated_decode(&expected));
	expected
}

#[test]
fn production_frame_codec_matches_generated_codec_at_every_width_boundary() {
	for length in [0, 1, 23, 24, 255, 256, 65_535, 65_536] {
		let payload: Vec<_> = (0..length).map(|index| index as u8).collect();
		for &seq in BOUNDARIES {
			for &key_id in BOUNDARIES {
				compare(CryptoFrame {
					seq,
					key_id,
					cipher_text: &payload,
				});
			}
		}
	}
}

#[test]
fn canonicality_truncation_and_exact_consumption_match_generated_decoder() {
	for &seq in BOUNDARIES {
		for &key_id in BOUNDARIES {
			let wire = compare(CryptoFrame {
				seq,
				key_id,
				cipher_text: &[0xff, 0x80, 0],
			});
			for cut in 0..wire.len() {
				assert!(decode_frame(&wire[..cut]) == generated_decode(&wire[..cut]));
				assert!(decode_frame(&wire[..cut]).is_none());
			}
			for index in 0..wire.len() {
				for byte in [0, 23, 24, 25, 26, 27, 28, 31, 32, 64, 0x80, 0xff] {
					let mut changed = wire.clone();
					changed[index] = byte;
					assert!(decode_frame(&changed) == generated_decode(&changed));
				}
			}
			for suffix in [&[0][..], &[0xff][..], wire.as_slice()] {
				let mut extended = wire.clone();
				extended.extend_from_slice(suffix);
				assert!(decode_frame(&extended).is_none());
				assert!(decode_frame(&extended) == generated_decode(&extended));
			}
		}
	}
	for malformed in [
		&[0x85, 1, 2, 0x18, 0, 0, 0x40][..],
		&[0x85, 1, 2, 0, 0x19, 0, 24, 0x40][..],
		&[0x85, 1, 2, 0, 0, 0x58, 0][..],
		&[0x85, 1, 2, 0, 0, 0x5f, 0xff][..],
		&[0x85, 1, 2, 0, 0, 0x80][..],
	] {
		assert!(decode_frame(malformed).is_none());
		assert!(decode_frame(malformed) == generated_decode(malformed));
	}
}

#[test]
fn complete_message_limit_is_inclusive_and_matches_generated_codec() {
	let payload = vec![0x57; MAX_MESSAGE_SIZE - 10];
	let mut wire = compare(CryptoFrame {
		seq: 0,
		key_id: 0,
		cipher_text: &payload,
	});
	assert_eq!(wire.len(), MAX_MESSAGE_SIZE);
	wire.push(0);
	// Make the larger frame canonical too, so the size gate is tested independently of trailing-byte rejection.
	wire[6..10].copy_from_slice(&((payload.len() + 1) as u32).to_be_bytes());
	assert!(decode_frame(&wire).is_none());
	assert!(decode_frame(&wire) == generated_decode(&wire));
	let mut short = [0xa7; 5];
	assert_eq!(
		encode_frame(
			CryptoFrame {
				seq: 0,
				key_id: 0,
				cipher_text: &payload
			},
			&mut short
		),
		0
	);
	assert_eq!(short, [0xa7; 5]);
}

proptest! {
	#![proptest_config(ProptestConfig::with_cases(1024))]

	#[test]
	fn arbitrary_frame_roundtrips_match_generated_codec(seq: u64, key_id: u64, payload in prop::collection::vec(any::<u8>(), 0..4096)) {
		compare(CryptoFrame { seq, key_id, cipher_text: &payload });
	}

	#[test]
	fn arbitrary_inputs_match_generated_complete_decoder(input in prop::collection::vec(any::<u8>(), 0..256)) {
		prop_assert!(decode_frame(&input) == generated_decode(&input));
	}
}
