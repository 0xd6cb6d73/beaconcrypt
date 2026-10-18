// SPDX-License-Identifier: 0BSD

extern crate std;

use std::vec;
use std::vec::Vec;

use super::{preflight, primitive_argument};

type Shape = (&'static [u8], &'static [u8], &'static [u8]);
const SHAPES: &[Shape] = &[
	(&[0x85, 1, 2], &[0, 0, 2], &[0x85, 1, 2, 0, 0, 0x40]),
	(
		&[0x86, 1, 0],
		&[2, 2, 2, 2],
		&[0x86, 1, 0, 0x40, 0x40, 0x40, 0x40],
	),
	(
		&[0x87, 1, 1],
		&[2, 2, 2, 2, 0],
		&[0x87, 1, 1, 0x40, 0x40, 0x40, 0x40, 0],
	),
];

fn replace(input: &[u8], index: usize, value: &[u8]) -> Vec<u8> {
	let mut result = input[..index].to_vec();
	result.extend_from_slice(value);
	result.extend_from_slice(&input[index + 1..]);
	result
}

#[test]
fn gate_admits_flat_shapes_and_skips_arbitrary_byte_string_contents() {
	for &(prefix, fields, wire) in SHAPES {
		assert_eq!(preflight(wire, prefix, fields), Some(()));
		for (index, &major) in fields.iter().enumerate() {
			if major == 2 {
				// The payload resembles a nested map, but is opaque inside a byte string.
				let changed = replace(wire, 3 + index, &[0x46, 0xa1, 0xa1, 0x80, 0x80, 0x80, 0x80]);
				assert_eq!(preflight(&changed, prefix, fields), Some(()));
			}
		}
	}
}

#[test]
fn gate_rejects_containers_tags_indefinite_and_other_unexpected_fields() {
	let invalid: &[&[u8]] = &[
		&[0x80],
		&[0xa0],
		&[0xc0, 0],
		&[0x9f, 0xff],
		&[0xbf, 0xff],
		&[0x5f, 0x40, 0xff],
		&[0xf6],
		&[0x20],
		&[0x60],
		&[0x1c],
		&[0x5c],
		&[0xff],
	];
	for &(prefix, fields, wire) in SHAPES {
		for index in 0..fields.len() {
			for value in invalid {
				let changed = replace(wire, 3 + index, value);
				assert_eq!(
					preflight(&changed, prefix, fields),
					None,
					"field {index}: {value:02x?}"
				);
			}
			let wrong_primitive = if fields[index] == 2 {
				&[0][..]
			} else {
				&[0x40][..]
			};
			assert_eq!(
				preflight(&replace(wire, 3 + index, wrong_primitive), prefix, fields),
				None
			);
		}
	}
}

#[test]
fn gate_requires_the_fixed_prefix_all_fields_and_exact_consumption() {
	for &(prefix, fields, wire) in SHAPES {
		for cut in 0..wire.len() {
			assert_eq!(preflight(&wire[..cut], prefix, fields), None);
		}
		for index in 0..prefix.len() {
			let mut changed = wire.to_vec();
			changed[index] ^= 1;
			assert_eq!(preflight(&changed, prefix, fields), None);
		}
		for suffix in [&[0][..], &[0xff][..], wire] {
			let mut extended = wire.to_vec();
			extended.extend_from_slice(suffix);
			assert_eq!(preflight(&extended, prefix, fields), None);
		}
	}
}

#[test]
fn primitive_arguments_preserve_unsigned_values_and_the_remaining_input() {
	for major in [0, 2] {
		for value in 0..=23 {
			assert_eq!(
				primitive_argument(&[major << 5 | value, 0xee], major),
				Some((u64::from(value), &[0xee][..]))
			);
		}
		for (argument, expected) in [
			(&[24, 0xab][..], 0xab),
			(&[25, 0xab, 0xcd][..], 0xabcd),
			(&[26, 0x89, 0xab, 0xcd, 0xef][..], 0x89abcdef),
			(
				&[27, 1, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef][..],
				0x0123456789abcdef,
			),
			(&[27, 255, 255, 255, 255, 255, 255, 255, 255][..], u64::MAX),
		] {
			let mut input = argument.to_vec();
			input[0] |= major << 5;
			input.push(0xee);
			assert_eq!(
				primitive_argument(&input, major),
				Some((expected, &[0xee][..]))
			);
		}
	}
}

#[test]
fn primitive_arguments_reject_truncated_reserved_indefinite_and_wrong_major_headers() {
	for major in [0, 2] {
		assert_eq!(primitive_argument(&[], major), None);
		for (information, width) in [(24, 1), (25, 2), (26, 4), (27, 8)] {
			let mut input = vec![major << 5 | information];
			for _ in 0..width {
				assert_eq!(primitive_argument(&input, major), None);
				input.push(0);
			}
		}
		for information in 28..=31 {
			assert_eq!(primitive_argument(&[major << 5 | information], major), None);
		}
		for wrong_major in [0, 1, 2, 3, 4, 5, 6, 7] {
			if wrong_major != major {
				assert_eq!(primitive_argument(&[wrong_major << 5], major), None);
			}
		}
	}
}

#[test]
fn gate_checks_byte_lengths_without_overflow() {
	for (header, length) in [
		(&[0x40][..], 0),
		(&[0x57][..], 23),
		(&[0x58, 24][..], 24),
		(&[0x58, 255][..], 255),
		(&[0x59, 1, 0][..], 256),
		(&[0x59, 255, 255][..], 65_535),
		(&[0x5a, 0, 1, 0, 0][..], 65_536),
		(&[0x5b, 0, 0, 0, 0, 0, 1, 0, 0][..], 65_536),
	] {
		let mut input = header.to_vec();
		input.resize(header.len() + length, 0xa1);
		assert_eq!(preflight(&input, &[], &[2]), Some(()));
		if length > 0 {
			assert_eq!(preflight(&input[..input.len() - 1], &[], &[2]), None);
		}
		input.push(0);
		assert_eq!(preflight(&input, &[], &[2]), None);
	}
	for impossible in [u64::MAX, usize::MAX as u64, 1 << 32, 1 << 63] {
		let mut input = vec![0x5b];
		input.extend_from_slice(&impossible.to_be_bytes());
		assert_eq!(preflight(&input, &[], &[2]), None);
	}
}

#[test]
fn generated_validation_retains_responsibility_for_minimal_primitive_encodings() {
	let frame = [0x85, 1, 2, 0x18, 0, 0, 0x58, 0];
	assert_eq!(preflight(&frame, &[0x85, 1, 2], &[0, 0, 2]), Some(()));
	assert!(super::decode_frame(&frame).is_none());
}
