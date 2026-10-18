// SPDX-License-Identifier: 0BSD

use beaconcrypt_parse::{
	CryptoFrame, InitKex, KexResponse, MAX_MESSAGE_SIZE, decode_frame, decode_init,
	decode_response, encode_frame, encode_init, encode_response, encoded_frame_len,
	encoded_init_len, encoded_response_len,
};

const UINT_BOUNDARIES: &[u64] = &[
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
const BYTE_LENGTH_BOUNDARIES: &[usize] = &[0, 1, 23, 24, 255, 256, 65_535, 65_536];

fn frame_bytes(value: CryptoFrame<'_>) -> Vec<u8> {
	let expected = encoded_frame_len(value.seq, value.key_id, value.cipher_text.len()).unwrap();
	let mut out = vec![0; expected];
	assert_eq!(encode_frame(value, &mut out), expected);
	out
}

fn init_bytes(value: InitKex<'_>) -> Vec<u8> {
	let expected = encoded_init_len([
		value.identity_key.len(),
		value.pre_key.len(),
		value.one_time_key.len(),
		value.pq_key.len(),
	])
	.unwrap();
	let mut out = vec![0; expected];
	assert_eq!(encode_init(value, &mut out), expected);
	out
}

fn response_bytes(value: KexResponse<'_>) -> Vec<u8> {
	let expected = encoded_response_len(
		[
			value.identity_key.len(),
			value.ephemeral_key.len(),
			value.kem_cipher_text.len(),
			value.app_cipher_text.len(),
		],
		value.key_id,
	)
	.unwrap();
	let mut out = vec![0; expected];
	assert_eq!(encode_response(value, &mut out), expected);
	out
}

#[derive(Clone, Copy, Debug)]
enum Kind {
	Frame,
	Init,
	Response,
}

impl Kind {
	fn minimal(self) -> &'static [u8] {
		match self {
			Self::Frame => &[0x85, 1, 2, 0, 0, 0x40],
			Self::Init => &[0x86, 1, 0, 0x40, 0x40, 0x40, 0x40],
			Self::Response => &[0x87, 1, 1, 0x40, 0x40, 0x40, 0x40, 0],
		}
	}

	fn byte_fields(self) -> &'static [usize] {
		match self {
			Self::Frame => &[5],
			Self::Init | Self::Response => &[3, 4, 5, 6],
		}
	}

	fn integer_fields(self) -> &'static [usize] {
		match self {
			Self::Frame => &[3, 4],
			Self::Init => &[],
			Self::Response => &[7],
		}
	}

	fn accepts(self, input: &[u8]) -> bool {
		match self {
			Self::Frame => decode_frame(input).is_some(),
			Self::Init => decode_init(input).is_some(),
			Self::Response => decode_response(input).is_some(),
		}
	}

	fn reject(self, reason: &str, input: &[u8]) {
		assert!(
			!self.accepts(input),
			"{self:?} accepted {reason}: {input:02x?}"
		);
	}
}

const KINDS: &[Kind] = &[Kind::Frame, Kind::Init, Kind::Response];

fn replacing(input: &[u8], offset: usize, replacement: &[u8]) -> Vec<u8> {
	let mut changed = input[..offset].to_vec();
	changed.extend_from_slice(replacement);
	changed.extend_from_slice(&input[offset + 1..]);
	changed
}

#[test]
fn hand_authored_cbor_matches_the_schema_and_encoder() {
	let frame = CryptoFrame {
		seq: 24,
		key_id: 256,
		cipher_text: &[0xde, 0xad, 0xbe],
	};
	let wire = [0x85, 1, 2, 0x18, 0x18, 0x19, 1, 0, 0x43, 0xde, 0xad, 0xbe];
	assert!(decode_frame(&wire) == Some(frame));
	assert_eq!(frame_bytes(frame), wire);

	let init = InitKex {
		identity_key: &[0x11],
		pre_key: &[0x22, 0x23],
		one_time_key: &[],
		pq_key: &[0x33],
	};
	let wire = [0x86, 1, 0, 0x41, 0x11, 0x42, 0x22, 0x23, 0x40, 0x41, 0x33];
	assert!(decode_init(&wire) == Some(init));
	assert_eq!(init_bytes(init), wire);

	let response = KexResponse {
		identity_key: &[0x10],
		ephemeral_key: &[0x20],
		kem_cipher_text: &[0x30],
		app_cipher_text: &[0x40],
		key_id: 42,
	};
	let wire = [
		0x87, 1, 1, 0x41, 0x10, 0x41, 0x20, 0x41, 0x30, 0x41, 0x40, 0x18, 42,
	];
	assert!(decode_response(&wire) == Some(response));
	assert_eq!(response_bytes(response), wire);
}

#[test]
fn integer_and_byte_length_boundaries_roundtrip() {
	for &number in UINT_BOUNDARIES {
		let frame = CryptoFrame {
			seq: number,
			key_id: u64::MAX - number,
			cipher_text: b"payload",
		};
		assert!(decode_frame(&frame_bytes(frame)) == Some(frame));
		let response = KexResponse {
			identity_key: b"identity",
			ephemeral_key: b"ephemeral",
			kem_cipher_text: b"kem",
			app_cipher_text: b"application",
			key_id: number,
		};
		assert!(decode_response(&response_bytes(response)) == Some(response));
	}
	for &length in BYTE_LENGTH_BOUNDARIES {
		let data: Vec<u8> = (0..length).map(|i| i as u8).collect();
		let frame = CryptoFrame {
			seq: 0,
			key_id: 0,
			cipher_text: &data,
		};
		assert!(decode_frame(&frame_bytes(frame)) == Some(frame));
		let init = InitKex {
			identity_key: &data,
			pre_key: &data,
			one_time_key: &data,
			pq_key: &data,
		};
		assert!(decode_init(&init_bytes(init)) == Some(init));
		let response = KexResponse {
			identity_key: &data,
			ephemeral_key: &data,
			kem_cipher_text: &data,
			app_cipher_text: &data,
			key_id: 0,
		};
		assert!(decode_response(&response_bytes(response)) == Some(response));
	}
}

#[test]
fn every_truncation_and_nonempty_suffix_is_rejected() {
	let data = [0xab; 256];
	let cases = [
		(
			Kind::Frame,
			frame_bytes(CryptoFrame {
				seq: u64::MAX,
				key_id: 24,
				cipher_text: &data,
			}),
		),
		(
			Kind::Init,
			init_bytes(InitKex {
				identity_key: &data,
				pre_key: &data[..24],
				one_time_key: &[],
				pq_key: &data[..1],
			}),
		),
		(
			Kind::Response,
			response_bytes(KexResponse {
				identity_key: &data[..1],
				ephemeral_key: &[],
				kem_cipher_text: &data,
				app_cipher_text: &data[..24],
				key_id: u64::MAX,
			}),
		),
	];
	for (kind, wire) in cases {
		assert!(kind.accepts(&wire));
		for end in 0..wire.len() {
			kind.reject("truncation", &wire[..end]);
		}
		for suffix in [vec![0], vec![0xff], wire.clone()] {
			let mut extended = wire.clone();
			extended.extend_from_slice(&suffix);
			kind.reject("suffix or concatenated message", &extended);
		}
	}
}

#[test]
fn empty_byte_strings_are_syntactically_valid() {
	// Cryptographic key and ciphertext lengths are a separate validation boundary.
	for &kind in KINDS {
		assert!(kind.accepts(kind.minimal()));
	}
}

#[test]
fn wrong_version_type_arity_and_major_types_are_rejected() {
	for &kind in KINDS {
		let wire = kind.minimal();
		kind.reject("unsupported version", &replacing(wire, 1, &[2]));
		kind.reject("unknown message type", &replacing(wire, 2, &[3]));
		for other in KINDS {
			if other.minimal()[2] != wire[2] {
				kind.reject("different message type", other.minimal());
			}
		}
		for arity in [wire[0] - 1, wire[0] + 1] {
			kind.reject("wrong arity", &replacing(wire, 0, &[arity]));
		}
		kind.reject(
			"map instead of array",
			&replacing(wire, 0, &[wire[0] + 0x20]),
		);
		for &offset in kind.byte_fields() {
			kind.reject(
				"text instead of byte string",
				&replacing(wire, offset, &[0x60]),
			);
			kind.reject(
				"integer instead of byte string",
				&replacing(wire, offset, &[0]),
			);
		}
		for &offset in kind.integer_fields() {
			kind.reject(
				"negative instead of unsigned integer",
				&replacing(wire, offset, &[0x20]),
			);
			kind.reject(
				"float instead of unsigned integer",
				&replacing(wire, offset, &[0xf9, 0, 0]),
			);
		}
	}
}

#[test]
fn nonminimal_integers_and_lengths_are_rejected() {
	for &kind in KINDS {
		let wire = kind.minimal();
		kind.reject(
			"overlong array length",
			&replacing(wire, 0, &[0x98, wire[0] & 0x1f]),
		);
		for offset in [1, 2]
			.into_iter()
			.chain(kind.integer_fields().iter().copied())
		{
			for replacement in [
				vec![0x18, wire[offset]],
				vec![0x19, 0, wire[offset]],
				vec![0x1a, 0, 0, 0, wire[offset]],
				vec![0x1b, 0, 0, 0, 0, 0, 0, 0, wire[offset]],
			] {
				kind.reject(
					"overlong unsigned integer",
					&replacing(wire, offset, &replacement),
				);
			}
		}
		for &offset in kind.byte_fields() {
			for replacement in [
				vec![0x58, 0],
				vec![0x59, 0, 0],
				vec![0x5a, 0, 0, 0, 0],
				vec![0x5b, 0, 0, 0, 0, 0, 0, 0, 0],
			] {
				kind.reject(
					"overlong byte string length",
					&replacing(wire, offset, &replacement),
				);
			}
		}
	}
}

#[test]
fn indefinite_containers_tags_and_unrepresentable_values_are_rejected() {
	for &kind in KINDS {
		let wire = kind.minimal();
		let mut indefinite = replacing(wire, 0, &[0x9f]);
		indefinite.push(0xff);
		kind.reject("indefinite array", &indefinite);
		let mut tagged = vec![0xc0];
		tagged.extend_from_slice(wire);
		kind.reject("tagged message", &tagged);
		kind.reject(
			"impossible array length",
			&replacing(wire, 0, &[0x9b, 255, 255, 255, 255, 255, 255, 255, 255]),
		);
		for &offset in kind.byte_fields() {
			kind.reject(
				"indefinite byte string",
				&replacing(wire, offset, &[0x5f, 0x40, 0xff]),
			);
			kind.reject(
				"impossible byte string length",
				&replacing(
					wire,
					offset,
					&[0x5b, 255, 255, 255, 255, 255, 255, 255, 255],
				),
			);
		}
		for offset in [1, 2]
			.into_iter()
			.chain(kind.integer_fields().iter().copied())
		{
			// CBOR unsigned integers stop at u64::MAX; 2^64 needs the unsupported bignum tag.
			kind.reject(
				"integer greater than u64",
				&replacing(wire, offset, &[0xc2, 0x49, 1, 0, 0, 0, 0, 0, 0, 0, 0]),
			);
			for invalid in 0x1c..=0x1f {
				kind.reject(
					"reserved integer additional information",
					&replacing(wire, offset, &[invalid]),
				);
			}
		}
	}
}

#[test]
fn bounded_hostile_inputs_do_not_panic() {
	let mut state = 0x9e37_79b9_u32;
	for first in 0..=u8::MAX {
		for length in 0..=64 {
			let mut input = vec![first; length];
			for byte in input.iter_mut().skip(1) {
				state ^= state << 13;
				state ^= state >> 17;
				state ^= state << 5;
				*byte = state as u8;
			}
			for &kind in KINDS {
				let _ = kind.accepts(&input);
			}
		}
	}
	for prefix in [&[0x81][..], &[0xc0][..], &[0xa1, 0][..]] {
		for depth in [1, 8, 32, 64] {
			let mut nested = prefix.repeat(depth);
			nested.push(0);
			for &kind in KINDS {
				kind.reject("nested container or tag", &nested);
				for &offset in kind.byte_fields() {
					kind.reject(
						"nested container or tag in byte field",
						&replacing(kind.minimal(), offset, &nested),
					);
				}
			}
		}
	}
}

fn assert_borrowed(input: &[u8], field: &[u8]) {
	assert!(!field.is_empty());
	let start = input.as_ptr() as usize;
	let field_start = field.as_ptr() as usize;
	assert!(field_start >= start && field_start + field.len() <= start + input.len());
}

#[test]
fn parsers_borrow_every_byte_string_from_the_input() {
	let frame = frame_bytes(CryptoFrame {
		seq: 1,
		key_id: 2,
		cipher_text: b"frame",
	});
	assert_borrowed(&frame, decode_frame(&frame).unwrap().cipher_text);
	let init = init_bytes(InitKex {
		identity_key: b"identity",
		pre_key: b"pre",
		one_time_key: b"once",
		pq_key: b"pq",
	});
	let value = decode_init(&init).unwrap();
	for field in [
		value.identity_key,
		value.pre_key,
		value.one_time_key,
		value.pq_key,
	] {
		assert_borrowed(&init, field);
	}
	let response = response_bytes(KexResponse {
		identity_key: b"identity",
		ephemeral_key: b"ephemeral",
		kem_cipher_text: b"kem",
		app_cipher_text: b"application",
		key_id: 3,
	});
	let value = decode_response(&response).unwrap();
	for field in [
		value.identity_key,
		value.ephemeral_key,
		value.kem_cipher_text,
		value.app_cipher_text,
	] {
		assert_borrowed(&response, field);
	}
}

fn assert_output_sizes(expected: &[u8], encode: impl Fn(&mut [u8]) -> usize) {
	for size in 0..expected.len() {
		let mut out = vec![0xa5; expected.len() + 8];
		assert_eq!(
			encode(&mut out[..size]),
			0,
			"accepted output capacity {size}"
		);
		assert!(out[size..].iter().all(|&byte| byte == 0xa5));
	}
	let mut exact = vec![0; expected.len()];
	assert_eq!(encode(&mut exact), expected.len());
	assert_eq!(exact, expected);
}

#[test]
fn insufficient_output_capacity_returns_zero_and_exact_capacity_succeeds() {
	let frame = CryptoFrame {
		seq: u64::MAX,
		key_id: 24,
		cipher_text: b"ciphertext",
	};
	assert_output_sizes(&frame_bytes(frame), |out| encode_frame(frame, out));
	let init = InitKex {
		identity_key: b"identity",
		pre_key: b"pre",
		one_time_key: b"once",
		pq_key: &[0xa5; 256],
	};
	assert_output_sizes(&init_bytes(init), |out| encode_init(init, out));
	let response = KexResponse {
		identity_key: b"identity",
		ephemeral_key: b"ephemeral",
		kem_cipher_text: b"kem",
		app_cipher_text: b"application",
		key_id: u64::MAX,
	};
	assert_output_sizes(&response_bytes(response), |out| {
		encode_response(response, out)
	});
}

#[test]
fn complete_encoded_limit_is_inclusive_and_oversized_encoders_do_not_write() {
	// Reuse one large allocation for all layouts and both sides of the limit.
	let mut wire = vec![0xa5; MAX_MESSAGE_SIZE + 1];
	for kind in KINDS {
		for oversized in [false, true] {
			let total = MAX_MESSAGE_SIZE + usize::from(oversized);
			let (prefix, tail): (&[u8], usize) = match kind {
				Kind::Frame => (&[0x85, 1, 2, 0, 0, 0x5a], 0),
				Kind::Init => (&[0x86, 1, 0, 0x40, 0x40, 0x40, 0x5a], 0),
				Kind::Response => (&[0x87, 1, 1, 0x40, 0x40, 0x40, 0x5a], 1),
			};
			let payload_length = total - prefix.len() - 4 - tail;
			wire[..prefix.len()].copy_from_slice(prefix);
			wire[prefix.len()..prefix.len() + 4]
				.copy_from_slice(&(payload_length as u32).to_be_bytes());
			if tail == 1 {
				wire[total - 1] = 0;
			}
			assert_eq!(
				kind.accepts(&wire[..total]),
				!oversized,
				"{kind:?} at {total} bytes"
			);
			let expected = (!oversized).then_some(total);
			let mut output = [0x5a; 64];
			match kind {
				Kind::Frame => {
					assert_eq!(encoded_frame_len(0, 0, payload_length), expected);
					if oversized {
						assert_eq!(
							encode_frame(
								CryptoFrame {
									seq: 0,
									key_id: 0,
									cipher_text: &wire[..payload_length]
								},
								&mut output
							),
							0
						);
					}
				}
				Kind::Init | Kind::Response => {
					// Every byte-string position contributes to the complete encoded size.
					for field in 0..4 {
						let mut lengths = [0; 4];
						lengths[field] = payload_length;
						let mut values: [&[u8]; 4] = [&[]; 4];
						values[field] = &wire[..payload_length];
						if matches!(kind, Kind::Init) {
							assert_eq!(encoded_init_len(lengths), expected);
							if oversized {
								assert_eq!(
									encode_init(
										InitKex {
											identity_key: values[0],
											pre_key: values[1],
											one_time_key: values[2],
											pq_key: values[3]
										},
										&mut output
									),
									0
								);
							}
						} else {
							assert_eq!(encoded_response_len(lengths, 0), expected);
							if oversized {
								assert_eq!(
									encode_response(
										KexResponse {
											identity_key: values[0],
											ephemeral_key: values[1],
											kem_cipher_text: values[2],
											app_cipher_text: values[3],
											key_id: 0
										},
										&mut output
									),
									0
								);
							}
						}
					}
				}
			}
			assert_eq!(output, [0x5a; 64], "oversized encoder touched output");
		}
	}
}
