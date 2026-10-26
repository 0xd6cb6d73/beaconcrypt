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
		value.mldsa_public_key.len(),
		value.signature.len(),
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
			value.signature.len(),
		],
		value.key_id,
	)
	.unwrap();
	let mut out = vec![0; expected];
	assert_eq!(encode_response(value, &mut out), expected);
	out
}

const INIT_IDENTITY: [u8; 33] = [0x11; 33];
const INIT_PREKEY: [u8; 98] = [0x22; 98];
const INIT_ONE_TIME: [u8; 98] = [0x33; 98];
const INIT_PQ: [u8; 1249] = [0x44; 1249];
const INIT_MLDSA_PUBLIC: [u8; 1952] = [0x88; 1952];
const INIT_SIGNATURE: [u8; 3309] = [0x99; 3309];
const RESPONSE_IDENTITY: [u8; 32] = [0x55; 32];
const RESPONSE_EPHEMERAL: [u8; 32] = [0x66; 32];
const RESPONSE_KEM: [u8; 1088] = [0x77; 1088];
const RESPONSE_SIGNATURE: [u8; 3309] = [0xaa; 3309];

fn valid_init() -> InitKex<'static> {
	InitKex {
		identity_key: &INIT_IDENTITY,
		pre_key: &INIT_PREKEY,
		one_time_key: &INIT_ONE_TIME,
		pq_key: &INIT_PQ,
		mldsa_public_key: &INIT_MLDSA_PUBLIC,
		signature: &INIT_SIGNATURE,
	}
}

fn valid_response(app_cipher_text: &[u8], key_id: u64) -> KexResponse<'_> {
	KexResponse {
		identity_key: &RESPONSE_IDENTITY,
		ephemeral_key: &RESPONSE_EPHEMERAL,
		kem_cipher_text: &RESPONSE_KEM,
		app_cipher_text,
		key_id,
		signature: &RESPONSE_SIGNATURE,
	}
}

// Independent fixture construction permits malformed lengths that the generated encoder rejects.
fn append_argument(wire: &mut Vec<u8>, major: u8, value: u64) {
	let (information, width) = match value {
		0..=23 => {
			wire.push(major << 5 | value as u8);
			return;
		}
		24..=255 => (24, 1),
		256..=65_535 => (25, 2),
		65_536..=4_294_967_295 => (26, 4),
		_ => (27, 8),
	};
	wire.push(major << 5 | information);
	wire.extend_from_slice(&value.to_be_bytes()[8 - width..]);
}

fn append_bytes(wire: &mut Vec<u8>, bytes: &[u8]) {
	append_argument(wire, 2, bytes.len() as u64);
	wire.extend_from_slice(bytes);
}

fn independent_init(value: InitKex<'_>) -> Vec<u8> {
	let mut wire = vec![0x88, 2, 0];
	for bytes in [
		value.identity_key,
		value.pre_key,
		value.one_time_key,
		value.pq_key,
		value.mldsa_public_key,
		value.signature,
	] {
		append_bytes(&mut wire, bytes);
	}
	wire
}

fn independent_response(value: KexResponse<'_>) -> Vec<u8> {
	let mut wire = vec![0x88, 2, 1];
	for bytes in [
		value.identity_key,
		value.ephemeral_key,
		value.kem_cipher_text,
		value.app_cipher_text,
	] {
		append_bytes(&mut wire, bytes);
	}
	append_argument(&mut wire, 0, value.key_id);
	append_bytes(&mut wire, value.signature);
	wire
}

#[derive(Clone, Copy, Debug)]
enum Kind {
	Frame,
	Init,
	Response,
}

impl Kind {
	fn minimal(self) -> Vec<u8> {
		match self {
			Self::Frame => vec![0x85, 1, 2, 0, 0, 0x40],
			Self::Init => independent_init(valid_init()),
			Self::Response => independent_response(valid_response(&[], 0)),
		}
	}

	fn byte_fields(self) -> &'static [usize] {
		match self {
			Self::Frame => &[5],
			Self::Init => &[3, 38, 138, 238, 1490, 3445],
			Self::Response => &[3, 37, 71, 1162, 1164],
		}
	}

	fn byte_field_lengths(self) -> &'static [(usize, usize)] {
		match self {
			Self::Frame => &[(5, 0)],
			Self::Init => &[
				(3, 33),
				(38, 98),
				(138, 98),
				(238, 1249),
				(1490, 1952),
				(3445, 3309),
			],
			Self::Response => &[(3, 32), (37, 32), (71, 1088), (1162, 0), (1164, 3309)],
		}
	}

	fn integer_fields(self) -> &'static [usize] {
		match self {
			Self::Frame => &[3, 4],
			Self::Init => &[],
			Self::Response => &[1163],
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

	let init = valid_init();
	let wire = independent_init(init);
	assert_eq!(&wire[..5], &[0x88, 2, 0, 0x58, 33]);
	assert_eq!(&wire[38..40], &[0x58, 98]);
	assert_eq!(&wire[138..140], &[0x58, 98]);
	assert_eq!(&wire[238..241], &[0x59, 4, 0xe1]);
	assert_eq!(&wire[1490..1493], &[0x59, 7, 0xa0]);
	assert_eq!(&wire[3445..3448], &[0x59, 0x0c, 0xed]);
	assert!(decode_init(&wire) == Some(init));
	assert_eq!(init_bytes(init), wire);

	let response = valid_response(&[0x40], 42);
	let wire = independent_response(response);
	assert_eq!(&wire[..5], &[0x88, 2, 1, 0x58, 32]);
	assert_eq!(&wire[71..74], &[0x59, 4, 0x40]);
	assert_eq!(&wire[1162..1169], &[0x41, 0x40, 0x18, 42, 0x59, 0x0c, 0xed]);
	assert_eq!(&wire[1169..], RESPONSE_SIGNATURE);
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
		let response = valid_response(b"application", number);
		assert!(decode_response(&response_bytes(response)) == Some(response));
	}
	let init = valid_init();
	assert!(decode_init(&init_bytes(init)) == Some(init));
	for &length in BYTE_LENGTH_BOUNDARIES {
		let data: Vec<u8> = (0..length).map(|i| i as u8).collect();
		let frame = CryptoFrame {
			seq: 0,
			key_id: 0,
			cipher_text: &data,
		};
		assert!(decode_frame(&frame_bytes(frame)) == Some(frame));
		let response = valid_response(&data, 0);
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
		(Kind::Init, init_bytes(valid_init())),
		(
			Kind::Response,
			response_bytes(valid_response(&data[..24], u64::MAX)),
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
fn variable_cipher_byte_strings_may_be_empty() {
	assert!(decode_frame(&[0x85, 1, 2, 0, 0, 0x40]).is_some());
	let response = valid_response(&[], 0);
	assert!(decode_response(&response_bytes(response)) == Some(response));
}

#[test]
fn wrong_version_type_arity_and_major_types_are_rejected() {
	for &kind in KINDS {
		let fixture = kind.minimal();
		let wire = fixture.as_slice();
		kind.reject("unsupported version", &replacing(wire, 1, &[wire[1] ^ 3]));
		kind.reject("unknown message type", &replacing(wire, 2, &[3]));
		for other in KINDS {
			if other.minimal()[2] != wire[2] {
				kind.reject("different message type", &other.minimal());
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
fn previous_registration_wire_and_missing_authentication_fields_are_rejected() {
	let init = independent_init(valid_init());
	let response = independent_response(valid_response(&[], 0));
	for (kind, wire, unsigned_end, old_arity) in [
		(Kind::Init, &init, 1490, 0x86),
		(Kind::Response, &response, 1164, 0x87),
	] {
		let mut old = wire[..unsigned_end].to_vec();
		old[0] = old_arity;
		old[1] = 1;
		kind.reject("unsigned registration version 1", &old);
		old[1] = 2;
		kind.reject("registration version 2 without authentication fields", &old);
		let mut old_version = wire.clone();
		old_version[1] = 1;
		kind.reject(
			"version 1 with version 2 authentication fields",
			&old_version,
		);
	}
	let mut missing_signature = init[..3445].to_vec();
	missing_signature[0] = 0x87;
	Kind::Init.reject("request without ML-DSA signature", &missing_signature);
	let mut unexpected_field = response.clone();
	unexpected_field[0] = 0x89;
	append_bytes(&mut unexpected_field, &[]);
	Kind::Response.reject("response with an extra field", &unexpected_field);
}

#[test]
fn nonminimal_integers_and_lengths_are_rejected() {
	for &kind in KINDS {
		let fixture = kind.minimal();
		let wire = fixture.as_slice();
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
		for &(offset, length) in kind.byte_field_lengths() {
			let canonical_width = match length {
				0..=23 => 0,
				24..=255 => 1,
				_ => 2,
			};
			for (header, width) in [(0x58, 1), (0x59, 2), (0x5a, 4), (0x5b, 8)] {
				if width > canonical_width {
					let mut changed = wire[..offset].to_vec();
					changed.push(header);
					changed.extend_from_slice(&(length as u64).to_be_bytes()[8 - width..]);
					changed.extend_from_slice(&wire[offset + canonical_width + 1..]);
					kind.reject(
						"overlong byte string length with unchanged payload",
						&changed,
					);
				}
			}
		}
	}
}

#[test]
fn indefinite_containers_tags_and_unrepresentable_values_are_rejected() {
	for &kind in KINDS {
		let fixture = kind.minimal();
		let wire = fixture.as_slice();
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
						&replacing(&kind.minimal(), offset, &nested),
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
	let init = init_bytes(valid_init());
	let value = decode_init(&init).unwrap();
	for field in [
		value.identity_key,
		value.pre_key,
		value.one_time_key,
		value.pq_key,
		value.mldsa_public_key,
		value.signature,
	] {
		assert_borrowed(&init, field);
	}
	let response = response_bytes(valid_response(b"application", 3));
	let value = decode_response(&response).unwrap();
	for field in [
		value.identity_key,
		value.ephemeral_key,
		value.kem_cipher_text,
		value.app_cipher_text,
		value.signature,
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
	let init = valid_init();
	assert_output_sizes(&init_bytes(init), |out| encode_init(init, out));
	let response = valid_response(b"application", u64::MAX);
	assert_output_sizes(&response_bytes(response), |out| {
		encode_response(response, out)
	});
}

#[test]
fn complete_encoded_limit_is_inclusive_and_oversized_encoders_do_not_write() {
	// Both authentication fields count toward the same complete-message budget.
	assert_eq!(init_bytes(valid_init()).len(), 6757);
	let mut wire = vec![0xa5; MAX_MESSAGE_SIZE + 1];
	for kind in [Kind::Frame, Kind::Response] {
		for oversized in [false, true] {
			let total = MAX_MESSAGE_SIZE + usize::from(oversized);
			let (mut prefix, tail) = match kind {
				Kind::Frame => (vec![0x85, 1, 2, 0, 0, 0x5a], 0),
				Kind::Response => {
					let mut prefix = vec![0x88, 2, 1];
					for field in [
						&RESPONSE_IDENTITY[..],
						&RESPONSE_EPHEMERAL[..],
						&RESPONSE_KEM[..],
					] {
						append_bytes(&mut prefix, field);
					}
					prefix.push(0x5a);
					(prefix, 1 + 3 + RESPONSE_SIGNATURE.len())
				}
				Kind::Init => unreachable!(),
			};
			let payload_length = total - prefix.len() - 4 - tail;
			prefix.extend_from_slice(&(payload_length as u32).to_be_bytes());
			wire[..prefix.len()].copy_from_slice(&prefix);
			if tail > 0 {
				let start = total - tail;
				wire[start..start + 4].copy_from_slice(&[0, 0x59, 0x0c, 0xed]);
				wire[start + 4..total].copy_from_slice(&RESPONSE_SIGNATURE);
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
				Kind::Response => {
					assert_eq!(
						encoded_response_len([32, 32, 1088, payload_length, 3309], 0),
						expected
					);
					if oversized {
						assert_eq!(
							encode_response(
								valid_response(&wire[..payload_length], 0),
								&mut output
							),
							0
						);
					}
				}
				Kind::Init => unreachable!(),
			}
			assert_eq!(output, [0x5a; 64], "oversized encoder touched output");
		}
	}
	// The complete-message budget also rejects oversized fixed-field requests before writing.
	let mut output = [0x5a; 64];
	assert_eq!(
		encode_init(
			InitKex {
				pq_key: &wire[..MAX_MESSAGE_SIZE],
				..valid_init()
			},
			&mut output
		),
		0
	);
	assert_eq!(output, [0x5a; 64]);
}

#[test]
fn fixed_registration_field_lengths_reject_one_short_and_one_long_wire_inputs() {
	for field in 0..6 {
		for adjustment in [-1isize, 1] {
			let mut values = [
				&INIT_IDENTITY[..],
				&INIT_PREKEY[..],
				&INIT_ONE_TIME[..],
				&INIT_PQ[..],
				&INIT_MLDSA_PUBLIC[..],
				&INIT_SIGNATURE[..],
			];
			let malformed = vec![0x5a; values[field].len().checked_add_signed(adjustment).unwrap()];
			values[field] = &malformed;
			let wire = independent_init(InitKex {
				identity_key: values[0],
				pre_key: values[1],
				one_time_key: values[2],
				pq_key: values[3],
				mldsa_public_key: values[4],
				signature: values[5],
			});
			assert!(
				decode_init(&wire).is_none(),
				"init field {field}, adjustment {adjustment}"
			);
		}
	}
	for field in 0..4 {
		for adjustment in [-1isize, 1] {
			let mut values = [
				&RESPONSE_IDENTITY[..],
				&RESPONSE_EPHEMERAL[..],
				&RESPONSE_KEM[..],
				&RESPONSE_SIGNATURE[..],
			];
			let malformed = vec![0x5a; values[field].len().checked_add_signed(adjustment).unwrap()];
			values[field] = &malformed;
			let wire = independent_response(KexResponse {
				identity_key: values[0],
				ephemeral_key: values[1],
				kem_cipher_text: values[2],
				app_cipher_text: &[],
				key_id: 0,
				signature: values[3],
			});
			assert!(
				decode_response(&wire).is_none(),
				"response field {field}, adjustment {adjustment}"
			);
		}
	}
}

#[test]
fn fixed_registration_field_lengths_reject_one_short_and_one_long_encoder_inputs() {
	let mut output = [0u8; 8192];
	assert!(encode_init(valid_init(), &mut output) > 0);
	assert!(encode_response(valid_response(&[], 0), &mut output) > 0);
	for field in 0..6 {
		for adjustment in [-1isize, 1] {
			let mut values = [
				&INIT_IDENTITY[..],
				&INIT_PREKEY[..],
				&INIT_ONE_TIME[..],
				&INIT_PQ[..],
				&INIT_MLDSA_PUBLIC[..],
				&INIT_SIGNATURE[..],
			];
			let malformed = vec![0x5a; values[field].len().checked_add_signed(adjustment).unwrap()];
			values[field] = &malformed;
			assert_eq!(
				encode_init(
					InitKex {
						identity_key: values[0],
						pre_key: values[1],
						one_time_key: values[2],
						pq_key: values[3],
						mldsa_public_key: values[4],
						signature: values[5],
					},
					&mut output
				),
				0,
				"init field {field}, adjustment {adjustment}"
			);
		}
	}
	for field in 0..4 {
		for adjustment in [-1isize, 1] {
			let mut values = [
				&RESPONSE_IDENTITY[..],
				&RESPONSE_EPHEMERAL[..],
				&RESPONSE_KEM[..],
				&RESPONSE_SIGNATURE[..],
			];
			let malformed = vec![0x5a; values[field].len().checked_add_signed(adjustment).unwrap()];
			values[field] = &malformed;
			assert_eq!(
				encode_response(
					KexResponse {
						identity_key: values[0],
						ephemeral_key: values[1],
						kem_cipher_text: values[2],
						app_cipher_text: &[],
						key_id: 0,
						signature: values[3],
					},
					&mut output
				),
				0,
				"response field {field}, adjustment {adjustment}"
			);
		}
	}
}
