// SPDX-License-Identifier: 0BSD

use beaconcrypt_parse::{
	CryptoFrame, InitKex, KexResponse, MAX_MESSAGE_SIZE, decode_frame, decode_init,
	decode_response, encode_frame, encode_init, encode_response, encoded_frame_len,
	encoded_init_len, encoded_response_len,
};
use proptest::{prelude::*, test_runner::FileFailurePersistence};

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

fn config() -> ProptestConfig {
	let mut config = ProptestConfig::default();
	if std::env::var_os("PROPTEST_CASES").is_none() {
		config.cases = 64;
	}
	// Keep integration-test regression replay independent of the working directory.
	config.failure_persistence = Some(Box::new(FileFailurePersistence::Direct(concat!(
		env!("CARGO_MANIFEST_DIR"),
		"/proptest-regressions/properties.txt"
	))));
	config
}

fn integers() -> impl Strategy<Value = u64> {
	prop_oneof![2 => any::<u64>(), 1 => proptest::sample::select(UINT_BOUNDARIES)]
}

fn payloads() -> impl Strategy<Value = Vec<u8>> {
	let lengths = prop_oneof![
		4 => 0usize..1025,
		2 => proptest::sample::select(vec![0, 1, 23, 24, 25, 255, 256, 257]),
		1 => proptest::sample::select(vec![65_535, 65_536]),
	];
	lengths.prop_flat_map(|length| proptest::collection::vec(any::<u8>(), length))
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Message {
	Frame {
		seq: u64,
		key_id: u64,
		ciphertext: Vec<u8>,
	},
	Init([Vec<u8>; 4]),
	Response {
		fields: [Vec<u8>; 4],
		key_id: u64,
	},
}

impl Message {
	fn frame(&self) -> CryptoFrame<'_> {
		let Self::Frame {
			seq,
			key_id,
			ciphertext,
		} = self
		else {
			unreachable!()
		};
		CryptoFrame {
			seq: *seq,
			key_id: *key_id,
			cipher_text: ciphertext,
		}
	}

	fn init(&self) -> InitKex<'_> {
		let Self::Init(fields) = self else {
			unreachable!()
		};
		InitKex {
			identity_key: &fields[0],
			pre_key: &fields[1],
			one_time_key: &fields[2],
			pq_key: &fields[3],
		}
	}

	fn response(&self) -> KexResponse<'_> {
		let Self::Response { fields, key_id } = self else {
			unreachable!()
		};
		KexResponse {
			identity_key: &fields[0],
			ephemeral_key: &fields[1],
			kem_cipher_text: &fields[2],
			app_cipher_text: &fields[3],
			key_id: *key_id,
		}
	}

	fn encoded_len(&self) -> Option<usize> {
		match self {
			Self::Frame {
				seq,
				key_id,
				ciphertext,
			} => encoded_frame_len(*seq, *key_id, ciphertext.len()),
			Self::Init(fields) => encoded_init_len(fields.each_ref().map(Vec::len)),
			Self::Response { fields, key_id } => {
				encoded_response_len(fields.each_ref().map(Vec::len), *key_id)
			}
		}
	}

	fn encode(&self, output: &mut [u8]) -> usize {
		match self {
			Self::Frame { .. } => encode_frame(self.frame(), output),
			Self::Init(_) => encode_init(self.init(), output),
			Self::Response { .. } => encode_response(self.response(), output),
		}
	}

	fn decode(&self, input: &[u8]) -> Option<Self> {
		match self {
			Self::Frame { .. } => decode_frame(input).map(|value| Self::Frame {
				seq: value.seq,
				key_id: value.key_id,
				ciphertext: value.cipher_text.to_vec(),
			}),
			Self::Init(_) => decode_init(input).map(|value| {
				Self::Init([
					value.identity_key.to_vec(),
					value.pre_key.to_vec(),
					value.one_time_key.to_vec(),
					value.pq_key.to_vec(),
				])
			}),
			Self::Response { .. } => decode_response(input).map(|value| Self::Response {
				fields: [
					value.identity_key.to_vec(),
					value.ephemeral_key.to_vec(),
					value.kem_cipher_text.to_vec(),
					value.app_cipher_text.to_vec(),
				],
				key_id: value.key_id,
			}),
		}
	}

	// Independent CBOR construction prevents a matching encoder/decoder mistake from passing.
	fn reference_bytes(&self) -> Vec<u8> {
		let mut bytes = match self {
			Self::Frame { .. } => vec![0x85, 1, 2],
			Self::Init(_) => vec![0x86, 1, 0],
			Self::Response { .. } => vec![0x87, 1, 1],
		};
		match self {
			Self::Frame {
				seq,
				key_id,
				ciphertext,
			} => {
				append_argument(&mut bytes, 0, *seq);
				append_argument(&mut bytes, 0, *key_id);
				append_bytes(&mut bytes, ciphertext);
			}
			Self::Init(fields) => {
				for field in fields {
					append_bytes(&mut bytes, field);
				}
			}
			Self::Response { fields, key_id } => {
				for field in fields {
					append_bytes(&mut bytes, field);
				}
				append_argument(&mut bytes, 0, *key_id);
			}
		}
		bytes
	}

	fn first_byte_field(&self) -> (usize, usize) {
		match self {
			Self::Frame {
				seq,
				key_id,
				ciphertext,
			} => {
				let mut prefix = Vec::new();
				append_argument(&mut prefix, 0, *seq);
				append_argument(&mut prefix, 0, *key_id);
				(3 + prefix.len(), ciphertext.len())
			}
			Self::Init(fields) | Self::Response { fields, .. } => (3, fields[0].len()),
		}
	}
}

fn frames() -> impl Strategy<Value = Message> {
	(integers(), integers(), payloads()).prop_map(|(seq, key_id, ciphertext)| Message::Frame {
		seq,
		key_id,
		ciphertext,
	})
}

fn inits() -> impl Strategy<Value = Message> {
	(
		proptest::collection::vec(any::<u8>(), 33),
		proptest::collection::vec(any::<u8>(), 98),
		proptest::collection::vec(any::<u8>(), 98),
		proptest::collection::vec(any::<u8>(), 1249),
	)
		.prop_map(|(identity, prekey, one_time, pq)| {
			Message::Init([identity, prekey, one_time, pq])
		})
}

fn responses() -> impl Strategy<Value = Message> {
	(
		proptest::collection::vec(any::<u8>(), 32),
		proptest::collection::vec(any::<u8>(), 32),
		proptest::collection::vec(any::<u8>(), 1088),
		payloads(),
		integers(),
	)
		.prop_map(
			|(identity, ephemeral, kem, application, key_id)| Message::Response {
				fields: [identity, ephemeral, kem, application],
				key_id,
			},
		)
}

fn messages() -> impl Strategy<Value = Message> {
	prop_oneof![frames(), inits(), responses()]
}

fn append_argument(bytes: &mut Vec<u8>, major: u8, value: u64) {
	let width = if value < 24 {
		0
	} else if value <= u8::MAX.into() {
		1
	} else if value <= u16::MAX.into() {
		2
	} else if value <= u32::MAX.into() {
		4
	} else {
		8
	};
	let information = match width {
		0 => value as u8,
		1 => 24,
		2 => 25,
		4 => 26,
		_ => 27,
	};
	bytes.push(major << 5 | information);
	bytes.extend_from_slice(&value.to_be_bytes()[8 - width..]);
}

fn append_bytes(bytes: &mut Vec<u8>, field: &[u8]) {
	append_argument(bytes, 2, field.len() as u64);
	bytes.extend_from_slice(field);
}

fn check_codec_contract(
	message: Message,
	capacity: usize,
) -> proptest::test_runner::TestCaseResult {
	let expected = message.reference_bytes();
	let length = expected.len();
	prop_assert_eq!(message.encoded_len(), Some(length));
	let mut output = vec![0xa5; length + 8];
	prop_assert_eq!(message.encode(&mut output), length);
	prop_assert_eq!(&output[..length], expected.as_slice());
	let decoded = message
		.decode(&expected)
		.expect("independently encoded valid value");
	prop_assert_eq!(&decoded, &message);
	let mut reencoded = vec![0; length];
	prop_assert_eq!(decoded.encode(&mut reencoded), length);
	prop_assert_eq!(reencoded, expected);
	for short in [0, length - 1, capacity % length] {
		let mut guarded = vec![0xa5; short + 8];
		prop_assert_eq!(message.encode(&mut guarded[..short]), 0);
		// Failed encodes may modify the offered slice, but never its guard bytes.
		prop_assert!(guarded[short..].iter().all(|&byte| byte == 0xa5));
	}
	Ok(())
}

fn sizing_lengths() -> impl Strategy<Value = usize> {
	prop_oneof![
		2 => any::<usize>(),
		3 => 0usize..=MAX_MESSAGE_SIZE,
		2 => proptest::sample::select(vec![0, 23, 24, 255, 256, 65_535, 65_536,
			MAX_MESSAGE_SIZE - 1, MAX_MESSAGE_SIZE, MAX_MESSAGE_SIZE + 1, usize::MAX]),
	]
}

fn reference_len(lengths: &[usize], numbers: &[u64]) -> Option<usize> {
	let mut headers = vec![0; 3];
	for &number in numbers {
		append_argument(&mut headers, 0, number);
	}
	let mut total = 0u128;
	for &length in lengths {
		append_argument(&mut headers, 2, u64::try_from(length).ok()?);
		total += length as u128;
	}
	total += headers.len() as u128;
	(total <= MAX_MESSAGE_SIZE as u128).then_some(total as usize)
}

proptest! {
	#![proptest_config(config())]

	#[test]
	fn frames_match_the_schema_and_obey_buffer_contracts(message in frames(), capacity in any::<usize>()) {
		check_codec_contract(message, capacity)?;
	}

	#[test]
	fn requests_match_the_schema_and_obey_buffer_contracts(message in inits(), capacity in any::<usize>()) {
		check_codec_contract(message, capacity)?;
	}

	#[test]
	fn responses_match_the_schema_and_obey_buffer_contracts(message in responses(), capacity in any::<usize>()) {
		check_codec_contract(message, capacity)?;
	}

	#[test]
	fn malformed_versions_of_valid_messages_are_rejected(
		message in messages(), cut in any::<usize>(), suffix in proptest::collection::vec(any::<u8>(), 1..17),
	) {
		let wire = message.reference_bytes();
		prop_assert!(message.decode(&wire[..cut % wire.len()]).is_none(), "truncation");
		let mut changed = wire.clone();
		changed.extend_from_slice(&suffix);
		prop_assert!(message.decode(&changed).is_none(), "nonempty suffix");
		for (offset, value) in [(0, 0x80), (1, 0), (2, 3)] {
			let mut changed = wire.clone();
			changed[offset] = value;
			prop_assert!(message.decode(&changed).is_none(), "wrong arity/version/type at {}", offset);
		}
		let (offset, length) = message.first_byte_field();
		let mut changed = wire.clone();
		changed[offset] ^= 0x20;
		prop_assert!(message.decode(&changed).is_none(), "text in place of byte string");
		let mut header = Vec::new();
		append_argument(&mut header, 2, length as u64);
		let mut overlong = wire[..offset].to_vec();
		overlong.push(0x5b);
		overlong.extend_from_slice(&(length as u64).to_be_bytes());
		overlong.extend_from_slice(&wire[offset + header.len()..]);
		prop_assert!(message.decode(&overlong).is_none(), "nonminimal byte length");
		let mut wrong_size = message.clone();
		if let Message::Init(fields) | Message::Response { fields, .. } = &mut wrong_size {
			fields[0].pop();
			prop_assert!(message.decode(&wrong_size.reference_bytes()).is_none(), "wrong identity width");
		}
	}

	#[test]
	fn bounded_arbitrary_inputs_decode_without_panicking(input in proptest::collection::vec(any::<u8>(), 0..4097)) {
		let _ = decode_frame(&input);
		let _ = decode_init(&input);
		let _ = decode_response(&input);
	}

	#[test]
	fn sizing_agrees_with_independent_wide_arithmetic(
		seq in integers(), key_id in integers(), lengths in proptest::array::uniform4(sizing_lengths()),
	) {
		prop_assert_eq!(encoded_frame_len(seq, key_id, lengths[0]), reference_len(&lengths[..1], &[seq, key_id]));
		prop_assert_eq!(encoded_init_len(lengths), reference_len(&lengths, &[]));
		prop_assert_eq!(encoded_response_len(lengths, key_id), reference_len(&lengths, &[key_id]));
	}
}

#[test]
fn complete_message_boundaries_cover_every_integer_width_without_large_allocations() {
	for &seq in UINT_BOUNDARIES {
		for &key_id in UINT_BOUNDARIES {
			// All candidate payloads use a five-byte byte-string header near 32 MiB.
			let overhead = reference_len(&[65_536], &[seq, key_id]).unwrap() - 65_536;
			let payload = MAX_MESSAGE_SIZE - overhead;
			assert_eq!(
				encoded_frame_len(seq, key_id, payload),
				Some(MAX_MESSAGE_SIZE)
			);
			assert_eq!(encoded_frame_len(seq, key_id, payload + 1), None);
		}
		for field in 0..4 {
			let mut lengths = [0; 4];
			lengths[field] = 65_536;
			let overhead = reference_len(&lengths, &[seq]).unwrap() - 65_536;
			lengths[field] = MAX_MESSAGE_SIZE - overhead;
			assert_eq!(encoded_response_len(lengths, seq), Some(MAX_MESSAGE_SIZE));
			lengths[field] += 1;
			assert_eq!(encoded_response_len(lengths, seq), None);
		}
	}
}
