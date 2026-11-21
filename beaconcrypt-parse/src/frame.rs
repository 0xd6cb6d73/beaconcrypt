// SPDX-License-Identifier: 0BSD

//! The ordinary frame's fixed, flat canonical CBOR codec.
//!
//! Registration continues to use the generated schema codecs. Keeping this
//! small codec independent of their general CBOR value machinery permits its
//! production control flow to be extracted and checked directly in Lean.

use beaconcrypt_core::transport::{MAX_MESSAGE_SIZE, encoded_frame_len};

#[derive(PartialEq, Clone, Copy)]
pub struct Frame<'a> {
	pub seq: u64,
	pub key_id: u64,
	pub cipher_text: &'a [u8],
}

/// A canonical argument fits in nine bytes; `length` selects its used prefix.
pub(crate) struct Argument {
	pub bytes: [u8; 9],
	pub length: usize,
}

pub(crate) fn encode_argument(major: u8, value: u64) -> Argument {
	let word = value.to_be_bytes();
	let (bytes, length) = if value <= 23 {
		([major << 5 | value as u8, 0, 0, 0, 0, 0, 0, 0, 0], 1)
	} else if value <= 255 {
		([major << 5 | 24, word[7], 0, 0, 0, 0, 0, 0, 0], 2)
	} else if value <= 65_535 {
		([major << 5 | 25, word[6], word[7], 0, 0, 0, 0, 0, 0], 3)
	} else if value <= 4_294_967_295 {
		(
			[
				major << 5 | 26,
				word[4],
				word[5],
				word[6],
				word[7],
				0,
				0,
				0,
				0,
			],
			5,
		)
	} else {
		(
			[
				major << 5 | 27,
				word[0],
				word[1],
				word[2],
				word[3],
				word[4],
				word[5],
				word[6],
				word[7],
			],
			9,
		)
	};
	Argument { bytes, length }
}

/// Decode exactly one canonical unsigned argument of the expected major type.
pub(crate) fn decode_argument(input: &[u8], major: u8) -> Option<(u64, usize)> {
	if input.is_empty() {
		return None;
	}
	let header = input[0];
	if header >> 5 != major {
		return None;
	}
	let information = header & 31;
	if information <= 23 {
		return Some((u64::from(information), 1));
	}
	match information {
		24 => {
			if input.len() < 2 {
				return None;
			}
			let value = input[1];
			if value >= 24 {
				Some((u64::from(value), 2))
			} else {
				None
			}
		}
		25 => {
			if input.len() < 3 {
				return None;
			}
			let value = u64::from_be_bytes([0, 0, 0, 0, 0, 0, input[1], input[2]]);
			if value >= 256 { Some((value, 3)) } else { None }
		}
		26 => {
			if input.len() < 5 {
				return None;
			}
			let value = u64::from_be_bytes([0, 0, 0, 0, input[1], input[2], input[3], input[4]]);
			if value >= 65_536 {
				Some((value, 5))
			} else {
				None
			}
		}
		27 => {
			if input.len() < 9 {
				return None;
			}
			let value = u64::from_be_bytes([
				input[1], input[2], input[3], input[4], input[5], input[6], input[7], input[8],
			]);
			if value >= 4_294_967_296 {
				Some((value, 9))
			} else {
				None
			}
		}
		_ => None,
	}
}

pub(crate) fn decode(input: &[u8]) -> Option<Frame<'_>> {
	if input.len() > MAX_MESSAGE_SIZE {
		return None;
	}
	if input.len() < 3 || input[0] != 0x85 || input[1] != 1 || input[2] != 2 {
		return None;
	}
	let rest = &input[3..];
	let (seq, used) = decode_argument(rest, 0)?;
	let rest = &rest[used..];
	let (key_id, used) = decode_argument(rest, 0)?;
	let rest = &rest[used..];
	let (length, used) = decode_argument(rest, 2)?;
	let cipher_text = &rest[used..];
	if length != cipher_text.len() as u64 {
		return None;
	}
	Some(Frame {
		seq,
		key_id,
		cipher_text,
	})
}

fn write_argument(major: u8, value: u64, output: &mut [u8]) -> usize {
	let encoded = encode_argument(major, value);
	output[..encoded.length].copy_from_slice(&encoded.bytes[..encoded.length]);
	encoded.length
}

fn write_header(
	sequence: u64,
	sender: u64,
	payload_length: usize,
	output: &mut [u8],
) -> Option<(usize, usize)> {
	let length = encoded_frame_len(sequence, sender, payload_length)?;
	if output.len() < length {
		return None;
	}
	output[..3].copy_from_slice(&[0x85, 1, 2]);
	let mut offset = 3;
	offset += write_argument(0, sequence, &mut output[offset..]);
	offset += write_argument(0, sender, &mut output[offset..]);
	offset += write_argument(2, payload_length as u64, &mut output[offset..]);
	Some((offset, length))
}

/// Flat borrowed chunks cover the native ciphertext, tag and commitment without nested slice borrows.
pub(crate) fn encode_three(
	sequence: u64,
	sender: u64,
	first: &[u8],
	second: &[u8],
	third: &[u8],
	output: &mut [u8],
) -> usize {
	let Some(prefix_length) = first.len().checked_add(second.len()) else {
		return 0;
	};
	let Some(payload_length) = prefix_length.checked_add(third.len()) else {
		return 0;
	};
	let Some((offset, length)) = write_header(sequence, sender, payload_length, output) else {
		return 0;
	};
	let end = offset + first.len();
	output[offset..end].copy_from_slice(first);
	let offset = end;
	let end = offset + second.len();
	output[offset..end].copy_from_slice(second);
	output[end..length].copy_from_slice(third);
	length
}

pub(crate) fn encode_parts(
	sequence: u64,
	sender: u64,
	parts: &[&[u8]],
	output: &mut [u8],
) -> usize {
	match parts {
		[] => return encode_three(sequence, sender, &[], &[], &[], output),
		[first] => return encode_three(sequence, sender, first, &[], &[], output),
		[first, second] => return encode_three(sequence, sender, first, second, &[], output),
		[first, second, third] => {
			return encode_three(sequence, sender, first, second, third, output);
		}
		_ => {}
	}
	let mut payload_length = 0usize;
	let mut index = 0;
	while index < parts.len() {
		payload_length = match payload_length.checked_add(parts[index].len()) {
			Some(length) => length,
			None => return 0,
		};
		index += 1;
	}
	let Some((mut offset, length)) = write_header(sequence, sender, payload_length, output) else {
		return 0;
	};
	index = 0;
	while index < parts.len() {
		let part = parts[index];
		let end = offset + part.len();
		output[offset..end].copy_from_slice(part);
		offset = end;
		index += 1;
	}
	length
}
