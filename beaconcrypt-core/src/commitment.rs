// SPDX-License-Identifier: 0BSD

//! Exact fixed-width transcript for the production CTX commitment.
//!
//! Hashing remains in the production adapter.
//! This module owns the ordered byte layout that the hash receives so it can be extracted and proved.

pub const AEAD_KEY_SIZE: usize = 32;
pub const AEAD_NONCE_SIZE: usize = 12;
pub const ASSOCIATED_DATA_SIZE: usize = crate::constants::ASSOCIATED_DATA_SIZE;
pub const AEAD_TAG_SIZE: usize = 16;
pub const ENCODED_U64_SIZE: usize = 8;
pub const COMMITMENT_TRANSCRIPT_SIZE: usize =
	AEAD_KEY_SIZE + AEAD_NONCE_SIZE + ASSOCIATED_DATA_SIZE + AEAD_TAG_SIZE + (2 * ENCODED_U64_SIZE);

// The literal slice bounds in `build_commitment_transcript` are intentionally tied to the public sizes.
// Hax exposes those bounds directly to F*.
const _: () = assert!(AEAD_KEY_SIZE == 32);
const _: () = assert!(AEAD_NONCE_SIZE == 12);
const _: () = assert!(ASSOCIATED_DATA_SIZE == 153);
const _: () = assert!(AEAD_TAG_SIZE == 16);
const _: () = assert!(ENCODED_U64_SIZE == 8);
const _: () = assert!(COMMITMENT_TRANSCRIPT_SIZE == 229);

/// Fixed-width input to the production BLAKE2b-512 commitment operation.
pub struct CommitmentTranscript {
	bytes: [u8; COMMITMENT_TRANSCRIPT_SIZE],
}

impl CommitmentTranscript {
	pub const fn as_bytes(&self) -> &[u8; COMMITMENT_TRANSCRIPT_SIZE] {
		&self.bytes
	}

	/// Mutable access is reserved for the production adapter's zeroization.
	/// The concrete transcript is erased immediately after the opaque hash call.
	pub fn as_mut_bytes(&mut self) -> &mut [u8; COMMITMENT_TRANSCRIPT_SIZE] {
		&mut self.bytes
	}
}

const fn encode_u64_le(value: u64) -> [u8; ENCODED_U64_SIZE] {
	[
		value as u8,
		(value >> 8) as u8,
		(value >> 16) as u8,
		(value >> 24) as u8,
		(value >> 32) as u8,
		(value >> 40) as u8,
		(value >> 48) as u8,
		(value >> 56) as u8,
	]
}

/// Build `key || nonce || associated_data || tag || LE64(sequence) || LE64(sender_id)` without hashing it.
pub fn build_commitment_transcript(
	key: &[u8; AEAD_KEY_SIZE],
	nonce: &[u8; AEAD_NONCE_SIZE],
	associated_data: &[u8; ASSOCIATED_DATA_SIZE],
	tag: &[u8; AEAD_TAG_SIZE],
	sequence: u64,
	sender_id: u64,
) -> CommitmentTranscript {
	let sequence = encode_u64_le(sequence);
	let sender_id = encode_u64_le(sender_id);
	let bytes = core::array::from_fn(|i| {
		if i < 32 {
			key[i]
		} else if i < 44 {
			nonce[i - 32]
		} else if i < 197 {
			associated_data[i - 44]
		} else if i < 213 {
			tag[i - 197]
		} else if i < 221 {
			sequence[i - 213]
		} else {
			sender_id[i - 221]
		}
	});
	CommitmentTranscript { bytes }
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn transcript_has_exact_field_order_and_integer_encoding() {
		let key = core::array::from_fn(|index| index as u8);
		let nonce = core::array::from_fn(|index| 0x20 + index as u8);
		let associated_data = core::array::from_fn(|index| (index as u8).wrapping_add(0x40));
		let tag = core::array::from_fn(|index| 0xE0 + index as u8);
		let sequence = 0x0807_0605_0403_0201;
		let sender_id = 0x1817_1615_1413_1211;

		let transcript =
			build_commitment_transcript(&key, &nonce, &associated_data, &tag, sequence, sender_id);
		let bytes = transcript.as_bytes();

		assert_eq!(&bytes[0..32], &key);
		assert_eq!(&bytes[32..44], &nonce);
		assert_eq!(&bytes[44..197], &associated_data);
		assert_eq!(&bytes[197..213], &tag);
		assert_eq!(&bytes[213..221], &sequence.to_le_bytes());
		assert_eq!(&bytes[221..229], &sender_id.to_le_bytes());
	}
}
