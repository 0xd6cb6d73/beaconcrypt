// SPDX-License-Identifier: 0BSD

/// Maximum complete encoded transport message, including all CBOR headers: 32 MiB.
pub const MAX_MESSAGE_SIZE: usize = 33_554_432;

/// Exact canonical frame length, if it fits the complete-message limit.
pub fn encoded_frame_len(seq: u64, key_id: u64, cipher_text_len: usize) -> Option<usize> {
	message_len(&[cipher_text_len], &[seq, key_id])
}

/// Exact canonical registration-request length, in identity/prekey/one-time/PQ field order.
pub fn encoded_init_len(lengths: [usize; 4]) -> Option<usize> {
	message_len(&lengths, &[])
}

/// Exact canonical registration-response length, in identity/ephemeral/KEM/application order.
pub fn encoded_response_len(lengths: [usize; 4], key_id: u64) -> Option<usize> {
	message_len(&lengths, &[key_id])
}

fn message_len(byte_lengths: &[usize], integers: &[u64]) -> Option<usize> {
	// The array header, protocol version and message type each occupy one byte.
	let mut length = 3usize;
	for &integer in integers {
		length = length.checked_add(argument_len(integer))?;
	}
	for &byte_length in byte_lengths {
		length = length
			.checked_add(argument_len(u64::try_from(byte_length).ok()?))?
			.checked_add(byte_length)?;
	}
	(length <= MAX_MESSAGE_SIZE).then_some(length)
}

fn argument_len(value: u64) -> usize {
	match value {
		0..=23 => 1,
		24..=255 => 2,
		256..=65_535 => 3,
		65_536..=4_294_967_295 => 5,
		_ => 9,
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn canonical_argument_widths_cover_each_integer_boundary() {
		for (value, width) in [
			(0, 1),
			(23, 1),
			(24, 2),
			(255, 2),
			(256, 3),
			(65_535, 3),
			(65_536, 5),
			(u32::MAX as u64, 5),
			(u32::MAX as u64 + 1, 9),
			(u64::MAX, 9),
		] {
			assert_eq!(argument_len(value), width);
		}
	}

	#[test]
	fn exact_lengths_include_every_header_and_field() {
		assert_eq!(encoded_frame_len(0, 0, 0), Some(6));
		assert_eq!(encoded_frame_len(24, 256, 65_536), Some(65_549));
		assert_eq!(encoded_frame_len(u64::MAX, u64::MAX, 23), Some(45));
		assert_eq!(encoded_init_len([0, 0, 0, 0]), Some(7));
		assert_eq!(encoded_init_len([1, 24, 256, 65_536]), Some(65_831));
		assert_eq!(encoded_response_len([0, 0, 0, 0], 0), Some(8));
		assert_eq!(
			encoded_response_len([1, 24, 256, 65_536], u64::MAX),
			Some(65_840)
		);
	}

	#[test]
	fn complete_message_limit_is_inclusive_for_every_layout_and_integer_width() {
		assert_eq!(MAX_MESSAGE_SIZE, 33_554_432);
		for (seq, key_id, overhead) in [(0, 0, 10), (24, 256, 13), (u64::MAX, u64::MAX, 26)] {
			assert_eq!(
				encoded_frame_len(seq, key_id, MAX_MESSAGE_SIZE - overhead),
				Some(MAX_MESSAGE_SIZE)
			);
			assert_eq!(
				encoded_frame_len(seq, key_id, MAX_MESSAGE_SIZE - overhead + 1),
				None
			);
		}
		for field in 0..4 {
			let mut lengths = [0; 4];
			lengths[field] = MAX_MESSAGE_SIZE - 11;
			assert_eq!(encoded_init_len(lengths), Some(MAX_MESSAGE_SIZE));
			lengths[field] += 1;
			assert_eq!(encoded_init_len(lengths), None);
			for (key_id, overhead) in [(0, 12), (24, 13), (u64::MAX, 20)] {
				lengths[field] = MAX_MESSAGE_SIZE - overhead;
				assert_eq!(
					encoded_response_len(lengths, key_id),
					Some(MAX_MESSAGE_SIZE)
				);
				lengths[field] += 1;
				assert_eq!(encoded_response_len(lengths, key_id), None);
			}
		}
	}

	#[test]
	fn sizing_rejects_usize_overflow_and_oversized_combinations() {
		for impossible in [usize::MAX, usize::MAX - 8, MAX_MESSAGE_SIZE] {
			assert_eq!(encoded_frame_len(0, 0, impossible), None);
			for field in 0..4 {
				let mut lengths = [0; 4];
				lengths[field] = impossible;
				assert_eq!(encoded_init_len(lengths), None);
				assert_eq!(encoded_response_len(lengths, 0), None);
			}
		}
		assert_eq!(encoded_init_len([MAX_MESSAGE_SIZE / 4; 4]), None);
		assert_eq!(encoded_response_len([MAX_MESSAGE_SIZE / 4; 4], 0), None);
		assert_eq!(message_len(&[usize::MAX - 12, 12], &[]), None);
	}
}
