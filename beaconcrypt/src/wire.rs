// SPDX-License-Identifier: 0BSD

//! Allocate output only from trusted slice lengths, and publish successful encodings.

use beaconcrypt_parse::CryptoFrame;
#[cfg(any(feature = "beacon", test))]
use beaconcrypt_parse::InitKex;
#[cfg(any(feature = "server", test))]
use beaconcrypt_parse::KexResponse;

fn encode_record(capacity: usize, serialize: impl FnOnce(&mut [u8]) -> usize) -> Option<Vec<u8>> {
	let mut output = Vec::new();
	output.try_reserve_exact(capacity).ok()?;
	output.resize(capacity, 0);
	let written = serialize(&mut output);
	if written == 0 {
		return None;
	}
	output.truncate(written);
	Some(output)
}

pub(crate) fn encode_frame(frame: CryptoFrame<'_>) -> Option<Vec<u8>> {
	let capacity =
		beaconcrypt_parse::encoded_frame_len(frame.seq, frame.key_id, frame.cipher_text.len())?;
	encode_record(capacity, |output| {
		beaconcrypt_parse::encode_frame(frame, output)
	})
}

/// Exact on-wire length before deriving a key or allocating ciphertext.
pub(crate) fn frame_len(plaintext_len: usize, sequence: u64, sender: u64) -> Option<usize> {
	beaconcrypt_parse::encoded_frame_len(
		sequence,
		sender,
		plaintext_len.checked_add(crate::ratchet::MESSAGE_OVERHEAD)?,
	)
}

#[cfg(any(feature = "beacon", test))]
pub(crate) fn encode_init(init: InitKex<'_>) -> Option<Vec<u8>> {
	let capacity = beaconcrypt_parse::encoded_init_len([
		init.identity_key.len(),
		init.pre_key.len(),
		init.one_time_key.len(),
		init.pq_key.len(),
	])?;
	encode_record(capacity, |output| {
		beaconcrypt_parse::encode_init(init, output)
	})
}

#[cfg(any(feature = "server", test))]
pub(crate) fn encode_response(response: KexResponse<'_>) -> Option<Vec<u8>> {
	let capacity = beaconcrypt_parse::encoded_response_len(
		[
			response.identity_key.len(),
			response.ephemeral_key.len(),
			response.kem_cipher_text.len(),
			response.app_cipher_text.len(),
		],
		response.key_id,
	)?;
	encode_record(capacity, |output| {
		beaconcrypt_parse::encode_response(response, output)
	})
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn overflow_rejects_before_calling_the_encoder() {
		assert!(encode_record(usize::MAX, |_| panic!("encoder must not run")).is_none());
	}

	#[test]
	fn failed_encoder_does_not_publish_partial_output() {
		assert!(
			encode_record(4, |output| {
				output[0] = 7;
				0
			})
			.is_none()
		);
	}

	#[test]
	fn output_bound_handles_full_width_metadata_and_empty_fields() {
		let frame = CryptoFrame {
			seq: u64::MAX,
			key_id: u64::MAX,
			cipher_text: &[],
		};
		assert!(beaconcrypt_parse::decode_frame(&encode_frame(frame).unwrap()) == Some(frame));
		let init = InitKex {
			identity_key: &[],
			pre_key: &[],
			one_time_key: &[],
			pq_key: &[],
		};
		assert!(beaconcrypt_parse::decode_init(&encode_init(init).unwrap()) == Some(init));
		let response = KexResponse {
			identity_key: &[],
			ephemeral_key: &[],
			kem_cipher_text: &[],
			app_cipher_text: &[],
			key_id: u64::MAX,
		};
		assert!(
			beaconcrypt_parse::decode_response(&encode_response(response).unwrap())
				== Some(response)
		);
	}

	#[test]
	fn plaintext_length_checks_include_authentication_overhead() {
		assert!(frame_len(usize::MAX, 1, 0).is_none());
		assert_eq!(
			frame_len(1, 1, 0),
			beaconcrypt_parse::encoded_frame_len(1, 0, 81)
		);
	}
}
