#![allow(dead_code)]

use beaconcrypt_parse::{CryptoFrame, InitKex, KexResponse};

pub fn encode_frame(frame: CryptoFrame<'_>) -> Vec<u8> {
	let mut output = vec![0; frame.cipher_text.len().checked_add(64).unwrap()];
	let written = beaconcrypt_parse::encode_frame(frame, &mut output);
	assert_ne!(written, 0, "test frame encoding must succeed");
	output.truncate(written);
	output
}

pub fn encode_response(response: KexResponse<'_>) -> Vec<u8> {
	let capacity = [
		response.identity_key.len(),
		response.ephemeral_key.len(),
		response.kem_cipher_text.len(),
		response.app_cipher_text.len(),
	]
	.into_iter()
	.try_fold(64usize, usize::checked_add)
	.unwrap();
	let mut output = vec![0; capacity];
	let written = beaconcrypt_parse::encode_response(response, &mut output);
	assert_ne!(written, 0, "test response encoding must succeed");
	output.truncate(written);
	output
}

// Hand-author canonical CBOR so malformed-length fixtures bypass the strict encoders.
pub fn encode_unchecked_init(init: InitKex<'_>) -> Vec<u8> {
	let mut output = vec![0x86, 1, 0];
	for field in [
		init.identity_key,
		init.pre_key,
		init.one_time_key,
		init.pq_key,
	] {
		append_byte_string(&mut output, field);
	}
	output
}

pub fn encode_unchecked_response(response: KexResponse<'_>) -> Vec<u8> {
	let mut output = vec![0x87, 1, 1];
	for field in [
		response.identity_key,
		response.ephemeral_key,
		response.kem_cipher_text,
		response.app_cipher_text,
	] {
		append_byte_string(&mut output, field);
	}
	append_argument(&mut output, 0, response.key_id);
	output
}

fn append_byte_string(output: &mut Vec<u8>, value: &[u8]) {
	append_argument(output, 2, value.len().try_into().unwrap());
	output.extend_from_slice(value);
}

fn append_argument(output: &mut Vec<u8>, major: u8, value: u64) {
	let (information, width) = match value {
		0..=23 => {
			output.push(major << 5 | value as u8);
			return;
		}
		24..=255 => (24, 1),
		256..=65_535 => (25, 2),
		65_536..=4_294_967_295 => (26, 4),
		_ => (27, 8),
	};
	output.push(major << 5 | information);
	output.extend_from_slice(&value.to_be_bytes()[8 - width..]);
}
