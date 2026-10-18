#![allow(dead_code)]

use beaconcrypt_parse::{CryptoFrame, KexResponse};

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
