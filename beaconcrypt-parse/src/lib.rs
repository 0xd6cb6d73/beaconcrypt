// SPDX-License-Identifier: 0BSD

//! Deterministic CBOR transport syntax; callers validate cryptographic field contents.

#![no_std]
#![allow(uncommon_codepoints)]

// Generated code uses crate-root module paths. Keep its low-level API private.
#[allow(dead_code, mismatched_lifetime_syntaxes, clippy::all)]
#[rustfmt::skip]
#[path = "generated/cbordetver.rs"]
mod cbordetver;
#[allow(dead_code, mismatched_lifetime_syntaxes, clippy::all)]
#[rustfmt::skip]
#[path = "generated/cbordetveraux.rs"]
mod cbordetveraux;
#[allow(dead_code, mismatched_lifetime_syntaxes, clippy::all)]
#[rustfmt::skip]
#[path = "generated/transport.rs"]
mod transport;

mod lowstar {
	pub mod ignore {
		pub fn ignore<T>(_: T) {}
	}
}

mod sizing;
pub use sizing::{MAX_MESSAGE_SIZE, encoded_frame_len, encoded_init_len, encoded_response_len};
pub use transport::{cryptoframe as CryptoFrame, initkex as InitKex, kexresponse as KexResponse};
use transport::{
	option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t· as ParsedFrame,
	option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t· as ParsedInit,
	option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t· as ParsedResponse,
	validate_and_parse_cryptoframe, validate_and_parse_initkex, validate_and_parse_kexresponse,
};

// Reject containers before the generic generated validator can scan their contents.
// Each schema has a fixed prefix and at most five primitive fields; byte strings
// are skipped without inspecting their payload.
fn preflight(input: &[u8], prefix: &[u8], fields: &[u8]) -> Option<()> {
	if input.len() > MAX_MESSAGE_SIZE {
		return None;
	}
	let mut remaining = input.strip_prefix(prefix)?;
	for &major in fields {
		let (argument, rest) = primitive_argument(remaining, major)?;
		remaining = if major == 2 {
			rest.get(usize::try_from(argument).ok()?..)?
		} else {
			rest
		};
	}
	remaining.is_empty().then_some(())
}

fn primitive_argument(input: &[u8], major: u8) -> Option<(u64, &[u8])> {
	let (&header, rest) = input.split_first()?;
	if header >> 5 != major {
		return None;
	}
	let information = header & 0x1f;
	let width = match information {
		0..=23 => return Some((u64::from(information), rest)),
		24 => 1,
		25 => 2,
		26 => 4,
		27 => 8,
		_ => return None,
	};
	let (encoded, rest) = rest.split_at_checked(width)?;
	let mut word = [0; 8];
	word[8 - width..].copy_from_slice(encoded);
	Some((u64::from_be_bytes(word), rest))
}

/// Encode a frame, returning zero if its complete encoding exceeds the message limit.
pub fn encode_frame(frame: CryptoFrame<'_>, output: &mut [u8]) -> usize {
	if encoded_frame_len(frame.seq, frame.key_id, frame.cipher_text.len()).is_none() {
		return 0;
	}
	transport::serialize_cryptoframe(frame, output)
}

/// Encode a registration request, returning zero if its complete encoding exceeds the limit.
pub fn encode_init(init: InitKex<'_>, output: &mut [u8]) -> usize {
	if encoded_init_len([
		init.identity_key.len(),
		init.pre_key.len(),
		init.one_time_key.len(),
		init.pq_key.len(),
	])
	.is_none()
	{
		return 0;
	}
	transport::serialize_initkex(init, output)
}

/// Encode a registration response, returning zero if its complete encoding exceeds the limit.
pub fn encode_response(response: KexResponse<'_>, output: &mut [u8]) -> usize {
	if encoded_response_len(
		[
			response.identity_key.len(),
			response.ephemeral_key.len(),
			response.kem_cipher_text.len(),
			response.app_cipher_text.len(),
		],
		response.key_id,
	)
	.is_none()
	{
		return 0;
	}
	transport::serialize_kexresponse(response, output)
}

/// Validate and borrow exactly one frame, before routing or touching any ratchet.
pub fn decode_frame(input: &[u8]) -> Option<CryptoFrame<'_>> {
	preflight(input, &[0x85, 1, 2], &[0, 0, 2])?;
	match validate_and_parse_cryptoframe(input) {
		ParsedFrame::Some { v: (frame, []) } => Some(frame),
		_ => None,
	}
}

/// Validate and borrow exactly one registration request.
pub fn decode_init(input: &[u8]) -> Option<InitKex<'_>> {
	preflight(input, &[0x86, 1, 0], &[2, 2, 2, 2])?;
	match validate_and_parse_initkex(input) {
		ParsedInit::Some { v: (init, []) } => Some(init),
		_ => None,
	}
}

/// Validate and borrow exactly one registration response.
pub fn decode_response(input: &[u8]) -> Option<KexResponse<'_>> {
	preflight(input, &[0x87, 1, 1], &[2, 2, 2, 2, 0])?;
	match validate_and_parse_kexresponse(input) {
		ParsedResponse::Some { v: (response, []) } => Some(response),
		_ => None,
	}
}

#[cfg(test)]
mod preflight_tests;
