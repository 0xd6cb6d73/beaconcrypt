// SPDX-License-Identifier: 0BSD

//! Transport admission and exact deterministic CBOR lengths.
//!
//! Parsing, allocation and serialization remain outside this module.

#![allow(clippy::question_mark)]

use crate::authentication::MLDSA_SIGNATURE_LEN;
use crate::pqxdh::{MLKEM768_CIPHERTEXT_SIZE, SIGN_PUBLIC_KEY_SIZE, X25519_PUBLIC_KEY_SIZE};
use crate::record::MESSAGE_OVERHEAD;

/// Maximum complete transport message, including every CBOR header: 32 MiB.
pub const MAX_MESSAGE_SIZE: usize = 33_554_432;

/// Default application bytes used by registration without an application payload.
pub const REGISTRATION_WITNESS: [u8; 1] = [0xff];

/// The parser applies this gate before scanning any encoded fields.
pub const fn complete_message_size_admitted(length: usize) -> bool {
	length <= MAX_MESSAGE_SIZE
}

/// Width of one canonical CBOR unsigned argument or byte-string length.
pub const fn argument_len(value: u64) -> usize {
	if value <= 23 {
		1
	} else if value <= 255 {
		2
	} else if value <= 65_535 {
		3
	} else if value <= 4_294_967_295 {
		5
	} else {
		9
	}
}

struct CborLength {
	value: Option<usize>,
}

impl CborLength {
	fn new() -> Self {
		// Array header, protocol version and message kind each occupy one byte.
		Self { value: Some(3) }
	}

	fn integer(self, value: u64) -> Self {
		Self {
			value: match self.value {
				Some(length) => length.checked_add(argument_len(value)),
				None => None,
			},
		}
	}

	fn bytes(self, byte_length: usize) -> Self {
		// usize is at most 64 bits on supported targets.
		let with_header = self.integer(byte_length as u64);
		Self {
			value: match with_header.value {
				Some(length) => length.checked_add(byte_length),
				None => None,
			},
		}
	}

	fn finish(self) -> Option<usize> {
		match self.value {
			Some(length) if complete_message_size_admitted(length) => Some(length),
			_ => None,
		}
	}
}

/// Exact canonical frame size, if the complete encoding fits the message limit.
pub fn encoded_frame_len(sequence: u64, sender: u64, ciphertext_length: usize) -> Option<usize> {
	CborLength::new()
		.integer(sequence)
		.integer(sender)
		.bytes(ciphertext_length)
		.finish()
}

/// Exact request size, in identity/prekey/one-time/PQ/ML-key/signature order.
pub fn encoded_init_len(lengths: [usize; 6]) -> Option<usize> {
	CborLength::new()
		.bytes(lengths[0])
		.bytes(lengths[1])
		.bytes(lengths[2])
		.bytes(lengths[3])
		.bytes(lengths[4])
		.bytes(lengths[5])
		.finish()
}

/// Exact response size, in identity/ephemeral/KEM/application/signature order.
pub fn encoded_response_len(lengths: [usize; 5], assigned_key_id: u64) -> Option<usize> {
	CborLength::new()
		.bytes(lengths[0])
		.bytes(lengths[1])
		.bytes(lengths[2])
		.bytes(lengths[3])
		.integer(assigned_key_id)
		.bytes(lengths[4])
		.finish()
}

/// Admit plaintext before deriving its send key or allocating the protected record.
pub fn protected_frame_len(plaintext_length: usize, sequence: u64, sender: u64) -> Option<usize> {
	let ciphertext_length = match plaintext_length.checked_add(MESSAGE_OVERHEAD) {
		Some(length) => length,
		None => return None,
	};
	encoded_frame_len(sequence, sender, ciphertext_length)
}

/// Include the assigned-ID prefix, authentication overhead and ML signature.
pub fn registration_response_len(application_length: usize, assigned_key_id: u64) -> Option<usize> {
	let bound_length = match application_length.checked_add(8) {
		Some(length) => length,
		None => return None,
	};
	let ciphertext_length = match bound_length.checked_add(MESSAGE_OVERHEAD) {
		Some(length) => length,
		None => return None,
	};
	encoded_response_len(
		[
			SIGN_PUBLIC_KEY_SIZE,
			X25519_PUBLIC_KEY_SIZE,
			MLKEM768_CIPHERTEXT_SIZE,
			ciphertext_length,
			MLDSA_SIGNATURE_LEN,
		],
		assigned_key_id,
	)
}

/// Metadata and borrowed payload from one parsed frame with its expected sender.
pub struct FrameView<'a> {
	pub sequence: u64,
	pub sender: u64,
	pub ciphertext: &'a [u8],
}

/// Sender admission precedes ratchet selection and leaves sequence admission to the ratchet.
pub fn admit_frame(
	sequence: u64,
	sender: u64,
	ciphertext: &[u8],
	expected_sender: u64,
) -> Option<FrameView<'_>> {
	if sender != expected_sender {
		return None;
	}
	Some(FrameView {
		sequence,
		sender,
		ciphertext,
	})
}

/// The exact source-selected application request; borrowing its stored view is external.
pub enum RegistrationApplication<'a> {
	Witness([u8; 1]),
	Provided(&'a [u8]),
}

pub fn normalize_registration_application(
	application: Option<&[u8]>,
) -> RegistrationApplication<'_> {
	match application {
		Some(bytes) => RegistrationApplication::Provided(bytes),
		None => RegistrationApplication::Witness(REGISTRATION_WITNESS),
	}
}
