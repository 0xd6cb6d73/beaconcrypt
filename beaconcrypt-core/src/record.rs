// SPDX-License-Identifier: 0BSD

//! Source-owned admission and borrowed views for a protected record.

#![allow(clippy::question_mark)]

use crate::commitment::{
	AEAD_KEY_SIZE, AEAD_NONCE_SIZE, AEAD_TAG_SIZE, ASSOCIATED_DATA_SIZE, CommitmentTranscript,
	build_commitment_transcript,
};
use crate::ratchet::{ConcreteRatchetKernel, ReceiveOpen};

pub const COMMITMENT_SIZE: usize = 64;
pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE + AEAD_TAG_SIZE;

/// Admit a decoded message only when its reader consumed the complete input.
pub fn finish_frame_read<Message>(remaining: &[u8], message: Message) -> Option<Message> {
	if remaining.is_empty() {
		Some(message)
	} else {
		None
	}
}

/// Borrow all opening fields from one validated payload and its selected owner metadata.
pub struct OpenFrameContext<'a> {
	base_ciphertext: &'a [u8],
	tag: &'a [u8; AEAD_TAG_SIZE],
	commitment: &'a [u8; COMMITMENT_SIZE],
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
	sender_kid: u64,
}

impl<'a> OpenFrameContext<'a> {
	pub fn from_frame(
		ciphertext: &'a [u8],
		associated_data: &[u8; ASSOCIATED_DATA_SIZE],
		sender_kid: u64,
	) -> Option<Self> {
		if ciphertext.len() <= MESSAGE_OVERHEAD {
			return None;
		}
		let (base_ciphertext, supplied_commitment) =
			ciphertext.split_at(ciphertext.len() - COMMITMENT_SIZE);
		let tag = &base_ciphertext[base_ciphertext.len() - AEAD_TAG_SIZE..];
		let tag = match tag.try_into() {
			Ok(tag) => tag,
			Err(_) => return None,
		};
		let commitment = match supplied_commitment.try_into() {
			Ok(commitment) => commitment,
			Err(_) => return None,
		};
		Some(Self {
			base_ciphertext,
			tag,
			commitment,
			associated_data: *associated_data,
			sender_kid,
		})
	}
}

/// A selected opening either rejects before hashing or requests its exact commitment transcript.
// The allocation-free effect retains the original owned kernel, as the ratchet phases do.
#[must_use]
#[allow(clippy::large_enum_variant)]
pub enum OpenStart<'a> {
	OpenRejected(ConcreteRatchetKernel),
	OpenCommitmentRequested(OpenCommitment<'a>),
}

/// The pending hash retains the original one-use ratchet capability.
pub struct OpenCommitment<'a> {
	opening: ReceiveOpen<OpenFrameContext<'a>>,
	pub(crate) transcript: CommitmentTranscript,
}

/// Select the source material, sequence and payload before any primitive effect.
pub fn begin_open(opening: ReceiveOpen<OpenFrameContext<'_>>) -> OpenStart<'_> {
	let material = match opening.material() {
		Some(material) => material,
		None => return OpenStart::OpenRejected(opening.reject().0),
	};
	let context = opening.context();
	let transcript = build_commitment_transcript(
		material.key().as_bytes(),
		material.nonce().as_bytes(),
		&context.associated_data,
		context.tag,
		opening.sequence(),
		context.sender_kid,
	);
	OpenStart::OpenCommitmentRequested(OpenCommitment {
		opening,
		transcript,
	})
}

impl<'a> OpenCommitment<'a> {
	pub const fn transcript(&self) -> &CommitmentTranscript {
		&self.transcript
	}

	/// The primitive executor erases the transcript immediately after hashing it.
	pub fn transcript_mut(&mut self) -> &mut CommitmentTranscript {
		&mut self.transcript
	}

	pub const fn supplied_commitment(&self) -> &[u8; COMMITMENT_SIZE] {
		self.opening.context().commitment
	}

	/// Hash failure and failed constant-time comparison both reject before AEAD.
	pub fn resume(self, commitment_matches: bool) -> OpenAfterCommitment<'a> {
		if !commitment_matches {
			return OpenAfterCommitment::OpenCommitmentRejected(self.opening.reject().0);
		}
		OpenAfterCommitment::OpenAeadRequested(OpenAead {
			opening: self.opening,
		})
	}
}

#[must_use]
#[allow(clippy::large_enum_variant)]
pub enum OpenAfterCommitment<'a> {
	OpenCommitmentRejected(ConcreteRatchetKernel),
	OpenAeadRequested(OpenAead<'a>),
}

/// Only successful commitment verification exposes the selected AEAD request.
pub struct OpenAead<'a> {
	opening: ReceiveOpen<OpenFrameContext<'a>>,
}

/// Primitive inputs borrowed from the same selected material and admitted payload.
pub struct AeadRequest<'a> {
	pub key: &'a [u8; AEAD_KEY_SIZE],
	pub nonce: &'a [u8; AEAD_NONCE_SIZE],
	pub ciphertext: &'a [u8],
	pub associated_data: &'a [u8; ASSOCIATED_DATA_SIZE],
}

/// The actual optional primitive plaintext, paired with the source-selected metadata.
pub struct OpenedRecord<Plaintext> {
	pub plaintext: Plaintext,
	pub key_id: u64,
	pub seq: u64,
}

impl OpenAead<'_> {
	pub fn request(&self) -> Option<AeadRequest<'_>> {
		let material = match self.opening.material() {
			Some(material) => material,
			None => return None,
		};
		let context = self.opening.context();
		Some(AeadRequest {
			key: material.key().as_bytes(),
			nonce: material.nonce().as_bytes(),
			ciphertext: context.base_ciphertext,
			associated_data: &context.associated_data,
		})
	}

	/// Publish through the original capability only after the actual AEAD result.
	pub fn finish<Plaintext>(
		self,
		opened: Option<Plaintext>,
	) -> (ConcreteRatchetKernel, Option<OpenedRecord<Plaintext>>) {
		let plaintext = match opened {
			Some(plaintext) => plaintext,
			None => return self.opening.finish(None),
		};
		let key_id = self.opening.context().sender_kid;
		let seq = self.opening.sequence();
		let opened = OpenedRecord {
			plaintext,
			key_id,
			seq,
		};
		self.opening.finish(Some(opened))
	}
}
