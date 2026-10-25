// SPDX-License-Identifier: 0BSD

//! Composed protected-record phases, with primitive execution left to the adapter.

#![allow(clippy::large_enum_variant, clippy::question_mark)]

use crate::commitment::{
	AEAD_KEY_SIZE, AEAD_NONCE_SIZE, AEAD_TAG_SIZE, ASSOCIATED_DATA_SIZE, CommitmentTranscript,
	build_commitment_transcript,
};
use crate::ratchet::{
	ConcreteRatchetKernel, RatchetKdfResponse, ReceiveEffect, ReceiveKdf, SendKdf, SendSeal,
	SendStart, SymmetricRatchetKdfRequest, begin_receive, begin_send,
};
use crate::record::{
	AeadRequest, COMMITMENT_SIZE, OpenAead, OpenAfterCommitment, OpenCommitment, OpenFrameContext,
	OpenStart, OpenedRecord, begin_open,
};

#[derive(Clone, Copy)]
pub enum RecordEncoding {
	Raw,
	Frame,
}

/// Payload bytes stay borrowed; the prefix and AD belong to this transaction.
pub struct SealFrameContext<'a> {
	plaintext: &'a [u8],
	prefix: Option<[u8; 8]>,
	associated_data: [u8; ASSOCIATED_DATA_SIZE],
	target_kid: u64,
	sender_kid: u64,
	encoding: RecordEncoding,
}

impl<'a> SealFrameContext<'a> {
	pub const fn new(
		plaintext: &'a [u8],
		target_kid: u64,
		sender_kid: u64,
		associated_data: &[u8; ASSOCIATED_DATA_SIZE],
		encoding: RecordEncoding,
	) -> Self {
		Self {
			plaintext,
			prefix: None,
			associated_data: *associated_data,
			target_kid,
			sender_kid,
			encoding,
		}
	}

	/// The assigned-ID prefix is built before the initial raw payload is sealed.
	pub fn registration(
		application: &'a [u8],
		assigned_kid: u64,
		sender_kid: u64,
		associated_data: &[u8; ASSOCIATED_DATA_SIZE],
	) -> Self {
		let prefix = *crate::pqxdh::registration_key_id_binding(assigned_kid).as_bytes();
		Self {
			plaintext: application,
			prefix: Some(prefix),
			associated_data: *associated_data,
			target_kid: assigned_kid,
			sender_kid,
			encoding: RecordEncoding::Raw,
		}
	}

	fn plaintext_request(&self) -> SealPlaintextRequest<'_> {
		match &self.prefix {
			Some(prefix) => SealPlaintextRequest::Prefixed {
				prefix,
				application: self.plaintext,
			},
			None => SealPlaintextRequest::Single(self.plaintext),
		}
	}
}

#[must_use]
pub enum RecordSendStart<'a> {
	Rejected(ConcreteRatchetKernel),
	KdfRequested(RecordSendKdf<'a>),
}

pub struct RecordSendKdf<'a> {
	pending: SendKdf<SealFrameContext<'a>>,
}

/// The transport interpreter performs exact encoded-size admission before entry.
pub fn begin_record_send(
	kernel: ConcreteRatchetKernel,
	context: SealFrameContext<'_>,
) -> RecordSendStart<'_> {
	if context.plaintext.is_empty() && context.prefix.is_none() {
		return RecordSendStart::Rejected(kernel);
	}
	match begin_send(kernel, context) {
		SendStart::SendExhausted { kernel, .. } => RecordSendStart::Rejected(kernel),
		SendStart::SendKdfRequested(pending) => {
			RecordSendStart::KdfRequested(RecordSendKdf { pending })
		}
	}
}

impl<'a> RecordSendKdf<'a> {
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		self.pending.request()
	}

	pub fn cancel(self) -> ConcreteRatchetKernel {
		self.pending.cancel().0
	}

	pub fn resume(self, response: RatchetKdfResponse) -> SealAead<'a> {
		SealAead {
			seal: self.pending.resume(response),
		}
	}
}

/// Exact borrowed application bytes, optionally preceded by the core-owned assigned ID.
pub enum SealPlaintextRequest<'a> {
	Single(&'a [u8]),
	Prefixed {
		prefix: &'a [u8; 8],
		application: &'a [u8],
	},
}

pub struct AeadSealRequest<'a> {
	pub key: &'a [u8; AEAD_KEY_SIZE],
	pub nonce: &'a [u8; AEAD_NONCE_SIZE],
	pub associated_data: &'a [u8; ASSOCIATED_DATA_SIZE],
	pub plaintext: SealPlaintextRequest<'a>,
}

// Retain the concrete failure-reply type through extraction before discarding it.
fn reject_send(pending: SendSeal<SealFrameContext<'_>>) -> (ConcreteRatchetKernel, Option<()>) {
	pending.finish(None)
}

#[must_use]
pub struct SealAead<'a> {
	seal: SendSeal<SealFrameContext<'a>>,
}

pub enum SealAfterAead<'a, 'ciphertext> {
	Rejected(ConcreteRatchetKernel),
	CommitmentRequested(SealCommitment<'a, 'ciphertext>),
}

impl<'a> SealAead<'a> {
	pub fn request(&self) -> AeadSealRequest<'_> {
		let material = self.seal.material();
		let context = self.seal.context();
		AeadSealRequest {
			key: material.key().as_bytes(),
			nonce: material.nonce().as_bytes(),
			associated_data: &context.associated_data,
			plaintext: context.plaintext_request(),
		}
	}

	pub fn resume<'ciphertext>(
		self,
		detached: Option<(&'ciphertext [u8], [u8; AEAD_TAG_SIZE])>,
	) -> SealAfterAead<'a, 'ciphertext> {
		let Some((ciphertext, tag)) = detached else {
			return SealAfterAead::Rejected(reject_send(self.seal).0);
		};
		let material = self.seal.material();
		let context = self.seal.context();
		let transcript = build_commitment_transcript(
			material.key().as_bytes(),
			material.nonce().as_bytes(),
			&context.associated_data,
			&tag,
			self.seal.sequence(),
			context.sender_kid,
		);
		SealAfterAead::CommitmentRequested(SealCommitment {
			seal: self.seal,
			ciphertext,
			tag,
			transcript,
		})
	}
}

#[must_use]
pub struct SealCommitment<'a, 'ciphertext> {
	seal: SendSeal<SealFrameContext<'a>>,
	ciphertext: &'ciphertext [u8],
	tag: [u8; AEAD_TAG_SIZE],
	pub(crate) transcript: CommitmentTranscript,
}

pub enum SealAfterCommitment<'a, 'ciphertext> {
	Rejected(ConcreteRatchetKernel),
	WriteRequested(SealWrite<'a, 'ciphertext>),
}

impl<'a, 'ciphertext> SealCommitment<'a, 'ciphertext> {
	pub const fn transcript(&self) -> &CommitmentTranscript {
		&self.transcript
	}

	pub fn transcript_mut(&mut self) -> &mut CommitmentTranscript {
		&mut self.transcript
	}

	pub fn resume(
		self,
		commitment: Option<[u8; COMMITMENT_SIZE]>,
	) -> SealAfterCommitment<'a, 'ciphertext> {
		let Some(commitment) = commitment else {
			return SealAfterCommitment::Rejected(reject_send(self.seal).0);
		};
		SealAfterCommitment::WriteRequested(SealWrite {
			seal: self.seal,
			ciphertext: self.ciphertext,
			tag: self.tag,
			commitment,
		})
	}
}

pub enum RecordWriteRequest<'a> {
	Raw {
		parts: [&'a [u8]; 3],
	},
	Frame {
		parts: [&'a [u8]; 3],
		sequence: u64,
		sender: u64,
	},
}

#[must_use]
pub struct SealWrite<'a, 'ciphertext> {
	seal: SendSeal<SealFrameContext<'a>>,
	ciphertext: &'ciphertext [u8],
	tag: [u8; AEAD_TAG_SIZE],
	commitment: [u8; COMMITMENT_SIZE],
}

pub struct SealedRecord<Output> {
	pub ciphertext: Output,
	pub key_id: u64,
	pub seq: u64,
}

impl SealWrite<'_, '_> {
	pub fn request(&self) -> RecordWriteRequest<'_> {
		let parts = [
			self.ciphertext,
			self.tag.as_slice(),
			self.commitment.as_slice(),
		];
		match self.seal.context().encoding {
			RecordEncoding::Raw => RecordWriteRequest::Raw { parts },
			RecordEncoding::Frame => RecordWriteRequest::Frame {
				parts,
				sequence: self.seal.sequence(),
				sender: self.seal.context().sender_kid,
			},
		}
	}

	/// Every writer outcome consumes the selected send key, including failure.
	pub fn finish<Output>(
		self,
		written: Option<Output>,
	) -> (ConcreteRatchetKernel, Option<SealedRecord<Output>>) {
		let ciphertext = match written {
			Some(ciphertext) => ciphertext,
			None => return self.seal.finish(None),
		};
		let key_id = self.seal.context().target_kid;
		let seq = self.seal.sequence();
		let output = SealedRecord {
			ciphertext,
			key_id,
			seq,
		};
		self.seal.finish(Some(output))
	}
}

#[must_use]
pub enum RecordReceiveEffect<'a> {
	Rejected(ConcreteRatchetKernel),
	KdfRequested(RecordReceiveKdf<'a>),
	CommitmentRequested(RecordReceiveCommitment<'a>),
	AeadRequested(RecordReceiveAead<'a>),
}

pub struct RecordReceiveKdf<'a> {
	pending: ReceiveKdf<OpenFrameContext<'a>>,
}

pub struct RecordReceiveCommitment<'a> {
	pub(crate) pending: OpenCommitment<'a>,
}

pub struct RecordReceiveAead<'a> {
	pending: OpenAead<'a>,
}

/// The context owns its AD, so no record phase borrows its outer session binding.
pub fn begin_record_receive<'a>(
	kernel: ConcreteRatchetKernel,
	sequence: u64,
	ciphertext: &'a [u8],
	associated_data: &[u8; ASSOCIATED_DATA_SIZE],
	sender: u64,
) -> RecordReceiveEffect<'a> {
	let Some(context) = OpenFrameContext::from_frame(ciphertext, associated_data, sender) else {
		return RecordReceiveEffect::Rejected(kernel);
	};
	normalize_receive(begin_receive(kernel, sequence, context))
}

fn normalize_receive(effect: ReceiveEffect<OpenFrameContext<'_>>) -> RecordReceiveEffect<'_> {
	match effect {
		ReceiveEffect::ReceiveRejected { kernel, .. } => RecordReceiveEffect::Rejected(kernel),
		ReceiveEffect::ReceiveKdfRequested(pending) => {
			RecordReceiveEffect::KdfRequested(RecordReceiveKdf { pending })
		}
		ReceiveEffect::ReceiveOpenRequested(opening) => match begin_open(opening) {
			OpenStart::OpenRejected(kernel) => RecordReceiveEffect::Rejected(kernel),
			OpenStart::OpenCommitmentRequested(pending) => {
				RecordReceiveEffect::CommitmentRequested(RecordReceiveCommitment { pending })
			}
		},
	}
}

impl<'a> RecordReceiveKdf<'a> {
	pub const fn request(&self) -> &SymmetricRatchetKdfRequest {
		self.pending.request()
	}

	pub fn cancel(self) -> ConcreteRatchetKernel {
		self.pending.cancel().0
	}

	pub fn resume(self, response: RatchetKdfResponse) -> RecordReceiveEffect<'a> {
		normalize_receive(self.pending.resume(response))
	}
}

impl<'a> RecordReceiveCommitment<'a> {
	pub const fn transcript(&self) -> &CommitmentTranscript {
		self.pending.transcript()
	}

	pub fn transcript_mut(&mut self) -> &mut CommitmentTranscript {
		&mut self.pending.transcript
	}

	pub const fn supplied_commitment(&self) -> &[u8; COMMITMENT_SIZE] {
		self.pending.supplied_commitment()
	}

	/// The interpreter performs a constant-time commitment comparison.
	pub fn resume(self, commitment_matches: bool) -> RecordReceiveEffect<'a> {
		match self.pending.resume(commitment_matches) {
			OpenAfterCommitment::OpenCommitmentRejected(kernel) => {
				RecordReceiveEffect::Rejected(kernel)
			}
			OpenAfterCommitment::OpenAeadRequested(pending) => {
				RecordReceiveEffect::AeadRequested(RecordReceiveAead { pending })
			}
		}
	}
}

impl RecordReceiveAead<'_> {
	pub fn request(&self) -> Option<AeadRequest<'_>> {
		self.pending.request()
	}

	pub fn finish<Plaintext>(
		self,
		plaintext: Option<Plaintext>,
	) -> (ConcreteRatchetKernel, Option<OpenedRecord<Plaintext>>) {
		self.pending.finish(plaintext)
	}
}
