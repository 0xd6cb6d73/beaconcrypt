// SPDX-License-Identifier: 0BSD

use crate::shared::{Decrypted, Encrypted};
#[cfg(test)]
use crate::shared::{SecretArr, roles, systems};
#[cfg(test)]
use beaconcrypt_core::commitment::build_commitment_transcript;
use beaconcrypt_core::commitment::{
	AEAD_KEY_SIZE as CORE_AEAD_KEY_LEN, AEAD_NONCE_SIZE as CORE_AEAD_NONCE_LEN,
	AEAD_TAG_SIZE as CORE_AEAD_TAG_LEN,
};
use beaconcrypt_core::pqxdh::{
	ASSOCIATED_DATA_SIZE as AD_SIZE, INITIAL_RATCHET_KDF_OUTPUT_SIZE, RATCHET_CHAIN_SIZE,
};
#[cfg(test)]
use beaconcrypt_core::pqxdh::{RatchetInitialization, start_initial_ratchet_kdf};
use beaconcrypt_core::ratchet as verified_ratchet;
use beaconcrypt_core::record as verified_record;
use beaconcrypt_core::record_effects as records;
use beaconcrypt_parse::{CryptoFrame, decode_frame};
use libsodium_rs::utils::memcmp;
use libsodium_rs::{crypto_aead, crypto_generichash, crypto_kdf};
use std::ops::{Deref, DerefMut};
use zeroize::{Zeroize, Zeroizing};

pub const KDF_STATE_SIZE: usize = 32usize;
const _: () = assert!(KDF_STATE_SIZE == RATCHET_CHAIN_SIZE);
/// crypto_aead::chacha20poly1305_ietf::KEYBYTES
pub const AEAD_KEY_LEN: usize = 32;
/// crypto_aead::chacha20poly1305_ietf::NPUBBYTES
pub const AEAD_NONCE_LEN: usize = 12;
/// crypto_aead::chacha20poly1305_ietf::ABYTES
pub const AEAD_TAG_LEN: usize = 16;
const _: () = assert!(AEAD_KEY_LEN == CORE_AEAD_KEY_LEN);
const _: () = assert!(AEAD_NONCE_LEN == CORE_AEAD_NONCE_LEN);
const _: () = assert!(AEAD_TAG_LEN == CORE_AEAD_TAG_LEN);
pub const KDF_RATCHET_OUTPUT_LEN: usize = AEAD_KEY_LEN + KDF_STATE_SIZE + AEAD_NONCE_LEN;
const _: () = assert!(KDF_RATCHET_OUTPUT_LEN == verified_ratchet::RATCHET_KDF_OUTPUT_SIZE);
// the maximum amounts of out-of-order messages we tolerate
// cbindgen requires a literal initializer for this public C constant. The
// compile-time assertion keeps it tied to the authoritative core value.
pub const RATCHET_MAX_GAP: u64 = 50;
const _: () = assert!(RATCHET_MAX_GAP == verified_ratchet::RATCHET_MAX_GAP);
pub const COMMITMENT_SIZE: usize = 64;
pub const MESSAGE_OVERHEAD: usize = COMMITMENT_SIZE + AEAD_TAG_LEN;
const _: () = assert!(COMMITMENT_SIZE == verified_record::COMMITMENT_SIZE);
const _: () = assert!(MESSAGE_OVERHEAD == verified_record::MESSAGE_OVERHEAD);

/// Non-secret progress metadata for an established symmetric ratchet.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RatchetStatus {
	send_sequence: u64,
	receive_sequence: u64,
	receive_cache_len: u8,
}

impl RatchetStatus {
	pub const fn send_sequence(self) -> u64 {
		self.send_sequence
	}

	pub const fn receive_sequence(self) -> u64 {
		self.receive_sequence
	}

	pub const fn receive_cache_len(self) -> u8 {
		self.receive_cache_len
	}
}

/// Expected to be bound by [roles::ChainKey] but the compiler doesn't enforce it
#[cfg(test)]
pub type KdfState<Role> = SecretArr<KDF_STATE_SIZE, systems::HkdfSha512, Role>;
#[cfg(test)]
pub type KdfSendState = KdfState<roles::ChainSendKey>;
#[cfg(test)]
pub type KdfRecvState = KdfState<roles::ChainRecvKey>;

pub type AeadKey = crypto_aead::chacha20poly1305_ietf::Key;
pub type AeadNonce = crypto_aead::chacha20poly1305_ietf::Nonce;

/// Execute a core-owned symmetric-ratchet request with HKDF-SHA-512.
///
/// The core fixes both the input and domain label before this executor runs.
/// Production only applies the requested primitive and returns its fixed-width output.
fn symmetric_ratchet_hkdf<const OUTPUT_SIZE: usize>(
	request: &verified_ratchet::SymmetricRatchetKdfRequest,
) -> [u8; OUTPUT_SIZE] {
	let prk = crypto_kdf::hkdf::sha512::extract(None, request.input())
		.expect("HKDF-SHA-512 extract accepts every fixed-width ratchet chain");
	let expanded = Zeroizing::new(
		crypto_kdf::hkdf::sha512::expand(OUTPUT_SIZE, Some(request.info()), &prk)
			.expect("the fixed ratchet output sizes are below the HKDF-SHA-512 limit"),
	);
	let mut output = [0u8; OUTPUT_SIZE];
	output.copy_from_slice(&expanded);
	output
}

pub(crate) fn ratchet_hkdf(
	request: &verified_ratchet::SymmetricRatchetKdfRequest,
) -> verified_ratchet::RatchetKdfResponse {
	verified_ratchet::RatchetKdfResponse::from_bytes(symmetric_ratchet_hkdf(request))
}

pub(crate) fn initial_ratchet_hkdf(
	request: &verified_ratchet::SymmetricRatchetKdfRequest,
) -> [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE] {
	symmetric_ratchet_hkdf(request)
}

#[cfg(test)]
pub(crate) fn finish_initial_ratchet_kdf(
	pending: beaconcrypt_core::pqxdh::InitialRatchetKdfPending,
) -> verified_ratchet::ConcreteRatchetKernel {
	let response = beaconcrypt_core::pqxdh::InitialRatchetKdfResponse::from_bytes(
		initial_ratchet_hkdf(pending.request()),
	);
	beaconcrypt_core::pqxdh::resume_initial_ratchet_kdf(pending, response)
}

#[cfg(any(feature = "server", test))]
pub(crate) type KeyMaterial = verified_ratchet::RatchetMaterial;
#[cfg(test)]
pub(crate) type SendChain = verified_ratchet::RatchetChain;
pub(crate) type RatchetKernel = verified_ratchet::ConcreteRatchetKernel;

pub(crate) struct RatchetKernelSlot {
	kernel: Option<RatchetKernel>,
}

impl RatchetKernelSlot {
	pub(crate) const fn new(kernel: RatchetKernel) -> Self {
		Self {
			kernel: Some(kernel),
		}
	}

	fn take(&mut self) -> RatchetKernel {
		self.kernel
			.take()
			.expect("a ratchet kernel is absent only while its synchronous effect is running")
	}

	fn put(&mut self, kernel: RatchetKernel) {
		assert!(
			self.kernel.is_none(),
			"a completed ratchet effect must return to an empty kernel slot"
		);
		self.kernel = Some(kernel);
	}

	#[cfg(test)]
	pub(crate) fn replace(&mut self, kernel: RatchetKernel) {
		self.kernel = Some(kernel);
	}
}

impl Deref for RatchetKernelSlot {
	type Target = RatchetKernel;

	fn deref(&self) -> &Self::Target {
		self.kernel
			.as_ref()
			.expect("a ratchet kernel is absent only while its synchronous effect is running")
	}
}

impl DerefMut for RatchetKernelSlot {
	fn deref_mut(&mut self) -> &mut Self::Target {
		self.kernel
			.as_mut()
			.expect("a ratchet kernel is absent only while its synchronous effect is running")
	}
}

#[cfg(test)]
fn empty_ratchet_kernel() -> RatchetKernel {
	RatchetKernel::new(
		verified_ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
		verified_ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
	)
}

pub(crate) struct RatchetManager {
	/// Shared refined kernel owning counters, both KDF chains, and concrete receive slots.
	pub(crate) refined: RatchetKernelSlot,
}

impl RatchetManager {
	#[cfg(test)]
	pub(crate) fn default() -> Self {
		Self {
			refined: RatchetKernelSlot::new(empty_ratchet_kernel()),
		}
	}

	pub(crate) const fn from_kernel(refined: RatchetKernel) -> Self {
		Self {
			refined: RatchetKernelSlot::new(refined),
		}
	}

	pub(crate) fn status(&self) -> RatchetStatus {
		RatchetStatus {
			send_sequence: self.refined.send_sequence(),
			receive_sequence: self.refined.receive_sequence(),
			receive_cache_len: self.refined.receive_cache_len(),
		}
	}

	#[cfg(test)]
	pub(crate) fn recv_key(&self, seq: u64) -> Option<&KeyMaterial> {
		(0..self.refined.receive_cache_len()).find_map(|slot| {
			let (sequence, material) = self.refined.receive_entry_at(slot)?;
			(sequence == seq).then_some(material)
		})
	}

	#[cfg(test)]
	pub(crate) fn ratchet_recv(&mut self) -> Option<u64> {
		let target = self.refined.receive_sequence().checked_add(1)?;
		self.ratchet_recv_until(target)
	}

	#[cfg(test)]
	pub(crate) fn ratchet_recv_until(&mut self, until: u64) -> Option<u64> {
		let kernel = self.refined.take();
		let mut effect = verified_ratchet::begin_receive_advance(kernel, until);
		loop {
			effect = match effect {
				verified_ratchet::ReceiveAdvanceEffect::ReceiveAdvanceRejected(kernel) => {
					self.refined.put(kernel);
					return None;
				}
				verified_ratchet::ReceiveAdvanceEffect::ReceiveAdvanceKdfRequested(pending) => {
					let response = ratchet_hkdf(pending.request());
					pending.resume(response)
				}
				verified_ratchet::ReceiveAdvanceEffect::ReceiveAdvanceCompleted {
					kernel,
					target,
				} => {
					self.refined.put(kernel);
					return Some(target);
				}
			};
		}
	}

	#[cfg(test)]
	pub(crate) fn init_ratchets(
		&mut self,
		root: &[u8; KDF_STATE_SIZE],
		initialization: RatchetInitialization,
	) {
		self.refined
			.replace(finish_initial_ratchet_kdf(start_initial_ratchet_kdf(
				root,
				initialization,
			)));
	}

	#[cfg(test)]
	pub(crate) fn complete_recv_key(
		&mut self,
		seq: u64,
		authenticated: bool,
	) -> verified_ratchet::ReceiveDisposition {
		if self.recv_key(seq).is_none() {
			return verified_ratchet::ReceiveDisposition::Missing;
		}
		let kernel = self.refined.take();
		let mut effect = verified_ratchet::begin_receive(kernel, seq, ());
		let opened = loop {
			effect = match effect {
				verified_ratchet::ReceiveEffect::ReceiveRejected { kernel, .. } => {
					self.refined.put(kernel);
					return verified_ratchet::ReceiveDisposition::Missing;
				}
				verified_ratchet::ReceiveEffect::ReceiveKdfRequested(pending) => {
					let response = ratchet_hkdf(pending.request());
					pending.resume(response)
				}
				verified_ratchet::ReceiveEffect::ReceiveOpenRequested(open) => {
					if open.material().is_none() {
						let (kernel, _) = open.reject();
						self.refined.put(kernel);
						return verified_ratchet::ReceiveDisposition::Missing;
					}
					let (kernel, opened) = open.finish(authenticated.then_some(()));
					self.refined.put(kernel);
					break opened;
				}
			};
		};
		if authenticated && opened.is_some() {
			verified_ratchet::ReceiveDisposition::Consumed
		} else if !authenticated {
			verified_ratchet::ReceiveDisposition::Retained
		} else {
			verified_ratchet::ReceiveDisposition::Missing
		}
	}

	#[cfg(test)]
	pub(crate) fn delete_recv_key(&mut self, seq: u64) {
		self.complete_recv_key(seq, true);
	}

	#[cfg(test)]
	pub(crate) fn reset(&mut self) {
		self.refined.replace(empty_ratchet_kernel());
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn send_sequence(&self) -> u64 {
		self.refined.send_sequence()
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn receive_sequence(&self) -> u64 {
		self.refined.receive_sequence()
	}

	/// Number of cached skipped receive keys, without exposing their material.
	#[cfg(any(feature = "server", test))]
	pub(crate) fn receive_cache_len(&self) -> u8 {
		self.refined.receive_cache_len()
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn receive_entry_at(&self, slot: u8) -> Option<(u64, &KeyMaterial)> {
		self.refined.receive_entry_at(slot)
	}

	#[cfg(test)]
	pub(crate) fn send_state(&self) -> &[u8; KDF_STATE_SIZE] {
		self.refined.send_chain().as_bytes()
	}

	#[cfg(test)]
	pub(crate) fn recv_state(&self) -> &[u8; KDF_STATE_SIZE] {
		self.refined.receive_chain().as_bytes()
	}
}

/// Decode exactly one complete message. Trailing bytes, including a second valid
/// frame, are rejected before routing or touching a ratchet.
fn decode_crypto_frame(data: &[u8]) -> Option<CryptoFrame<'_>> {
	decode_frame(data)
}

#[cfg(feature = "server")]
pub(crate) fn encrypted_frame_sender(data: &[u8]) -> Option<u64> {
	Some(decode_crypto_frame(data)?.key_id)
}

#[cfg(test)]
struct SealFrameContext<'a> {
	bytes: &'a [u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &'a [u8; AD_SIZE],
	frame_encoding: bool,
}

#[cfg(test)]
fn seal_frame(
	material: &verified_ratchet::RatchetMaterial,
	key_seq: u64,
	context: &SealFrameContext<'_>,
) -> Option<Encrypted> {
	let key: AeadKey = (*material.key().as_bytes()).into();
	let nonce: AeadNonce = (*material.nonce().as_bytes()).into();
	let (mut plaintext, mut tag) = crypto_aead::chacha20poly1305_ietf::encrypt_detached(
		context.bytes,
		Some(context.associated_data.as_slice()),
		&nonce,
		&key,
	)
	.ok()?;
	let mut commitment = build_commitment(
		material,
		context.associated_data.as_slice(),
		tag.as_slice(),
		key_seq,
		context.sender_kid,
	)?;
	plaintext.append(&mut tag);
	plaintext.append(&mut commitment);
	let buffer = if context.frame_encoding {
		crate::wire::encode_frame(CryptoFrame {
			cipher_text: &plaintext,
			seq: key_seq,
			key_id: context.sender_kid,
		})?
	} else {
		plaintext
	};
	Some(Encrypted {
		ciphertext: buffer,
		key_id: context.target_kid,
		seq: key_seq,
	})
}

/// Encrypt one frame against a staged or committed peer ratchet.
///
/// The extracted record controller advances the send chain and retains the
/// allocated sequence, material and associated data through each primitive
/// request. The native interpreter supplies actual AEAD, hash and writer
/// replies before the controller consumes the selected send material.
pub(crate) fn encrypt_message_with_ratchet(
	bytes: &[u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Encrypted> {
	encrypt_with_ratchet(
		bytes,
		target_kid,
		sender_kid,
		associated_data,
		ratchet,
		true,
	)
}

fn encrypt_with_ratchet(
	bytes: &[u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
	frame_encoding: bool,
) -> Option<Encrypted> {
	if bytes.is_empty() {
		return None;
	}
	if frame_encoding {
		let sequence = ratchet.status().send_sequence().checked_add(1)?;
		crate::wire::frame_len(bytes.len(), sequence, sender_kid)?;
	}
	let encoding = if frame_encoding {
		records::RecordEncoding::Frame
	} else {
		records::RecordEncoding::Raw
	};
	let context =
		records::SealFrameContext::new(bytes, target_kid, sender_kid, associated_data, encoding);
	let (kernel, sealed) = execute_record_send(ratchet.refined.take(), context);
	ratchet.refined.put(kernel);
	sealed
}

/// Execute only the detached AEAD operands selected by the core record phase.
pub(crate) fn execute_seal_request(
	request: records::AeadSealRequest<'_>,
) -> Option<(Vec<u8>, [u8; AEAD_TAG_LEN])> {
	let key: AeadKey = (*request.key).into();
	let nonce: AeadNonce = (*request.nonce).into();
	let prefixed = match &request.plaintext {
		records::SealPlaintextRequest::Single(_) => None,
		records::SealPlaintextRequest::Prefixed {
			prefix,
			application,
		} => Some(Zeroizing::new(join_record_parts([
			prefix.as_slice(),
			*application,
		])?)),
	};
	let plaintext = match request.plaintext {
		records::SealPlaintextRequest::Single(plaintext) => plaintext,
		records::SealPlaintextRequest::Prefixed { .. } => prefixed.as_ref()?.as_slice(),
	};
	let (ciphertext, tag) = crypto_aead::chacha20poly1305_ietf::encrypt_detached(
		plaintext,
		Some(request.associated_data.as_slice()),
		&nonce,
		&key,
	)
	.ok()?;
	Some((ciphertext, tag.as_slice().try_into().ok()?))
}

/// The copied transcript is erased after every hash attempt.
pub(crate) fn execute_commitment_hash(
	transcript: &mut beaconcrypt_core::commitment::CommitmentTranscript,
) -> Option<[u8; COMMITMENT_SIZE]> {
	let commitment =
		crypto_generichash::generichash(transcript.as_bytes(), None, COMMITMENT_SIZE).ok();
	transcript.as_mut_bytes().zeroize();
	commitment?.as_slice().try_into().ok()
}

fn join_record_parts<const N: usize>(parts: [&[u8]; N]) -> Option<Vec<u8>> {
	let length = parts
		.iter()
		.try_fold(0usize, |length, part| length.checked_add(part.len()))?;
	let mut output = Vec::new();
	output.try_reserve_exact(length).ok()?;
	for part in parts {
		output.extend_from_slice(part);
	}
	Some(output)
}

/// Format and metadata come from the core; this function only allocates and encodes.
pub(crate) fn execute_write_request(request: records::RecordWriteRequest<'_>) -> Option<Vec<u8>> {
	match request {
		records::RecordWriteRequest::Raw { parts } => join_record_parts(parts),
		records::RecordWriteRequest::Frame {
			parts,
			sequence,
			sender,
		} => {
			let ciphertext = join_record_parts(parts)?;
			crate::wire::encode_frame(CryptoFrame {
				cipher_text: &ciphertext,
				seq: sequence,
				key_id: sender,
			})
		}
	}
}

pub(crate) fn execute_open_request(
	request: Option<verified_record::AeadRequest<'_>>,
) -> Option<Vec<u8>> {
	let request = request?;
	let key: AeadKey = (*request.key).into();
	let nonce: AeadNonce = (*request.nonce).into();
	crypto_aead::chacha20poly1305_ietf::decrypt(
		request.ciphertext,
		Some(request.associated_data.as_slice()),
		&nonce,
		&key,
	)
	.ok()
}

fn execute_record_send(
	kernel: RatchetKernel,
	context: records::SealFrameContext<'_>,
) -> (RatchetKernel, Option<Encrypted>) {
	let pending = match records::begin_record_send(kernel, context) {
		records::RecordSendStart::Rejected(kernel) => return (kernel, None),
		records::RecordSendStart::KdfRequested(pending) => pending,
	};
	let response = ratchet_hkdf(pending.request());
	let aead = pending.resume(response);
	let detached = execute_seal_request(aead.request());
	let detached_view = detached.as_ref().map(|(body, tag)| (body.as_slice(), *tag));
	let mut commitment = match aead.resume(detached_view) {
		records::SealAfterAead::Rejected(kernel) => return (kernel, None),
		records::SealAfterAead::CommitmentRequested(pending) => pending,
	};
	let digest = execute_commitment_hash(commitment.transcript_mut());
	let writer = match commitment.resume(digest) {
		records::SealAfterCommitment::Rejected(kernel) => return (kernel, None),
		records::SealAfterCommitment::WriteRequested(writer) => writer,
	};
	let written = execute_write_request(writer.request());
	let (kernel, output) = writer.finish(written);
	(
		kernel,
		output.map(|sealed| Encrypted {
			ciphertext: sealed.ciphertext,
			key_id: sealed.key_id,
			seq: sealed.seq,
		}),
	)
}

fn execute_record_receive(
	mut effect: records::RecordReceiveEffect<'_>,
) -> (RatchetKernel, Option<Decrypted>) {
	loop {
		effect = match effect {
			records::RecordReceiveEffect::Rejected(kernel) => return (kernel, None),
			records::RecordReceiveEffect::KdfRequested(pending) => {
				let response = ratchet_hkdf(pending.request());
				pending.resume(response)
			}
			records::RecordReceiveEffect::CommitmentRequested(mut pending) => {
				let actual = execute_commitment_hash(pending.transcript_mut());
				let matches = match actual {
					Some(actual) => memcmp(&actual, pending.supplied_commitment()),
					None => false,
				};
				pending.resume(matches)
			}
			records::RecordReceiveEffect::AeadRequested(pending) => {
				let plaintext = execute_open_request(pending.request());
				let (kernel, opened) = pending.finish(plaintext);
				return (
					kernel,
					opened.map(|opened| Decrypted {
						plaintext: opened.plaintext,
						key_id: opened.key_id,
						seq: opened.seq,
					}),
				);
			}
		};
	}
}

/// Decrypt one frame against a staged or committed peer ratchet.
///
/// Every rejected frame preserves the complete entry ratchet state. Successful authentication
/// atomically publishes the planned receive advance and consumes the selected key through the
/// shared refined kernel. Production interprets each typed KDF request, then opens with the exact
/// material and sequence exposed by the resulting one-use capability.
pub(crate) fn decrypt_message_with_ratchet(
	data: &[u8],
	expected_sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Decrypted> {
	if data.is_empty() {
		return None;
	}
	let frame = decode_crypto_frame(data)?;
	let kid = frame.key_id;
	if kid != expected_sender_kid {
		return None;
	}
	decrypt_payload_with_ratchet(frame.cipher_text, frame.seq, kid, associated_data, ratchet)
}

fn decrypt_payload_with_ratchet(
	ciphertext: &[u8],
	key_seq: u64,
	kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Decrypted> {
	let effect = records::begin_record_receive(
		ratchet.refined.take(),
		key_seq,
		ciphertext,
		associated_data,
		kid,
	);
	let (kernel, opened) = execute_record_receive(effect);
	ratchet.refined.put(kernel);
	opened
}

/// Implementation of the modified Chan and Rogaway `CTX` scheme: <https://eprint.iacr.org/2022/1260.pdf>
/// `CT, T = ENC(K, N, A, M)`
///
/// `T* = H(K, N, A, T, LE64(seq), LE64(kid))`
///
/// The paper omits the original tag from the output. It is included here so we can keep using the libsodium interface
///
/// `CT* = CT || T || T*`
/// This commitment scheme commits to:
/// * Message
/// * Key
/// * Nonce
/// * Associated data
/// * key `seq`
/// * sender key identifier `kid`
#[cfg(test)]
pub(crate) fn build_commitment(
	material: &verified_ratchet::RatchetMaterial,
	ad: &[u8],
	tag: &[u8],
	seq: u64,
	kid: u64,
) -> Option<Vec<u8>> {
	let key = material.key().as_bytes();
	let nonce = material.nonce().as_bytes();
	let ad = ad.try_into().ok()?;
	let tag = tag.try_into().ok()?;
	let mut input = build_commitment_transcript(key, nonce, ad, tag, seq, kid);
	let hash = crypto_generichash::generichash(input.as_bytes(), None, COMMITMENT_SIZE).ok();
	input.as_mut_bytes().zeroize();
	hash
}

#[cfg(test)]
mod raw_receive_tests {
	use super::*;

	#[test]
	fn authenticated_empty_payload_is_rejected_without_state_change() {
		let mut sender = RatchetManager::default();
		let mut receiver = RatchetManager::default();
		let associated_data = [0x42; AD_SIZE];
		let context = SealFrameContext {
			bytes: &[],
			target_kid: 9,
			sender_kid: 7,
			associated_data: &associated_data,
			frame_encoding: true,
		};
		let verified_ratchet::SendStart::SendKdfRequested(pending) =
			verified_ratchet::begin_send(sender.refined.take(), context)
		else {
			panic!("the initial sequence is available")
		};
		let response = ratchet_hkdf(pending.request());
		let seal = pending.resume(response);
		// The primitive supports empty messages; the production protocol excludes them.
		let encrypted = seal_frame(seal.material(), seal.sequence(), seal.context()).unwrap();
		let before = serde_json::to_string(&receiver).unwrap();
		assert!(
			decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &associated_data, &mut receiver)
				.is_none()
		);
		assert_eq!(serde_json::to_string(&receiver).unwrap(), before);
	}

	#[test]
	fn associated_data_mismatch_preserves_the_complete_ratchet() {
		let mut sender = RatchetManager::default();
		let mut receiver = RatchetManager::default();
		let associated_data = [0x51; AD_SIZE];
		let encrypted =
			encrypt_message_with_ratchet(b"payload", 9, 7, &associated_data, &mut sender).unwrap();
		let before = serde_json::to_string(&receiver).unwrap();
		assert!(
			decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &[0x52; AD_SIZE], &mut receiver)
				.is_none()
		);
		assert_eq!(serde_json::to_string(&receiver).unwrap(), before);
		assert_eq!(
			decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &associated_data, &mut receiver)
				.unwrap()
				.plaintext,
			b"payload"
		);
	}

	#[test]
	fn each_mldsa_key_hash_byte_is_bound_without_consuming_a_rejected_key() {
		let mut sender = RatchetManager::default();
		let mut receiver = RatchetManager::default();
		let mut associated_data = [0x51; AD_SIZE];
		associated_data[153..217].fill(0x61);
		associated_data[217..281].fill(0x71);
		let encrypted =
			encrypt_message_with_ratchet(b"payload", 9, 7, &associated_data, &mut sender).unwrap();
		let before = serde_json::to_string(&receiver).unwrap();
		for index in 153..281 {
			let mut changed = associated_data;
			changed[index] ^= 1;
			assert!(
				decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &changed, &mut receiver)
					.is_none(),
				"changed authentication-key hash byte {index} was accepted"
			);
			assert_eq!(serde_json::to_string(&receiver).unwrap(), before);
		}
		assert_eq!(
			decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &associated_data, &mut receiver)
				.unwrap()
				.plaintext,
			b"payload"
		);
		let accepted = serde_json::to_string(&receiver).unwrap();
		assert!(
			decrypt_message_with_ratchet(&encrypted.ciphertext, 7, &associated_data, &mut receiver)
				.is_none()
		);
		assert_eq!(serde_json::to_string(&receiver).unwrap(), accepted);
	}
}

#[cfg(test)]
mod initial_kdf_tests {
	use super::*;
	use beaconcrypt_core::pqxdh::{start_beacon_ratchet_kdf, start_server_ratchet_kdf};

	#[test]
	fn initial_ratchet_hkdf_matches_known_answer_and_orders_complementary_chains() {
		libsodium_rs::ensure_init().unwrap();
		// Independently reproduced by both KAT generators' [ratchet] step 1: HKDF's
		// 64-byte expansion is the prefix of that step's 76-byte expansion.
		let expected_hex = concat!(
			"f57007f1b1c7a62a7d6cdfa5df07538c43d83656906764d607e627401906e42a",
			"5936897d8bd06b7daf70bd0d64b2f607a055fd843ddb779051cb975bbb02b1d3"
		);
		let expected: [u8; 64] = core::array::from_fn(|index| {
			u8::from_str_radix(&expected_hex[index * 2..index * 2 + 2], 16).unwrap()
		});
		let root = [0x24; KDF_STATE_SIZE];
		let beacon_pending = start_beacon_ratchet_kdf(&root);
		assert_eq!(initial_ratchet_hkdf(beacon_pending.request()), expected);
		let beacon = finish_initial_ratchet_kdf(beacon_pending);
		let server = finish_initial_ratchet_kdf(start_server_ratchet_kdf(&root));
		assert_eq!(beacon.receive_chain().as_bytes(), &expected[..32]);
		assert_eq!(beacon.send_chain().as_bytes(), &expected[32..]);
		assert_eq!(server.send_chain().as_bytes(), &expected[..32]);
		assert_eq!(server.receive_chain().as_bytes(), &expected[32..]);

		let changed = start_beacon_ratchet_kdf(&[0x25; KDF_STATE_SIZE]);
		assert_ne!(initial_ratchet_hkdf(changed.request()), expected);
	}
}

#[cfg(test)]
mod record_fixture_tests {
	use super::*;

	#[test]
	fn fixture_sealing_matches_record_requests_and_wire_bytes() {
		libsodium_rs::ensure_init().unwrap();
		let material = verified_ratchet::RatchetMaterial::from_bytes([0x31; 32], [0x52; 12]);
		let associated_data = [0x73; AD_SIZE];
		let sender = 0x8877_6655_4433_2211;
		let target = 0x1020_3040_5060_7080;
		for plaintext in [&[][..], &b"wire compatibility"[..]] {
			for sequence in [1, u64::MAX] {
				for frame_encoding in [false, true] {
					let legacy = seal_frame(
						&material,
						sequence,
						&SealFrameContext {
							bytes: plaintext,
							target_kid: target,
							sender_kid: sender,
							associated_data: &associated_data,
							frame_encoding,
						},
					)
					.unwrap();
					let (body, tag) = execute_seal_request(records::AeadSealRequest {
						key: material.key().as_bytes(),
						nonce: material.nonce().as_bytes(),
						associated_data: &associated_data,
						plaintext: records::SealPlaintextRequest::Single(plaintext),
					})
					.unwrap();
					let mut transcript = build_commitment_transcript(
						material.key().as_bytes(),
						material.nonce().as_bytes(),
						&associated_data,
						&tag,
						sequence,
						sender,
					);
					let commitment = execute_commitment_hash(&mut transcript).unwrap();
					let parts = [body.as_slice(), tag.as_slice(), commitment.as_slice()];
					let request = if frame_encoding {
						records::RecordWriteRequest::Frame {
							parts,
							sequence,
							sender,
						}
					} else {
						records::RecordWriteRequest::Raw { parts }
					};
					assert_eq!(legacy.ciphertext, execute_write_request(request).unwrap());
					assert_eq!(legacy.key_id, target);
					assert_eq!(legacy.seq, sequence);
				}
			}
		}
	}
}
