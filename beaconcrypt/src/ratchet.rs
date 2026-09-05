// SPDX-License-Identifier: 0BSD

use crate::cryptoframe_capnp;
use crate::shared::{Decrypted, Encrypted};
#[cfg(test)]
use crate::shared::{SecretArr, roles, systems};
use beaconcrypt_core::commitment::{
	AEAD_KEY_SIZE as CORE_AEAD_KEY_LEN, AEAD_NONCE_SIZE as CORE_AEAD_NONCE_LEN,
	AEAD_TAG_SIZE as CORE_AEAD_TAG_LEN, build_commitment_transcript,
};
use beaconcrypt_core::pqxdh::{
	ASSOCIATED_DATA_SIZE as AD_SIZE, INITIAL_RATCHET_KDF_OUTPUT_SIZE, RATCHET_CHAIN_SIZE,
};
#[cfg(test)]
use beaconcrypt_core::pqxdh::{RatchetInitialization, start_initial_ratchet_kdf};
use beaconcrypt_core::ratchet as verified_ratchet;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use capnp::serialize::OwnedSegments;
use libsodium_rs::utils::memcmp;
use libsodium_rs::{crypto_aead, crypto_generichash, crypto_kdf};
use std::ops::{Deref, DerefMut};
use std::vec;
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
/// frame, are rejected before routing or touching a ratchet. Cap'n Proto may have
/// multiple encodings of the same fields; this is framing, not canonicalization.
fn decode_crypto_frame(
	data: &[u8],
) -> Option<TypedReader<OwnedSegments, cryptoframe_capnp::crypto_frame::Owned>> {
	let mut remaining = data;
	let reader = capnp::serialize::read_message(&mut remaining, ReaderOptions::new()).ok()?;
	if !remaining.is_empty() {
		return None;
	}
	Some(TypedReader::new(reader))
}

#[cfg(feature = "server")]
pub(crate) fn encrypted_frame_sender(data: &[u8]) -> Option<u64> {
	Some(decode_crypto_frame(data)?.get().ok()?.get_key_id())
}

struct SealFrameContext<'a> {
	bytes: &'a [u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &'a [u8; AD_SIZE],
}

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
	let mut t_builder = TypedBuilder::<cryptoframe_capnp::crypto_frame::Owned>::new_default();
	let mut builder: cryptoframe_capnp::crypto_frame::Builder<'_> = t_builder.init_root();
	builder.set_cipher_text(&plaintext);
	builder.set_seq(key_seq);
	builder.set_key_id(context.sender_kid);
	let mut buffer = vec![];
	capnp::serialize::write_message(&mut buffer, t_builder.borrow_inner()).ok()?;
	Some(Encrypted {
		ciphertext: buffer,
		key_id: context.target_kid,
		seq: key_seq,
	})
}

/// Encrypt one frame against a staged or committed peer ratchet.
///
/// This is shared by the regular high-level provider path and the transactional
/// server-registration path. The extracted kernel advances the send chain,
/// lends the exact allocated sequence/material pair to `seal_frame`, and
/// consumes that pair before returning.
pub(crate) fn encrypt_message_with_ratchet(
	bytes: &[u8],
	target_kid: u64,
	sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Encrypted> {
	if bytes.is_empty() {
		return None;
	}
	let context = SealFrameContext {
		bytes,
		target_kid,
		sender_kid,
		associated_data,
	};
	let kernel = ratchet.refined.take();
	let pending = match verified_ratchet::begin_send(kernel, context) {
		verified_ratchet::SendStart::SendExhausted { kernel, .. } => {
			ratchet.refined.put(kernel);
			return None;
		}
		verified_ratchet::SendStart::SendKdfRequested(pending) => pending,
	};
	let response = ratchet_hkdf(pending.request());
	let seal = pending.resume(response);
	let sealed = seal_frame(seal.material(), seal.sequence(), seal.context());
	let (kernel, sealed) = seal.finish(sealed);
	ratchet.refined.put(kernel);
	sealed
}

/// Validated payload fields borrowed from the single decoded frame. Construction
/// and splitting happen before the ratchet is taken. The AEAD input and CTX tag
/// are views of this same payload, so their provenance cannot diverge later.
struct OpenFrameContext<'a> {
	base_ciphertext: &'a [u8],
	tag: &'a [u8; AEAD_TAG_LEN],
	commitment: &'a [u8; COMMITMENT_SIZE],
	associated_data: &'a [u8; AD_SIZE],
	sender_kid: u64,
}

impl<'a> OpenFrameContext<'a> {
	fn from_frame(
		ciphertext: &'a [u8],
		associated_data: &'a [u8; AD_SIZE],
		sender_kid: u64,
	) -> Option<Self> {
		if ciphertext.len() <= MESSAGE_OVERHEAD {
			return None;
		}
		let (base_ciphertext, commitment) = ciphertext.split_at(ciphertext.len() - COMMITMENT_SIZE);
		let tag = &base_ciphertext[base_ciphertext.len() - AEAD_TAG_LEN..];
		Some(Self {
			base_ciphertext,
			tag: tag.try_into().ok()?,
			commitment: commitment.try_into().ok()?,
			associated_data,
			sender_kid,
		})
	}
}

/// The executor accepts the one-use core request itself. Callers cannot choose
/// an independent sequence, material, or context, or substitute a claimed
/// plaintext. Publication consumes this request only after the primitive result.
fn execute_open(
	open: verified_ratchet::ReceiveOpen<OpenFrameContext<'_>>,
) -> (RatchetKernel, Option<Decrypted>) {
	let opened = (|| {
		let material = open.material()?;
		let context = open.context();
		let key_seq = open.sequence();
		let commitment = build_commitment(
			material,
			context.associated_data.as_slice(),
			context.tag,
			key_seq,
			context.sender_kid,
		)?;
		if !memcmp(&commitment, context.commitment) {
			return None;
		}
		let key: AeadKey = (*material.key().as_bytes()).into();
		let nonce: AeadNonce = (*material.nonce().as_bytes()).into();
		let plaintext = crypto_aead::chacha20poly1305_ietf::decrypt(
			context.base_ciphertext,
			Some(context.associated_data.as_slice()),
			&nonce,
			&key,
		)
		.ok()?;
		Some(Decrypted {
			plaintext,
			key_id: context.sender_kid,
			seq: key_seq,
		})
	})();
	open.finish(opened)
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
	let typed_reader = decode_crypto_frame(data)?;
	let frame = typed_reader.get().ok()?;
	let kid = frame.get_key_id();
	if kid != expected_sender_kid {
		return None;
	}
	let ciphertext = frame.get_cipher_text().ok()?;
	let context = OpenFrameContext::from_frame(ciphertext, associated_data, kid)?;
	let key_seq = frame.get_seq();
	let kernel = ratchet.refined.take();
	let mut effect = verified_ratchet::begin_receive(kernel, key_seq, context);
	loop {
		effect = match effect {
			verified_ratchet::ReceiveEffect::ReceiveRejected { kernel, .. } => {
				ratchet.refined.put(kernel);
				return None;
			}
			verified_ratchet::ReceiveEffect::ReceiveKdfRequested(pending) => {
				let response = ratchet_hkdf(pending.request());
				pending.resume(response)
			}
			verified_ratchet::ReceiveEffect::ReceiveOpenRequested(open) => {
				let (kernel, opened) = execute_open(open);
				ratchet.refined.put(kernel);
				return opened;
			}
		};
	}
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
}
