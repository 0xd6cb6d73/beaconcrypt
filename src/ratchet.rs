// SPDX-License-Identifier: 0BSD

use crate::cryptoframe_capnp;
use crate::shared::{Decrypted, Encrypted};
#[cfg(test)]
use crate::shared::{SecretArr, roles, systems};
use beaconcrypt_protocol_core::commitment::{
	AEAD_KEY_SIZE as CORE_AEAD_KEY_LEN, AEAD_NONCE_SIZE as CORE_AEAD_NONCE_LEN,
	AEAD_TAG_SIZE as CORE_AEAD_TAG_LEN, build_commitment_transcript,
};
use beaconcrypt_protocol_core::pqxdh::{
	ASSOCIATED_DATA_SIZE as AD_SIZE, INITIAL_RATCHET_KDF_OUTPUT_SIZE, RATCHET_CHAIN_SIZE,
};
#[cfg(test)]
use beaconcrypt_protocol_core::pqxdh::{RatchetInitialization, derive_initial_ratchet_kernel};
use beaconcrypt_protocol_core::ratchet as verified_ratchet;
use capnp::message::{ReaderOptions, TypedBuilder, TypedReader};
use libsodium_rs::utils::memcmp;
use libsodium_rs::{crypto_aead, crypto_generichash, crypto_kdf};
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
) -> [u8; verified_ratchet::RATCHET_KDF_OUTPUT_SIZE] {
	symmetric_ratchet_hkdf(request)
}

pub(crate) fn initial_ratchet_hkdf(
	request: &verified_ratchet::SymmetricRatchetKdfRequest,
) -> [u8; INITIAL_RATCHET_KDF_OUTPUT_SIZE] {
	symmetric_ratchet_hkdf(request)
}

#[cfg(any(feature = "server", test))]
pub(crate) type KeyMaterial = verified_ratchet::RatchetMaterial;
#[cfg(test)]
pub(crate) type SendChain = verified_ratchet::RatchetChain;
pub(crate) type RatchetKernel = verified_ratchet::ConcreteRatchetKernel;

fn empty_ratchet_kernel() -> RatchetKernel {
	RatchetKernel::new(
		verified_ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
		verified_ratchet::RatchetChain::from_bytes([0; KDF_STATE_SIZE]),
		ratchet_hkdf,
	)
}

#[derive(Clone)]
pub struct RatchetManager {
	/// Shared refined kernel owning counters, both KDF chains, and concrete receive slots.
	pub(crate) refined: RatchetKernel,
}

impl RatchetManager {
	pub fn default() -> Self {
		Self {
			refined: empty_ratchet_kernel(),
		}
	}

	pub(crate) const fn from_kernel(refined: RatchetKernel) -> Self {
		Self { refined }
	}

	#[cfg(feature = "server")]
	pub fn from_json(json: String) -> Self {
		serde_json::from_str(&json).unwrap()
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
		let context = TestReceiveAttempt::new(false);
		let _ = verified_ratchet::concrete_open_and_finish(
			&mut self.refined,
			until,
			&context,
			test_receive_attempt,
		);
		context.seen.get()
	}

	#[cfg(test)]
	pub(crate) fn init_ratchets(
		&mut self,
		root: &[u8; KDF_STATE_SIZE],
		initialization: RatchetInitialization,
	) {
		self.refined =
			derive_initial_ratchet_kernel(root, initialization, initial_ratchet_hkdf, ratchet_hkdf);
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
		let context = TestReceiveAttempt::new(authenticated);
		let opened = verified_ratchet::concrete_open_and_finish(
			&mut self.refined,
			seq,
			&context,
			test_receive_attempt,
		);
		if authenticated && opened.is_some() {
			verified_ratchet::ReceiveDisposition::Consumed
		} else if !authenticated && context.seen.get() == Some(seq) {
			verified_ratchet::ReceiveDisposition::Retained
		} else {
			verified_ratchet::ReceiveDisposition::Missing
		}
	}

	#[cfg(test)]
	pub(crate) fn delete_recv_key(&mut self, seq: u64) {
		self.complete_recv_key(seq, true);
	}

	pub fn reset(&mut self) {
		self.refined = empty_ratchet_kernel();
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn send_sequence(&self) -> u64 {
		self.refined.send_sequence()
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn receive_sequence(&self) -> u64 {
		self.refined.receive_sequence()
	}

	/// Number of retained receive attempts, without exposing their material.
	pub fn receive_cache_len(&self) -> u8 {
		self.refined.receive_cache_len()
	}

	#[cfg(any(feature = "server", test))]
	pub(crate) fn receive_entry_at(&self, slot: u8) -> Option<(u64, &KeyMaterial)> {
		self.refined.receive_entry_at(slot)
	}

	pub fn send_state(&self) -> &[u8; KDF_STATE_SIZE] {
		self.refined.send_chain().as_bytes()
	}

	pub fn recv_state(&self) -> &[u8; KDF_STATE_SIZE] {
		self.refined.receive_chain().as_bytes()
	}
}

#[cfg(test)]
struct TestReceiveAttempt {
	seen: core::cell::Cell<Option<u64>>,
	authenticated: bool,
}

#[cfg(test)]
impl TestReceiveAttempt {
	fn new(authenticated: bool) -> Self {
		Self {
			seen: core::cell::Cell::new(None),
			authenticated,
		}
	}
}

#[cfg(test)]
fn test_receive_attempt(
	_material: &verified_ratchet::RatchetMaterial,
	sequence: u64,
	context: &TestReceiveAttempt,
) -> Option<()> {
	context.seen.set(Some(sequence));
	context.authenticated.then_some(())
}

#[cfg(feature = "server")]
pub(crate) fn encrypted_frame_sender(data: &[u8]) -> Option<u64> {
	let reader = capnp::serialize::read_message(data, ReaderOptions::new()).ok()?;
	let typed_reader = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
	Some(typed_reader.get().ok()?.get_key_id())
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
	verified_ratchet::concrete_seal_next(&mut ratchet.refined, &context, seal_frame)
}

struct OpenFrameContext<'a> {
	ciphertext: &'a [u8],
	associated_data: &'a [u8; AD_SIZE],
	sender_kid: u64,
}

fn open_frame(
	material: &verified_ratchet::RatchetMaterial,
	key_seq: u64,
	context: &OpenFrameContext<'_>,
) -> Option<Vec<u8>> {
	let ct_len = context.ciphertext.len();
	if ct_len <= MESSAGE_OVERHEAD {
		return None;
	}
	let commitment = build_commitment(
		material,
		context.associated_data.as_slice(),
		&context.ciphertext[ct_len - COMMITMENT_SIZE - AEAD_TAG_LEN..ct_len - COMMITMENT_SIZE],
		key_seq,
		context.sender_kid,
	)?;
	if !memcmp(&commitment, &context.ciphertext[ct_len - COMMITMENT_SIZE..]) {
		return None;
	}
	let key: AeadKey = (*material.key().as_bytes()).into();
	let nonce: AeadNonce = (*material.nonce().as_bytes()).into();
	crypto_aead::chacha20poly1305_ietf::decrypt(
		&context.ciphertext[..ct_len - COMMITMENT_SIZE],
		Some(context.associated_data.as_slice()),
		&nonce,
		&key,
	)
	.ok()
}

/// Decrypt one frame against a staged or committed peer ratchet.
///
/// Authentication failure retains the exact logical and concrete receive key;
/// successful authentication consumes both through the shared refined kernel.
/// Production supplies one opaque AEAD callback and never receives material or
/// reports an independent authentication Boolean.
pub(crate) fn decrypt_message_with_ratchet(
	data: &[u8],
	expected_sender_kid: u64,
	associated_data: &[u8; AD_SIZE],
	ratchet: &mut RatchetManager,
) -> Option<Decrypted> {
	if data.is_empty() {
		return None;
	}
	let reader = capnp::serialize::read_message(data, ReaderOptions::new()).ok()?;
	let typed_reader = TypedReader::<_, cryptoframe_capnp::crypto_frame::Owned>::new(reader);
	let frame = typed_reader.get().ok()?;
	let kid = frame.get_key_id();
	if kid != expected_sender_kid {
		return None;
	}
	let ciphertext = frame.get_cipher_text().ok()?;
	let ct_len = ciphertext.len();
	if ct_len <= MESSAGE_OVERHEAD {
		return None;
	}
	let context = OpenFrameContext {
		ciphertext,
		associated_data,
		sender_kid: kid,
	};
	let key_seq = frame.get_seq();
	let plaintext = verified_ratchet::concrete_open_and_finish(
		&mut ratchet.refined,
		key_seq,
		&context,
		open_frame,
	)?;
	Some(Decrypted {
		plaintext,
		key_id: kid,
		seq: key_seq,
	})
}

/// implementation of the Chan and Rogaway `CTX` scheme: <https://eprint.iacr.org/2022/1260.pdf>
/// `CT, T = ENC(K, N, A, M)`
///
/// `T* = H(K, N, A, T, LE64(seq), LE64(kid))`
///
/// the paper omits the original tag from the output. It is included here so we can keep using the libsodium interface
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
