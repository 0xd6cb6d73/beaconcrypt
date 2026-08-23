// SPDX-License-Identifier: 0BSD

#[cfg(not(hax_compilation))]
use zeroize::{Zeroize, ZeroizeOnDrop};

mod concrete;
mod control;
mod refined;

pub use concrete::{
	ConcreteRatchetKernel, ConcreteRatchetRestore, ReceiveEffect, ReceiveKdf, ReceiveOpen, SendKdf,
	SendSeal, SendStart, begin_receive, begin_send, concrete_restore_receive_key,
	finish_concrete_restore, start_concrete_restore,
};

#[cfg(any(test, feature = "test-utils"))]
#[doc(hidden)]
pub use concrete::{ReceiveAdvanceEffect, ReceiveAdvanceKdf, begin_receive_advance};
pub use control::{
	PeerRatchetState, PeerSendAdvance, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetRestore,
	RatchetState, ReceiveAdvance, ReceiveDisposition, ReceiveFinish, ReceiveFinishWithRemoval,
	ReceivePlan, ReceiveRemoval, ReceiveRestoreStep, SendAdvance, SendFinish, SendKey,
	SequenceCache, finish_restore, replace_ratchet_for_peer, restore_receive_key,
	restore_receive_key_with_slot, start_restore,
};
pub use refined::{
	CachedReceiveKey, RatchetStep, RefinedRatchet, RefinedRatchetRestore, finish_refined_restore,
	refined_restore_receive_key, start_refined_restore,
};

#[allow(unused_imports)]
pub(crate) use control::{
	advance_receive, advance_receive_target, advance_send, advance_send_for_peer, finish_receive,
	finish_receive_with_removal, finish_send, lookup_receive_key, plan_receive_until,
};
#[allow(unused_imports)]
pub(crate) use refined::refined_receive_key;

#[cfg(test)]
pub(crate) use refined::{
	RefinedSendKey, refined_advance_receive, refined_advance_receive_until, refined_advance_send,
	refined_finish_receive, refined_finish_send, refined_open_and_finish, refined_seal_next,
};

#[cfg(test)]
use refined::{
	PendingReceive, PreparedReceive, empty_material_slots, pending_receive_is_valid,
	pending_receive_slots_are_valid, prepare_receive, publish_future_receive,
	publish_future_receive_slots, receive_control_prefix_matches,
};

/// Fixed width of every symmetric-ratchet root and chain value.
pub const RATCHET_CHAIN_SIZE: usize = 32;

/// Fixed HKDF domain label for initial and subsequent symmetric-ratchet derivations.
pub const SYM_RATCHET_INFO_SIZE: usize = 41;
pub const SYM_RATCHET_INFO: &[u8; SYM_RATCHET_INFO_SIZE] =
	b"SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305";

/// Number of bytes returned by one production symmetric-ratchet HKDF expansion.
pub const RATCHET_KDF_OUTPUT_SIZE: usize =
	crate::commitment::AEAD_KEY_SIZE + RATCHET_CHAIN_SIZE + crate::commitment::AEAD_NONCE_SIZE;

const _: () = assert!(RATCHET_KDF_OUTPUT_SIZE == 76);

/// Fixed-width symmetric-ratchet chain bytes owned by the extracted boundary.
#[cfg_attr(
	feature = "proverif",
	hax_lib::fstar::before("friend Beaconcrypt_core.Ratchet.Refined")
)]
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct RatchetChain {
	bytes: [u8; RATCHET_CHAIN_SIZE],
}

impl RatchetChain {
	pub const fn from_bytes(bytes: [u8; RATCHET_CHAIN_SIZE]) -> Self {
		Self { bytes }
	}

	pub const fn as_bytes(&self) -> &[u8; RATCHET_CHAIN_SIZE] {
		&self.bytes
	}

	pub fn into_bytes(self) -> [u8; RATCHET_CHAIN_SIZE] {
		self.bytes
	}
}

/// Fixed-width symmetric-ratchet message-key bytes owned by the extracted boundary.
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct RatchetKey {
	bytes: [u8; crate::commitment::AEAD_KEY_SIZE],
}

impl RatchetKey {
	pub const fn from_bytes(bytes: [u8; crate::commitment::AEAD_KEY_SIZE]) -> Self {
		Self { bytes }
	}

	pub const fn as_bytes(&self) -> &[u8; crate::commitment::AEAD_KEY_SIZE] {
		&self.bytes
	}

	pub fn into_bytes(self) -> [u8; crate::commitment::AEAD_KEY_SIZE] {
		self.bytes
	}
}

/// Fixed-width symmetric-ratchet AEAD nonce bytes owned by the extracted boundary.
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct RatchetNonce {
	bytes: [u8; crate::commitment::AEAD_NONCE_SIZE],
}

impl RatchetNonce {
	pub const fn from_bytes(bytes: [u8; crate::commitment::AEAD_NONCE_SIZE]) -> Self {
		Self { bytes }
	}

	pub const fn as_bytes(&self) -> &[u8; crate::commitment::AEAD_NONCE_SIZE] {
		&self.bytes
	}

	pub fn into_bytes(self) -> [u8; crate::commitment::AEAD_NONCE_SIZE] {
		self.bytes
	}
}

/// Fixed-width key and nonce produced by one symmetric-ratchet step.
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct RatchetMaterial {
	key: RatchetKey,
	nonce: RatchetNonce,
}

impl RatchetMaterial {
	pub const fn from_parts(key: RatchetKey, nonce: RatchetNonce) -> Self {
		Self { key, nonce }
	}

	pub const fn from_bytes(
		key: [u8; crate::commitment::AEAD_KEY_SIZE],
		nonce: [u8; crate::commitment::AEAD_NONCE_SIZE],
	) -> Self {
		Self {
			key: RatchetKey::from_bytes(key),
			nonce: RatchetNonce::from_bytes(nonce),
		}
	}

	pub const fn key(&self) -> &RatchetKey {
		&self.key
	}

	pub const fn nonce(&self) -> &RatchetNonce {
		&self.nonce
	}
}

/// Core-owned invocation of the symmetric-ratchet KDF domain.
///
/// Both fields are private so an executor can read but cannot alter the exact
/// input or protocol label selected by the core transition that created it.
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct SymmetricRatchetKdfRequest {
	input: [u8; RATCHET_CHAIN_SIZE],
	info: [u8; SYM_RATCHET_INFO_SIZE],
}

impl SymmetricRatchetKdfRequest {
	pub(crate) const fn new(input: [u8; RATCHET_CHAIN_SIZE]) -> Self {
		Self {
			input,
			info: *SYM_RATCHET_INFO,
		}
	}

	pub const fn input(&self) -> &[u8; RATCHET_CHAIN_SIZE] {
		&self.input
	}

	pub const fn info(&self) -> &[u8; SYM_RATCHET_INFO_SIZE] {
		&self.info
	}
}

/// Fixed-width response to one core-owned symmetric-ratchet KDF request.
///
/// Keeping this response distinct from the initial 64-byte response prevents
/// cross-phase width confusion. The type does not prove which pending request
/// produced the bytes; request/response provenance and cryptographic correctness
/// remain obligations of the external interpreter.
#[cfg_attr(not(hax_compilation), derive(Zeroize, ZeroizeOnDrop))]
pub struct RatchetKdfResponse {
	bytes: [u8; RATCHET_KDF_OUTPUT_SIZE],
}

impl RatchetKdfResponse {
	pub const fn from_bytes(bytes: [u8; RATCHET_KDF_OUTPUT_SIZE]) -> Self {
		Self { bytes }
	}

	pub const fn as_bytes(&self) -> &[u8; RATCHET_KDF_OUTPUT_SIZE] {
		&self.bytes
	}
}

/// Proof-visible owned partition of one symmetric-ratchet HKDF expansion.
pub struct RatchetKdfOutput {
	key: RatchetKey,
	next_chain: RatchetChain,
	nonce: RatchetNonce,
}

impl RatchetKdfOutput {
	pub const fn key(&self) -> &RatchetKey {
		&self.key
	}

	pub const fn next_chain(&self) -> &RatchetChain {
		&self.next_chain
	}

	pub const fn nonce(&self) -> &RatchetNonce {
		&self.nonce
	}
}

/// Split `key || next_chain || nonce` into fixed-width values at the protocol's exact offsets.
pub fn split_ratchet_kdf_output(output: &[u8; RATCHET_KDF_OUTPUT_SIZE]) -> RatchetKdfOutput {
	let key = core::array::from_fn(|i| output[i]);

	let next_chain = core::array::from_fn(|i| output[i + crate::commitment::AEAD_KEY_SIZE]);

	let nonce =
		core::array::from_fn(|i| output[i + crate::commitment::AEAD_KEY_SIZE + RATCHET_CHAIN_SIZE]);

	RatchetKdfOutput {
		key: RatchetKey::from_bytes(key),
		next_chain: RatchetChain::from_bytes(next_chain),
		nonce: RatchetNonce::from_bytes(nonce),
	}
}

#[cfg(test)]
mod tests {
	extern crate std;

	use core::cell::Cell;
	use core::sync::atomic::{AtomicU64, Ordering};
	use std::thread;

	use super::{
		CachedReceiveKey, ConcreteRatchetKernel, PeerRatchetState, PendingReceive, PreparedReceive,
		RATCHET_KDF_OUTPUT_SIZE, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetChain,
		RatchetKdfResponse, RatchetKey, RatchetMaterial, RatchetNonce, RatchetState, RatchetStep,
		ReceiveDisposition, ReceiveEffect, ReceiveOpen, RefinedRatchet, RefinedSendKey,
		SYM_RATCHET_INFO, SendKey, SequenceCache, SymmetricRatchetKdfRequest, advance_receive,
		advance_receive_target, advance_send, advance_send_for_peer, begin_receive, begin_send,
		empty_material_slots, finish_receive, finish_receive_with_removal, finish_refined_restore,
		finish_restore, finish_send, lookup_receive_key, pending_receive_is_valid,
		pending_receive_slots_are_valid, plan_receive_until, prepare_receive,
		publish_future_receive, publish_future_receive_slots, receive_control_prefix_matches,
		refined_advance_receive, refined_advance_receive_until, refined_advance_send,
		refined_finish_receive, refined_finish_send, refined_open_and_finish, refined_receive_key,
		refined_restore_receive_key, refined_seal_next, replace_ratchet_for_peer,
		restore_receive_key, restore_receive_key_with_slot, split_ratchet_kdf_output,
		start_refined_restore, start_restore,
	};

	#[test]
	fn owned_ratchet_bytes_round_trip_through_wrappers() {
		let chain = [0x23; super::RATCHET_CHAIN_SIZE];
		let key = [0x45; crate::commitment::AEAD_KEY_SIZE];
		let nonce = [0x67; crate::commitment::AEAD_NONCE_SIZE];

		assert_eq!(RatchetChain::from_bytes(chain).into_bytes(), chain);
		assert_eq!(RatchetKey::from_bytes(key).into_bytes(), key);
		assert_eq!(RatchetNonce::from_bytes(nonce).into_bytes(), nonce);
	}

	#[derive(Debug, Eq, PartialEq)]
	struct TestMaterial {
		generation: u64,
	}

	#[derive(Debug, Eq, PartialEq)]
	struct TestRatchetSnapshot {
		control: RatchetState,
		send_chain: u64,
		receive_chain: u64,
		receive_slots: [Option<(u64, u64)>; RECEIVE_CACHE_CAPACITY],
	}

	fn test_snapshot(state: &RefinedRatchet<u64, u64, TestMaterial>) -> TestRatchetSnapshot {
		TestRatchetSnapshot {
			control: state.control,
			send_chain: state.send_chain,
			receive_chain: state.receive_chain,
			receive_slots: core::array::from_fn(|slot| {
				state.receive_slots[slot]
					.as_ref()
					.map(|cached| (cached.sequence, cached.material.generation))
			}),
		}
	}

	fn test_step(chain: &u64) -> RatchetStep<u64, TestMaterial> {
		let next = chain + 1;
		RatchetStep {
			chain: next,
			material: TestMaterial { generation: next },
		}
	}

	static TEST_STEP_CALLS: AtomicU64 = AtomicU64::new(0);

	fn counting_test_step(chain: &u64) -> RatchetStep<u64, TestMaterial> {
		TEST_STEP_CALLS.fetch_add(1, Ordering::Relaxed);
		test_step(chain)
	}

	fn test_derivation(mut chain: u64, iterations: u64) -> (u64, Option<TestMaterial>) {
		let mut material = None;
		for _ in 0..iterations {
			let stepped = test_step(&chain);
			chain = stepped.chain;
			material = Some(stepped.material);
		}
		(chain, material)
	}

	fn test_is_reachable(
		initial_send_chain: u64,
		initial_receive_chain: u64,
		state: &RefinedRatchet<u64, u64, TestMaterial>,
	) -> bool {
		let (expected_send_chain, _) = test_derivation(initial_send_chain, state.send_sequence());
		let (expected_receive_chain, _) =
			test_derivation(initial_receive_chain, state.receive_sequence());
		if !(state.send_chain() == &expected_send_chain)
			|| !(state.receive_chain() == &expected_receive_chain)
		{
			return false;
		}

		for slot in 0..state.receive_cache_len() {
			let Some((sequence, material)) = state.receive_entry_at(slot) else {
				return false;
			};
			let (_, Some(expected_material)) = test_derivation(initial_receive_chain, sequence)
			else {
				return false;
			};
			if !(material == &expected_material) {
				return false;
			}
		}
		true
	}

	fn rejected_test_step(_chain: &u64) -> RatchetStep<u64, TestMaterial> {
		panic!("rejected receive transaction invoked its KDF callback")
	}

	struct TestAeadContext {
		marker: u64,
		authenticated: bool,
		calls: core::cell::Cell<u64>,
		seen_sequence: core::cell::Cell<Option<u64>>,
		seen_generation: core::cell::Cell<Option<u64>>,
	}

	impl TestAeadContext {
		fn new(marker: u64, authenticated: bool) -> Self {
			Self {
				marker,
				authenticated,
				calls: core::cell::Cell::new(0),
				seen_sequence: core::cell::Cell::new(None),
				seen_generation: core::cell::Cell::new(None),
			}
		}
	}

	fn test_aead(
		material: &TestMaterial,
		sequence: u64,
		context: &TestAeadContext,
	) -> Option<(u64, u64, u64)> {
		context.calls.set(context.calls.get() + 1);
		context.seen_sequence.set(Some(sequence));
		context.seen_generation.set(Some(material.generation));
		context
			.authenticated
			.then_some((sequence, material.generation, context.marker))
	}

	fn test_ratchet_kdf(request: &SymmetricRatchetKdfRequest) -> [u8; RATCHET_KDF_OUTPUT_SIZE] {
		assert_eq!(request.info(), SYM_RATCHET_INFO);
		let old_chain = request.input();
		let output: [u8; RATCHET_KDF_OUTPUT_SIZE] = core::array::from_fn(|i| {
			if i < 32 {
				old_chain[i]
			} else if i < 64 {
				old_chain[i - 32]
			} else {
				old_chain[i - 64]
			}
		});
		output
	}

	fn execute_receive_plan(mut state: RatchetState, target: u64) -> RatchetState {
		let plan = plan_receive_until(state, target);
		assert_eq!(plan.sequence, Some(target));
		for _ in 0..plan.derivations {
			let advanced = advance_receive(state);
			assert!(advanced.sequence.is_some());
			state = advanced.state;
		}
		state
	}

	#[test]
	fn ratchet_kdf_output_split_uses_every_exact_byte_range() {
		let output = core::array::from_fn::<_, RATCHET_KDF_OUTPUT_SIZE, _>(|index| index as u8);
		let split = split_ratchet_kdf_output(&output);

		assert_eq!(split.key().as_bytes(), &output[0..32]);
		assert_eq!(split.next_chain().as_bytes(), &output[32..64]);
		assert_eq!(split.nonce().as_bytes(), &output[64..76]);
	}

	#[test]
	fn concrete_ratchet_step_passes_the_exact_old_chain_to_the_opaque_kdf() {
		let old_chain = core::array::from_fn::<_, 32, _>(|index| index as u8);
		let kernel = ConcreteRatchetKernel::new(
			RatchetChain::from_bytes(old_chain),
			RatchetChain::from_bytes([0; super::RATCHET_CHAIN_SIZE]),
		);
		let super::SendStart::SendKdfRequested(kdf) = begin_send(kernel, ()) else {
			panic!("fresh send unexpectedly exhausted");
		};
		assert_eq!(kdf.request().input(), &old_chain);
		let response = RatchetKdfResponse::from_bytes(test_ratchet_kdf(kdf.request()));
		let seal = kdf.resume(response);

		assert_eq!(seal.material().key().as_bytes(), &old_chain);
		assert_eq!(seal.material().nonce().as_bytes(), &old_chain[0..12]);
		let (kernel, _) = seal.finish::<()>(None);
		assert_eq!(kernel.send_chain().as_bytes(), &old_chain);
	}

	fn drive_receive_to_open<Context>(mut effect: ReceiveEffect<Context>) -> ReceiveOpen<Context> {
		loop {
			effect = match effect {
				ReceiveEffect::ReceiveRejected { .. } => {
					panic!("admitted receive unexpectedly rejected");
				}
				ReceiveEffect::ReceiveKdfRequested(kdf) => {
					let response = RatchetKdfResponse::from_bytes(test_ratchet_kdf(kdf.request()));
					kdf.resume(response)
				}
				ReceiveEffect::ReceiveOpenRequested(open) => return open,
			};
		}
	}

	#[test]
	fn concrete_send_failure_keeps_the_advanced_kernel() {
		let send_chain = [0x31; super::RATCHET_CHAIN_SIZE];
		let receive_chain = [0x52; super::RATCHET_CHAIN_SIZE];
		let kernel = ConcreteRatchetKernel::new(
			RatchetChain::from_bytes(send_chain),
			RatchetChain::from_bytes(receive_chain),
		);
		let super::SendStart::SendKdfRequested(kdf) = begin_send(kernel, 77u64) else {
			panic!("fresh send unexpectedly exhausted");
		};
		assert_eq!(kdf.request().input(), &send_chain);
		let response = RatchetKdfResponse::from_bytes(test_ratchet_kdf(kdf.request()));
		let seal = kdf.resume(response);
		assert_eq!(seal.sequence(), 1);
		assert_eq!(seal.context(), &77);
		let (kernel, output) = seal.finish::<()>(None);

		assert!(output.is_none());
		assert_eq!(kernel.send_sequence(), 1);
		assert_eq!(kernel.receive_sequence(), 0);
		assert_eq!(kernel.send_chain().as_bytes(), &send_chain);
		assert_eq!(kernel.receive_chain().as_bytes(), &receive_chain);
	}

	#[test]
	fn concrete_effect_cancellation_and_rejection_restore_the_entry_kernel() {
		let send_chain = [0x31; super::RATCHET_CHAIN_SIZE];
		let receive_chain = [0x52; super::RATCHET_CHAIN_SIZE];
		let kernel = ConcreteRatchetKernel::new(
			RatchetChain::from_bytes(send_chain),
			RatchetChain::from_bytes(receive_chain),
		);
		let super::SendStart::SendKdfRequested(send) = begin_send(kernel, 71u64) else {
			panic!("fresh send unexpectedly exhausted");
		};
		let (kernel, context) = send.cancel();
		assert_eq!(context, 71);
		assert_eq!(kernel.send_sequence(), 0);
		assert_eq!(kernel.receive_sequence(), 0);
		assert_eq!(kernel.send_chain().as_bytes(), &send_chain);
		assert_eq!(kernel.receive_chain().as_bytes(), &receive_chain);

		let ReceiveEffect::ReceiveKdfRequested(receive) = begin_receive(kernel, 3, 72u64) else {
			panic!("future receive unexpectedly skipped its KDF phase");
		};
		let (kernel, context) = receive.cancel();
		assert_eq!(context, 72);
		assert_eq!(kernel.send_sequence(), 0);
		assert_eq!(kernel.receive_sequence(), 0);
		assert_eq!(kernel.receive_cache_len(), 0);
		assert_eq!(kernel.send_chain().as_bytes(), &send_chain);
		assert_eq!(kernel.receive_chain().as_bytes(), &receive_chain);

		let open = drive_receive_to_open(begin_receive(kernel, 3, 73u64));
		let (kernel, context) = open.reject();
		assert_eq!(context, 73);
		assert_eq!(kernel.send_sequence(), 0);
		assert_eq!(kernel.receive_sequence(), 0);
		assert_eq!(kernel.receive_cache_len(), 0);
		assert_eq!(kernel.send_chain().as_bytes(), &send_chain);
		assert_eq!(kernel.receive_chain().as_bytes(), &receive_chain);
	}

	#[test]
	fn concrete_receive_effect_publishes_only_after_open_success() {
		let send_chain = [0x31; super::RATCHET_CHAIN_SIZE];
		let receive_chain = [0x52; super::RATCHET_CHAIN_SIZE];
		let kernel = ConcreteRatchetKernel::new(
			RatchetChain::from_bytes(send_chain),
			RatchetChain::from_bytes(receive_chain),
		);
		let open = drive_receive_to_open(begin_receive(kernel, 3, 91u64));
		assert_eq!(open.sequence(), 3);
		assert_eq!(open.context(), &91);
		assert!(open.material().is_some());
		let (kernel, rejected) = open.finish::<u64>(None);

		assert!(rejected.is_none());
		assert_eq!(kernel.receive_sequence(), 0);
		assert_eq!(kernel.receive_cache_len(), 0);
		assert_eq!(kernel.receive_chain().as_bytes(), &receive_chain);

		let open = drive_receive_to_open(begin_receive(kernel, 3, 92u64));
		let (kernel, accepted) = open.finish(Some(123u64));
		assert_eq!(accepted, Some(123));
		assert_eq!(kernel.receive_sequence(), 3);
		assert_eq!(kernel.receive_cache_len(), 2);
		assert_eq!(kernel.receive_entry_at(0).map(|entry| entry.0), Some(1));
		assert_eq!(kernel.receive_entry_at(1).map(|entry| entry.0), Some(2));

		let cached = drive_receive_to_open(begin_receive(kernel, 1, 93u64));
		assert_eq!(cached.sequence(), 1);
		assert!(cached.material().is_some());
		let (kernel, accepted) = cached.finish(Some(456u64));
		assert_eq!(accepted, Some(456));
		assert_eq!(kernel.receive_sequence(), 3);
		assert_eq!(kernel.receive_cache_len(), 1);
		assert_eq!(kernel.receive_entry_at(0).map(|entry| entry.0), Some(2));
	}

	#[test]
	fn concrete_receive_accepts_fifty_skipped_keys_without_caching_the_target() {
		let initial_chain = [0x52; super::RATCHET_CHAIN_SIZE];
		let kernel = ConcreteRatchetKernel::new(
			RatchetChain::from_bytes([0x31; super::RATCHET_CHAIN_SIZE]),
			RatchetChain::from_bytes(initial_chain),
		);
		let boundary = RATCHET_MAX_GAP + 1;
		let mut derivations = 0u64;
		let mut effect = begin_receive(kernel, boundary, ());
		let open = loop {
			effect = match effect {
				ReceiveEffect::ReceiveRejected { .. } => {
					panic!("fifty skipped keys must be admitted")
				}
				ReceiveEffect::ReceiveKdfRequested(kdf) => {
					derivations += 1;
					let response = RatchetKdfResponse::from_bytes(test_ratchet_kdf(kdf.request()));
					kdf.resume(response)
				}
				ReceiveEffect::ReceiveOpenRequested(open) => break open,
			};
		};

		assert_eq!(derivations, RATCHET_MAX_GAP + 1);
		assert_eq!(open.sequence(), boundary);
		let (kernel, opened) = open.finish(Some(()));
		assert_eq!(opened, Some(()));
		assert_eq!(kernel.receive_sequence(), boundary);
		assert_eq!(kernel.receive_cache_len() as usize, RECEIVE_CACHE_CAPACITY);
		for slot in 0..RECEIVE_CACHE_CAPACITY as u8 {
			assert_eq!(
				kernel.receive_entry_at(slot).map(|entry| entry.0),
				Some(slot as u64 + 1)
			);
		}
		assert!(
			(0..kernel.receive_cache_len())
				.all(|slot| kernel.receive_entry_at(slot).unwrap().0 != boundary)
		);

		// A full skipped-key cache does not block the separately derived next target.
		let next = drive_receive_to_open(begin_receive(kernel, boundary + 1, ()));
		assert_eq!(next.sequence(), boundary + 1);
		let (kernel, opened) = next.finish(Some(()));
		assert_eq!(opened, Some(()));
		assert_eq!(kernel.receive_sequence(), boundary + 1);
		assert_eq!(kernel.receive_cache_len() as usize, RECEIVE_CACHE_CAPACITY);
	}

	#[test]
	fn concrete_receive_accepts_fifty_skipped_keys_at_counter_exhaustion() {
		let entry_sequence = u64::MAX - (RATCHET_MAX_GAP + 1);
		let kernel = ConcreteRatchetKernel::from_counters(
			0,
			entry_sequence,
			RatchetChain::from_bytes([0x31; super::RATCHET_CHAIN_SIZE]),
			RatchetChain::from_bytes([0x52; super::RATCHET_CHAIN_SIZE]),
		);
		let open = drive_receive_to_open(begin_receive(kernel, u64::MAX, ()));
		assert_eq!(open.sequence(), u64::MAX);
		let (kernel, opened) = open.finish(Some(()));

		assert_eq!(opened, Some(()));
		assert_eq!(kernel.receive_sequence(), u64::MAX);
		assert_eq!(kernel.receive_cache_len() as usize, RECEIVE_CACHE_CAPACITY);
		assert!(
			(0..kernel.receive_cache_len())
				.all(|slot| kernel.receive_entry_at(slot).unwrap().0 != u64::MAX)
		);
	}

	#[test]
	fn rejected_max_gap_open_fits_in_a_constrained_stack() {
		const STACK_SIZE: usize = 256 * 1024;
		let initial_chain = [0x23; super::RATCHET_CHAIN_SIZE];
		let worker = thread::Builder::new()
			.stack_size(STACK_SIZE)
			.spawn(move || {
				let state = ConcreteRatchetKernel::new(
					RatchetChain::from_bytes(initial_chain),
					RatchetChain::from_bytes(initial_chain),
				);

				fn reject_open(
					_material: &RatchetMaterial,
					sequence: u64,
					context: &(Cell<u64>, Cell<Option<u64>>),
				) -> Option<()> {
					context.0.set(context.0.get() + 1);
					context.1.set(Some(sequence));
					None
				}

				let context = (Cell::new(0), Cell::new(None));
				let mut effect = begin_receive(state, RATCHET_MAX_GAP + 1, &context);
				let state = loop {
					effect = match effect {
						ReceiveEffect::ReceiveRejected { kernel, .. } => break kernel,
						ReceiveEffect::ReceiveKdfRequested(kdf) => {
							let response =
								RatchetKdfResponse::from_bytes(test_ratchet_kdf(kdf.request()));
							kdf.resume(response)
						}
						ReceiveEffect::ReceiveOpenRequested(open) => {
							let material = open.material().expect("prepared material");
							let opened = reject_open(material, open.sequence(), open.context());
							let (kernel, result) = open.finish(opened);
							assert!(result.is_none());
							break kernel;
						}
					};
				};
				assert_eq!(context.0.get(), 1);
				assert_eq!(context.1.get(), Some(RATCHET_MAX_GAP + 1));
				assert_eq!(state.send_sequence(), 0);
				assert_eq!(state.receive_sequence(), 0);
				assert_eq!(state.receive_cache_len(), 0);
				assert_eq!(state.send_chain().as_bytes(), &initial_chain);
				assert_eq!(state.receive_chain().as_bytes(), &initial_chain);
			})
			.expect("constrained-stack worker should start");

		worker
			.join()
			.expect("max-gap receive should fit in the constrained stack");
	}

	#[test]
	fn send_advances_once_and_allocates_a_one_use_key() {
		let advanced = advance_send(RatchetState::new(7));

		assert_eq!(advanced.state.send_sequence(), 8);
		assert_eq!(advanced.sequence, Some(8));
		assert_eq!(advanced.key.sequence(), Some(8));
		assert!(advanced.key.is_available());
	}

	#[test]
	fn send_allocates_the_last_available_sequence() {
		let advanced = advance_send(RatchetState::new(u64::MAX - 1));

		assert_eq!(advanced.state.send_sequence(), u64::MAX);
		assert_eq!(advanced.sequence, Some(u64::MAX));
	}

	#[test]
	fn send_exhaustion_is_reported_without_changing_state() {
		let exhausted = RatchetState::new(u64::MAX);
		let result = advance_send(exhausted);

		assert_eq!(result.state, exhausted);
		assert_eq!(result.sequence, None);
		assert!(!result.key.is_available());
	}

	#[test]
	fn send_key_is_consumed_exactly_once() {
		let key = advance_send(RatchetState::default()).key;
		let first = finish_send(key);
		let second = finish_send(first.key);

		assert!(first.consumed);
		assert!(!first.key.is_available());
		assert!(!second.consumed);
		assert_eq!(second.key, first.key);
	}

	#[test]
	fn refined_send_pairs_one_step_with_the_allocated_sequence() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::from_counters(7, 0, 10, 20);
		let key = refined_advance_send(&mut state, test_step).unwrap();

		assert_eq!(key.sequence(), Some(8));
		assert_eq!(key.material().generation, 11);
		assert_eq!(*state.send_chain(), 11);
		assert_eq!(*state.receive_chain(), 20);
		assert_eq!(state.send_sequence(), 8);
		assert_eq!(state.receive_sequence(), 0);
		assert!(refined_finish_send(key));
	}

	#[test]
	fn refined_seal_next_keeps_sequence_and_material_inside_callback() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::from_counters(7, 0, 10, 20);
		let context = TestAeadContext::new(99, true);

		assert_eq!(
			refined_seal_next(&mut state, test_step, &context, test_aead),
			Some((8, 11, 99))
		);
		assert_eq!(context.seen_sequence.get(), Some(8));
		assert_eq!(context.seen_generation.get(), Some(11));
		assert_eq!(state.send_sequence(), 8);
		assert_eq!(*state.send_chain(), 11);
	}

	#[test]
	fn refined_seal_next_consumes_failed_attempt_material() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let context = TestAeadContext::new(99, false);

		assert_eq!(
			refined_seal_next(&mut state, test_step, &context, test_aead),
			None
		);
		assert_eq!(context.seen_sequence.get(), Some(1));
		assert_eq!(context.seen_generation.get(), Some(11));
		assert_eq!(state.send_sequence(), 1);
		assert_eq!(*state.send_chain(), 11);
	}

	#[test]
	fn refined_send_finish_rejects_an_unavailable_logical_key() {
		let key = RefinedSendKey {
			logical: SendKey::unavailable(),
			material: TestMaterial { generation: 0 },
		};

		assert!(!refined_finish_send(key));
	}

	#[test]
	fn refined_send_exhaustion_is_concretely_neutral() {
		let mut state =
			RefinedRatchet::<u64, u64, TestMaterial>::from_counters(u64::MAX, 4, 10, 20);

		assert!(refined_advance_send(&mut state, test_step).is_none());
		assert_eq!(state.send_sequence(), u64::MAX);
		assert_eq!(state.receive_sequence(), 4);
		assert_eq!(*state.send_chain(), 10);
		assert_eq!(*state.receive_chain(), 20);
		assert_eq!(state.receive_cache_len(), 0);
	}

	#[test]
	fn receive_plan_preserves_old_sequence_lookup_semantics() {
		let state = RatchetState::from_counters(0, 7);

		assert_eq!(plan_receive_until(state, 0).sequence, Some(0));
		assert_eq!(plan_receive_until(state, 3).sequence, Some(3));
		assert_eq!(plan_receive_until(state, 7).derivations, 0);
		assert_eq!(state.receive_sequence(), 7);
	}

	#[test]
	fn receive_plan_enforces_gap_and_capacity_without_mutation() {
		let state = RatchetState::default();
		let boundary = plan_receive_until(state, RATCHET_MAX_GAP + 1);
		let rejected = plan_receive_until(state, RATCHET_MAX_GAP + 2);

		assert_eq!(boundary.sequence, Some(RATCHET_MAX_GAP + 1));
		assert_eq!(boundary.derivations, RATCHET_MAX_GAP + 1);
		assert_eq!(rejected.sequence, None);
		assert_eq!(rejected.derivations, 0);
		assert_eq!(state, RatchetState::default());

		let full = execute_receive_plan(state, RATCHET_MAX_GAP);
		assert_eq!(
			plan_receive_until(full, RATCHET_MAX_GAP + 1).sequence,
			Some(RATCHET_MAX_GAP + 1)
		);
		assert_eq!(plan_receive_until(full, RATCHET_MAX_GAP + 2).sequence, None);
	}

	#[test]
	fn receive_target_advance_does_not_allocate_a_cache_slot() {
		let state = execute_receive_plan(RatchetState::default(), RATCHET_MAX_GAP);
		let advanced = advance_receive_target(state);

		assert_eq!(advanced.sequence, Some(RATCHET_MAX_GAP + 1));
		assert_eq!(advanced.state.receive_sequence(), RATCHET_MAX_GAP + 1);
		assert_eq!(advanced.state.receive_cache, state.receive_cache);
		assert_eq!(
			advanced.state.receive_cache_len() as usize,
			RECEIVE_CACHE_CAPACITY
		);

		let exhausted_state = RatchetState::from_counters(7, u64::MAX);
		let exhausted = advance_receive_target(exhausted_state);
		assert_eq!(exhausted.sequence, None);
		assert_eq!(exhausted.state, exhausted_state);
	}

	#[test]
	fn receive_advance_is_monotonic_and_stops_at_capacity() {
		let mut state = execute_receive_plan(RatchetState::default(), RATCHET_MAX_GAP);

		assert_eq!(state.receive_sequence(), RATCHET_MAX_GAP);
		assert_eq!(state.receive_cache_len() as usize, RECEIVE_CACHE_CAPACITY);
		let rejected = advance_receive(state);
		assert_eq!(rejected.state, state);
		assert_eq!(rejected.sequence, None);

		let slot = lookup_receive_key(state, RATCHET_MAX_GAP).unwrap();
		state = finish_receive(state, RATCHET_MAX_GAP, slot, true).state;
		assert_eq!(state.receive_cache_len(), RATCHET_MAX_GAP as u8 - 1);
		assert_eq!(
			plan_receive_until(state, RATCHET_MAX_GAP * 2).sequence,
			None
		);
	}

	#[test]
	fn receive_key_at_rejects_logical_boundary() {
		let state = execute_receive_plan(RatchetState::default(), 3);
		assert_eq!(state.receive_key_at(0), Some(1));
		assert_eq!(state.receive_key_at(2), Some(3));
		assert_eq!(state.receive_key_at(3), None);
	}

	#[test]
	fn verified_receive_lookup_is_total_when_logical_length_exceeds_capacity() {
		let entries = core::array::from_fn(|slot| slot as u64 + 1);
		let invalid = RatchetState {
			send_sequence: 0,
			receive_sequence: RECEIVE_CACHE_CAPACITY as u64 + 1,
			receive_cache: SequenceCache {
				entries,
				len: RECEIVE_CACHE_CAPACITY as u8 + 1,
			},
		};

		assert_eq!(
			lookup_receive_key(invalid, RECEIVE_CACHE_CAPACITY as u64),
			Some(RECEIVE_CACHE_CAPACITY as u8 - 1)
		);
		assert_eq!(
			lookup_receive_key(invalid, RECEIVE_CACHE_CAPACITY as u64 + 1),
			None
		);
		assert_eq!(invalid.receive_key_at(RECEIVE_CACHE_CAPACITY as u8), None);
	}

	#[test]
	fn verified_receive_lookup_finds_only_active_sequences() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		for sequence in 1..=4 {
			assert_eq!(
				lookup_receive_key(state, sequence),
				Some(sequence as u8 - 1)
			);
		}
		assert_eq!(lookup_receive_key(state, 0), None);
		assert_eq!(lookup_receive_key(state, 5), None);
	}

	#[test]
	fn verified_receive_lookup_tracks_swap_removal_and_consumption() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let consumed = finish_receive_with_removal(state, 2, 1, true);

		assert_eq!(lookup_receive_key(consumed.state, 2), None);
		assert_eq!(lookup_receive_key(consumed.state, 4), Some(1));
		assert_eq!(lookup_receive_key(consumed.state, 1), Some(0));
		assert_eq!(lookup_receive_key(consumed.state, 3), Some(2));
	}

	#[test]
	fn receive_allocates_max_then_exhausts_without_mutation() {
		let state = RatchetState::from_counters(0, u64::MAX - 1);
		let last = advance_receive(state);

		assert_eq!(last.sequence, Some(u64::MAX));
		assert_eq!(last.state.receive_sequence(), u64::MAX);
		let exhausted = advance_receive(last.state);
		assert_eq!(exhausted.sequence, None);
		assert_eq!(exhausted.state, last.state);
	}

	#[test]
	fn authentication_failure_retains_the_exact_key_for_retry() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let slot = lookup_receive_key(state, 4).unwrap();
		let failed = finish_receive(state, 4, slot, false);

		assert_eq!(failed.disposition, ReceiveDisposition::Retained);
		assert_eq!(failed.state, state);
		assert_eq!(failed.state.receive_key_at(slot), Some(4));
	}

	#[test]
	fn receive_completion_rejects_a_slot_at_the_logical_boundary() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let result = finish_receive(state, 0, state.receive_cache_len(), true);

		assert_eq!(result.disposition, ReceiveDisposition::Missing);
		assert_eq!(result.state, state);
	}

	#[test]
	fn successful_receive_consumes_only_target_and_replay_is_rejected() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let target_slot = lookup_receive_key(state, 3).unwrap();
		let consumed = finish_receive(state, 3, target_slot, true);

		assert_eq!(consumed.disposition, ReceiveDisposition::Consumed);
		assert_eq!(consumed.state.receive_cache_len(), 3);
		assert_eq!(lookup_receive_key(consumed.state, 3), None);
		assert!(lookup_receive_key(consumed.state, 1).is_some());
		assert!(lookup_receive_key(consumed.state, 2).is_some());
		assert!(lookup_receive_key(consumed.state, 4).is_some());

		let replay = finish_receive(consumed.state, 3, target_slot, true);
		assert_eq!(replay.disposition, ReceiveDisposition::Missing);
		assert_eq!(replay.state, consumed.state);
	}

	#[test]
	fn refined_receive_until_owns_derivation_and_material_association() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);

		assert_eq!(
			refined_advance_receive_until(&mut state, 4, test_step),
			Some(4)
		);
		assert_eq!(state.send_sequence(), 0);
		assert_eq!(state.receive_sequence(), 4);
		assert_eq!(state.receive_cache_len(), 4);
		assert_eq!(*state.send_chain(), 10);
		assert_eq!(*state.receive_chain(), 24);
		for slot in 0..4 {
			let (sequence, material) = state.receive_entry_at(slot).unwrap();
			assert_eq!(sequence, slot as u64 + 1);
			assert_eq!(material.generation, 21 + slot as u64);
			assert_eq!(refined_receive_key(&state, sequence), Some(material));
		}
		assert!(state.receive_entry_at(4).is_none());
		assert!(refined_receive_key(&state, 5).is_none());
	}

	#[test]
	fn refined_receive_transaction_executes_every_admitted_distance_exactly() {
		for distance in 0..=RATCHET_MAX_GAP {
			let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);

			assert_eq!(
				refined_advance_receive_until(&mut state, distance, test_step,),
				Some(distance)
			);
			assert_eq!(state.receive_sequence(), distance);
			assert_eq!(state.receive_cache_len(), distance as u8);
			assert_eq!(*state.receive_chain(), 20 + distance);
			for slot in 0..distance as u8 {
				let (sequence, material) = state.receive_entry_at(slot).unwrap();
				assert_eq!(sequence, slot as u64 + 1);
				assert_eq!(material.generation, 21 + slot as u64);
			}
		}
	}

	#[test]
	fn refined_receive_rejection_does_not_step_or_populate_slots() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);

		assert_eq!(
			refined_advance_receive_until(&mut state, RATCHET_MAX_GAP + 1, rejected_test_step,),
			None
		);
		assert_eq!(state.receive_sequence(), 0);
		assert_eq!(state.receive_cache_len(), 0);
		assert_eq!(*state.receive_chain(), 20);
		assert!(state.receive_entry_at(0).is_none());

		assert_eq!(
			refined_advance_receive_until(&mut state, 3, test_step),
			Some(3)
		);
		assert_eq!(*state.receive_chain(), 23);
	}

	#[test]
	fn refined_receive_transaction_rejects_a_later_occupied_slot_before_stepping() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		state.receive_slots[1] = Some(CachedReceiveKey {
			sequence: 99,
			material: TestMaterial { generation: 99 },
		});

		assert_eq!(
			refined_advance_receive_until(&mut state, 2, rejected_test_step),
			None
		);
		assert_eq!(state.control, RatchetState::default());
		assert_eq!(*state.receive_chain(), 20);
		assert!(state.receive_slots[0].is_none());
		assert_eq!(
			state.receive_slots[1].as_ref().unwrap().material.generation,
			99
		);
	}

	#[test]
	fn refined_receive_rejects_an_occupied_append_slot() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		state.receive_slots[0] = Some(CachedReceiveKey {
			sequence: 99,
			material: TestMaterial { generation: 99 },
		});

		assert_eq!(
			refined_advance_receive(&mut state, rejected_test_step),
			None
		);
		assert_eq!(state.control, RatchetState::default());
		assert_eq!(*state.receive_chain(), 20);
		assert_eq!(
			state.receive_slots[0].as_ref().unwrap().material.generation,
			99
		);
	}

	#[test]
	fn refined_receive_completion_rejects_missing_material() {
		let control = execute_receive_plan(RatchetState::default(), 2);
		let mut missing_target = RefinedRatchet::<u64, u64, TestMaterial> {
			control,
			send_chain: 10,
			receive_chain: 20,
			receive_slots: empty_material_slots(),
		};
		assert_eq!(
			refined_finish_receive(&mut missing_target, 1, false),
			ReceiveDisposition::Missing
		);
		assert_eq!(missing_target.control, control);

		let mut missing_last = RefinedRatchet::<u64, u64, TestMaterial> {
			control,
			send_chain: 10,
			receive_chain: 20,
			receive_slots: empty_material_slots(),
		};
		missing_last.receive_slots[0] = Some(CachedReceiveKey {
			sequence: 1,
			material: TestMaterial { generation: 21 },
		});
		assert_eq!(
			refined_finish_receive(&mut missing_last, 1, true),
			ReceiveDisposition::Missing
		);
		assert_eq!(missing_last.control, control);
		assert_eq!(
			missing_last.receive_slots[0]
				.as_ref()
				.unwrap()
				.material
				.generation,
			21
		);
	}

	#[test]
	fn refined_receive_rejects_a_mismatched_target_tag_without_mutation() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		assert_eq!(
			refined_advance_receive_until(&mut state, 2, test_step),
			Some(2)
		);
		state.receive_slots[0].as_mut().unwrap().sequence = 2;
		let control = state.control;
		let receive_chain = state.receive_chain;
		let generation = state.receive_slots[0].as_ref().unwrap().material.generation;

		assert!(state.receive_entry_at(0).is_none());
		assert!(refined_receive_key(&state, 1).is_none());
		assert_eq!(
			refined_finish_receive(&mut state, 1, false),
			ReceiveDisposition::Missing
		);
		assert_eq!(
			refined_finish_receive(&mut state, 1, true),
			ReceiveDisposition::Missing
		);
		assert_eq!(state.control, control);
		assert_eq!(state.receive_chain, receive_chain);
		assert_eq!(state.receive_slots[0].as_ref().unwrap().sequence, 2);
		assert_eq!(
			state.receive_slots[0].as_ref().unwrap().material.generation,
			generation
		);
	}

	#[test]
	fn refined_receive_rejects_a_mismatched_last_tag_before_swap() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		assert_eq!(
			refined_advance_receive_until(&mut state, 3, test_step),
			Some(3)
		);
		state.receive_slots[2].as_mut().unwrap().sequence = 99;
		let control = state.control;
		let target_generation = state.receive_slots[0].as_ref().unwrap().material.generation;
		let last_generation = state.receive_slots[2].as_ref().unwrap().material.generation;

		assert_eq!(refined_receive_key(&state, 1).unwrap().generation, 21);
		assert_eq!(
			refined_finish_receive(&mut state, 1, true),
			ReceiveDisposition::Missing
		);
		assert_eq!(state.control, control);
		assert_eq!(
			state.receive_slots[0].as_ref().unwrap().material.generation,
			target_generation
		);
		assert_eq!(state.receive_slots[2].as_ref().unwrap().sequence, 99);
		assert_eq!(
			state.receive_slots[2].as_ref().unwrap().material.generation,
			last_generation
		);
	}

	#[test]
	fn refined_receive_failure_retains_and_success_swaps_material() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		assert_eq!(
			refined_advance_receive_until(&mut state, 4, test_step),
			Some(4)
		);

		assert_eq!(
			refined_finish_receive(&mut state, 2, false),
			ReceiveDisposition::Retained
		);
		assert_eq!(state.receive_cache_len(), 4);
		assert_eq!(refined_receive_key(&state, 2).unwrap().generation, 22);
		assert_eq!(*state.receive_chain(), 24);

		assert_eq!(
			refined_finish_receive(&mut state, 2, true),
			ReceiveDisposition::Consumed
		);
		assert_eq!(state.receive_cache_len(), 3);
		assert!(refined_receive_key(&state, 2).is_none());
		assert_eq!(refined_receive_key(&state, 4).unwrap().generation, 24);
		let (moved_sequence, moved_material) = state.receive_entry_at(1).unwrap();
		assert_eq!(moved_sequence, 4);
		assert_eq!(moved_material.generation, 24);
		assert_eq!(
			refined_finish_receive(&mut state, 2, true),
			ReceiveDisposition::Missing
		);
		assert_eq!(*state.receive_chain(), 24);
	}

	#[test]
	fn refined_open_success_consumes_the_callback_material() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let context = TestAeadContext::new(77, true);

		assert_eq!(
			refined_open_and_finish(&mut state, 3, test_step, &context, test_aead),
			Some((3, 23, 77))
		);
		assert_eq!(context.seen_sequence.get(), Some(3));
		assert_eq!(context.seen_generation.get(), Some(23));
		assert!(refined_receive_key(&state, 3).is_none());
		assert_eq!(refined_receive_key(&state, 1).unwrap().generation, 21);
		assert_eq!(refined_receive_key(&state, 2).unwrap().generation, 22);
		assert_eq!(state.receive_cache_len(), 2);
	}

	#[test]
	fn receive_control_prefix_validation_checks_every_requested_slot() {
		let first = advance_receive(RatchetState::default()).state;
		let entry = advance_receive(first).state;
		let mut mismatched = entry;
		mismatched.receive_cache.entries[1] = 99;

		assert!(receive_control_prefix_matches(entry, entry, 0, 2));
		assert!(!receive_control_prefix_matches(entry, mismatched, 0, 2));
	}

	#[test]
	fn pending_receive_validation_rejects_corrupted_private_delta_fields() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let PreparedReceive::PreparedReceiveFutureCase(mut pending) =
			prepare_receive(&state, 3, test_step).expect("future receive should prepare")
		else {
			panic!("future target unexpectedly prepared as cached");
		};
		assert_eq!(pending.first_slot, 0);
		assert_eq!(pending.skipped, 2);
		assert!(pending_receive_slots_are_valid(
			&state,
			&pending,
			pending.first_slot,
			1,
			pending.skipped,
		));
		assert!(pending_receive_is_valid(&state, &pending, 3));

		let second_slot = 1;
		let second_sequence = pending.staged_slots[second_slot]
			.as_ref()
			.expect("second skipped slot should be staged")
			.sequence;
		pending.staged_slots[second_slot]
			.as_mut()
			.expect("second skipped slot should be staged")
			.sequence = 99;
		assert!(!pending_receive_slots_are_valid(
			&state,
			&pending,
			pending.first_slot,
			1,
			pending.skipped,
		));
		assert!(!pending_receive_is_valid(&state, &pending, 3));
		pending.staged_slots[second_slot]
			.as_mut()
			.expect("second skipped slot should be staged")
			.sequence = second_sequence;

		let target_slot = pending.first_slot as usize + pending.skipped as usize;
		state.receive_slots[target_slot] = Some(CachedReceiveKey {
			sequence: 77,
			material: TestMaterial { generation: 77 },
		});
		assert!(!pending_receive_is_valid(&state, &pending, 3));
		state.receive_slots[target_slot] = None;
		pending.staged_slots[target_slot] = Some(CachedReceiveKey {
			sequence: 88,
			material: TestMaterial { generation: 88 },
		});
		assert!(!pending_receive_is_valid(&state, &pending, 3));
	}

	#[test]
	fn future_slot_publication_moves_only_the_validated_range() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let mut staged_slots = empty_material_slots();
		staged_slots[0] = Some(CachedReceiveKey {
			sequence: 1,
			material: TestMaterial { generation: 21 },
		});
		state.receive_slots[1] = Some(CachedReceiveKey {
			sequence: 99,
			material: TestMaterial { generation: 99 },
		});

		publish_future_receive_slots(&mut state, &mut staged_slots, 0, 1);

		assert!(staged_slots[0].is_none());
		assert_eq!(state.receive_slots[0].as_ref().unwrap().sequence, 1);
		assert_eq!(
			state.receive_slots[0].as_ref().unwrap().material.generation,
			21
		);
		assert_eq!(state.receive_slots[1].as_ref().unwrap().sequence, 99);
		assert_eq!(
			state.receive_slots[1].as_ref().unwrap().material.generation,
			99
		);
	}

	fn malformed_range_pending(skipped: u8) -> PendingReceive<u64, TestMaterial> {
		let mut staged_slots = empty_material_slots();
		staged_slots[RECEIVE_CACHE_CAPACITY - 1] = Some(CachedReceiveKey {
			sequence: 77,
			material: TestMaterial { generation: 77 },
		});
		PendingReceive {
			committed_control: RatchetState::from_counters(88, 89),
			final_receive_chain: 90,
			staged_slots,
			target_sequence: 91,
			target_material: TestMaterial { generation: 91 },
			first_slot: (RECEIVE_CACHE_CAPACITY - 1) as u8,
			skipped,
		}
	}

	#[test]
	fn future_publication_rejects_ranges_beyond_the_cache() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let entry = test_snapshot(&state);
		publish_future_receive(&mut state, malformed_range_pending(2));
		assert_eq!(test_snapshot(&state), entry);
	}

	#[test]
	fn rejected_future_opens_preserve_every_observable_field() {
		for target in [1, 7, RATCHET_MAX_GAP + 1] {
			let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
			let entry = test_snapshot(&state);
			let failed = TestAeadContext::new(target + 100, false);

			assert_eq!(
				refined_open_and_finish(&mut state, target, test_step, &failed, test_aead),
				None
			);
			assert_eq!(failed.calls.get(), 1);
			assert_eq!(failed.seen_sequence.get(), Some(target));
			assert_eq!(failed.seen_generation.get(), Some(20 + target));
			assert_eq!(test_snapshot(&state), entry);
		}
	}

	#[test]
	fn successful_future_opens_publish_only_skipped_material_and_replay_is_neutral() {
		for target in [1, RATCHET_MAX_GAP + 1] {
			let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
			let accepted = TestAeadContext::new(target + 200, true);

			assert_eq!(
				refined_open_and_finish(&mut state, target, test_step, &accepted, test_aead),
				Some((target, 20 + target, target + 200))
			);
			assert_eq!(accepted.calls.get(), 1);
			assert_eq!(state.receive_sequence(), target);
			assert_eq!(*state.receive_chain(), 20 + target);
			assert_eq!(state.receive_cache_len(), target as u8 - 1);
			for sequence in 1..target {
				assert_eq!(
					refined_receive_key(&state, sequence).unwrap().generation,
					20 + sequence
				);
			}
			assert!(refined_receive_key(&state, target).is_none());

			let entry = test_snapshot(&state);
			let replay = TestAeadContext::new(target + 300, true);
			assert_eq!(
				refined_open_and_finish(&mut state, target, rejected_test_step, &replay, test_aead,),
				None
			);
			assert_eq!(replay.calls.get(), 0);
			assert_eq!(replay.seen_sequence.get(), None);
			assert_eq!(replay.seen_generation.get(), None);
			assert_eq!(test_snapshot(&state), entry);
		}
	}

	#[test]
	fn cached_open_rejection_does_not_swap_and_success_removes_the_whole_entry() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let future = TestAeadContext::new(40, true);
		assert!(refined_open_and_finish(&mut state, 4, test_step, &future, test_aead).is_some());
		let entry = test_snapshot(&state);

		let failed = TestAeadContext::new(41, false);
		assert_eq!(
			refined_open_and_finish(&mut state, 2, rejected_test_step, &failed, test_aead),
			None
		);
		assert_eq!(failed.calls.get(), 1);
		assert_eq!(failed.seen_sequence.get(), Some(2));
		assert_eq!(failed.seen_generation.get(), Some(22));
		assert_eq!(test_snapshot(&state), entry);

		let accepted = TestAeadContext::new(42, true);
		assert_eq!(
			refined_open_and_finish(&mut state, 2, rejected_test_step, &accepted, test_aead,),
			Some((2, 22, 42))
		);
		assert_eq!(accepted.calls.get(), 1);
		assert_eq!(state.receive_cache_len(), 2);
		assert_eq!(state.receive_entry_at(0).unwrap().0, 1);
		assert_eq!(state.receive_entry_at(1).unwrap().0, 3);
		assert_eq!(state.receive_entry_at(1).unwrap().1.generation, 23);
		assert!(refined_receive_key(&state, 2).is_none());
		assert_eq!(*state.receive_chain(), 24);
	}

	#[test]
	fn rejected_receive_plans_do_not_invoke_kdf_or_open() {
		for target in [0, RATCHET_MAX_GAP + 2, u64::MAX] {
			let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
			let entry = test_snapshot(&state);
			let context = TestAeadContext::new(target, true);
			assert_eq!(
				refined_open_and_finish(
					&mut state,
					target,
					rejected_test_step,
					&context,
					test_aead,
				),
				None
			);
			assert_eq!(context.calls.get(), 0);
			assert_eq!(context.seen_sequence.get(), None);
			assert_eq!(context.seen_generation.get(), None);
			assert_eq!(test_snapshot(&state), entry);
		}

		let mut missing = RefinedRatchet::<u64, u64, TestMaterial>::from_counters(0, 9, 10, 29);
		let missing_entry = test_snapshot(&missing);
		let context = TestAeadContext::new(3, true);
		assert_eq!(
			refined_open_and_finish(&mut missing, 3, rejected_test_step, &context, test_aead,),
			None
		);
		assert_eq!(context.calls.get(), 0);
		assert_eq!(context.seen_sequence.get(), None);
		assert_eq!(test_snapshot(&missing), missing_entry);

		let mut full = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		assert_eq!(
			refined_advance_receive_until(&mut full, RATCHET_MAX_GAP, test_step),
			Some(RATCHET_MAX_GAP)
		);
		let full_entry = test_snapshot(&full);
		let context = TestAeadContext::new(RATCHET_MAX_GAP + 2, true);
		assert_eq!(
			refined_open_and_finish(
				&mut full,
				RATCHET_MAX_GAP + 2,
				rejected_test_step,
				&context,
				test_aead,
			),
			None
		);
		assert_eq!(context.calls.get(), 0);
		assert_eq!(context.seen_sequence.get(), None);
		assert_eq!(test_snapshot(&full), full_entry);
	}

	#[test]
	fn refined_open_failure_preserves_entry_and_retry_rederives() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		let entry = test_snapshot(&state);
		let failed = TestAeadContext::new(77, false);
		TEST_STEP_CALLS.store(0, Ordering::Relaxed);

		assert_eq!(
			refined_open_and_finish(&mut state, 3, counting_test_step, &failed, test_aead),
			None
		);
		assert_eq!(failed.seen_sequence.get(), Some(3));
		assert_eq!(failed.seen_generation.get(), Some(23));
		assert_eq!(TEST_STEP_CALLS.load(Ordering::Relaxed), 3);
		assert_eq!(test_snapshot(&state), entry);

		let retry = TestAeadContext::new(88, true);
		assert_eq!(
			refined_open_and_finish(&mut state, 3, counting_test_step, &retry, test_aead),
			Some((3, 23, 88))
		);
		assert_eq!(TEST_STEP_CALLS.load(Ordering::Relaxed), 6);
		assert_eq!(*state.receive_chain(), 23);
		assert!(refined_receive_key(&state, 3).is_none());
		assert_eq!(refined_receive_key(&state, 1).unwrap().generation, 21);
		assert_eq!(refined_receive_key(&state, 2).unwrap().generation, 22);
	}

	#[test]
	fn refined_transitions_preserve_derivational_reachability() {
		let initial_send_chain = 10;
		let initial_receive_chain = 20;
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(
			initial_send_chain,
			initial_receive_chain,
		);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&state
		));

		let send = TestAeadContext::new(70, true);
		assert_eq!(
			refined_seal_next(&mut state, test_step, &send, test_aead),
			Some((1, 11, 70))
		);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&state
		));

		let failed_open = TestAeadContext::new(71, false);
		assert_eq!(
			refined_open_and_finish(&mut state, 4, test_step, &failed_open, test_aead),
			None
		);
		assert_eq!(failed_open.seen_sequence.get(), Some(4));
		assert_eq!(failed_open.seen_generation.get(), Some(24));
		assert_eq!(state.receive_sequence(), 0);
		assert_eq!(state.receive_cache_len(), 0);
		assert_eq!(*state.receive_chain(), initial_receive_chain);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&state
		));

		let consume = TestAeadContext::new(72, true);
		assert_eq!(
			refined_open_and_finish(&mut state, 2, test_step, &consume, test_aead),
			Some((2, 22, 72))
		);
		assert!(refined_receive_key(&state, 2).is_none());
		let (skipped_sequence, skipped_material) = state.receive_entry_at(0).unwrap();
		assert_eq!(skipped_sequence, 1);
		assert_eq!(skipped_material.generation, 21);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&state
		));

		assert_eq!(
			refined_advance_receive_until(&mut state, 6, test_step),
			Some(6)
		);
		assert_eq!(state.receive_sequence(), 6);
		assert_eq!(refined_receive_key(&state, 5).unwrap().generation, 25);
		assert_eq!(refined_receive_key(&state, 6).unwrap().generation, 26);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&state
		));
	}

	#[test]
	fn refined_receive_one_step_uses_the_next_empty_slot() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);

		assert_eq!(refined_advance_receive(&mut state, test_step), Some(1));
		assert_eq!(state.receive_entry_at(0).unwrap().0, 1);
		assert_eq!(state.receive_entry_at(0).unwrap().1.generation, 21);
		assert!(state.receive_entry_at(1).is_none());
	}

	#[test]
	fn detailed_receive_completion_reports_exact_swap_removal() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let missing = finish_receive_with_removal(state, 9, 1, true);
		assert_eq!(missing.disposition, ReceiveDisposition::Missing);
		assert_eq!(missing.removal, None);
		assert_eq!(missing.state, state);
		assert_eq!(
			finish_receive(state, 9, 1, true),
			super::ReceiveFinish {
				state: missing.state,
				disposition: missing.disposition,
			}
		);

		let retained = finish_receive_with_removal(state, 2, 1, false);
		assert_eq!(retained.disposition, ReceiveDisposition::Retained);
		assert_eq!(retained.removal, None);
		assert_eq!(retained.state, state);
		assert_eq!(finish_receive(state, 2, 1, false).state, retained.state);
		assert_eq!(
			finish_receive(state, 2, 1, false).disposition,
			retained.disposition
		);

		let consumed = finish_receive_with_removal(state, 2, 1, true);
		assert_eq!(consumed.disposition, ReceiveDisposition::Consumed);
		let removal = consumed.removal.unwrap();
		assert_eq!(removal.target_slot, 1);
		assert_eq!(removal.last_slot, 3);
		assert_eq!(consumed.state.receive_key_at(1), Some(4));
		assert_eq!(finish_receive(state, 2, 1, true).state, consumed.state);
		assert_eq!(
			finish_receive(state, 2, 1, true).disposition,
			consumed.disposition
		);
	}

	#[test]
	fn detailed_receive_completion_reports_last_slot_removal() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let consumed = finish_receive_with_removal(state, 4, 3, true);
		let removal = consumed.removal.unwrap();

		assert_eq!(removal.target_slot, 3);
		assert_eq!(removal.last_slot, 3);
		assert_eq!(consumed.state.receive_cache_len(), 3);
		assert_eq!(lookup_receive_key(consumed.state, 4), None);
		for sequence in 1..=3 {
			assert_eq!(
				lookup_receive_key(consumed.state, sequence),
				Some(sequence as u8 - 1)
			);
		}
	}

	#[test]
	fn old_skipped_key_does_not_turn_capacity_into_a_sliding_window() {
		let mut state = execute_receive_plan(RatchetState::default(), RATCHET_MAX_GAP);
		for sequence in 2..=RATCHET_MAX_GAP {
			let slot = lookup_receive_key(state, sequence).unwrap();
			state = finish_receive(state, sequence, slot, true).state;
		}

		for target in RATCHET_MAX_GAP + 1..=200 {
			state = execute_receive_plan(state, target);
			let slot = lookup_receive_key(state, target).unwrap();
			state = finish_receive(state, target, slot, true).state;
		}

		assert_eq!(state.receive_sequence(), 200);
		assert_eq!(state.receive_cache_len(), 1);
		assert!(lookup_receive_key(state, 1).is_some());
	}

	#[test]
	fn restore_accepts_only_sorted_unique_bounded_sequences() {
		let restore = start_restore(9, 12);
		let restore = restore_receive_key(restore, 1).unwrap();
		assert!(restore_receive_key(restore, 1).is_none());
		let restore = restore_receive_key(restore, 4).unwrap();
		assert!(restore_receive_key(restore, 3).is_none());
		let restore = restore_receive_key(restore, 12).unwrap();
		assert!(restore_receive_key(restore, 13).is_none());

		let state = finish_restore(restore);
		assert_eq!(state.send_sequence(), 9);
		assert_eq!(state.receive_sequence(), 12);
		assert_eq!(state.receive_cache_len(), 3);
		assert_eq!(state.receive_key_at(0), Some(1));
		assert_eq!(state.receive_key_at(1), Some(4));
		assert_eq!(state.receive_key_at(2), Some(12));
	}

	#[test]
	fn restore_reports_the_slot_used_by_the_logical_append() {
		let initial = start_restore(0, 9);
		let first = restore_receive_key_with_slot(initial, 2).unwrap();
		assert_eq!(first.slot, 0);
		let second = restore_receive_key_with_slot(first.restore, 7).unwrap();
		assert_eq!(second.slot, 1);
		let third = restore_receive_key_with_slot(second.restore, 9).unwrap();
		assert_eq!(third.slot, 2);
		assert_eq!(finish_restore(third.restore).receive_key_at(2), Some(9));
		assert_eq!(restore_receive_key(initial, 2), Some(first.restore));
		assert_eq!(restore_receive_key(first.restore, 7), Some(second.restore));
		assert_eq!(restore_receive_key(second.restore, 9), Some(third.restore));

		for (restore, sequence) in [
			(initial, 0),
			(initial, 10),
			(first.restore, 2),
			(first.restore, 1),
		] {
			assert_eq!(restore_receive_key_with_slot(restore, sequence), None);
			assert_eq!(restore_receive_key(restore, sequence), None);
		}
	}

	#[test]
	fn restore_rejects_more_than_the_cache_capacity() {
		let mut restore = start_restore(0, RECEIVE_CACHE_CAPACITY as u64 + 1);
		for sequence in 1..=RECEIVE_CACHE_CAPACITY as u64 {
			restore = restore_receive_key(restore, sequence).unwrap();
		}
		assert!(restore_receive_key(restore, RECEIVE_CACHE_CAPACITY as u64 + 1).is_none());
	}

	#[test]
	fn refined_restore_binds_each_sequence_and_material_atomically() {
		let mut restore = start_refined_restore::<u64, u64, TestMaterial>(9, 12, 100, 200);
		assert!(refined_restore_receive_key(
			&mut restore,
			2,
			TestMaterial { generation: 22 }
		));
		assert!(!refined_restore_receive_key(
			&mut restore,
			2,
			TestMaterial { generation: 999 }
		));
		assert!(refined_restore_receive_key(
			&mut restore,
			7,
			TestMaterial { generation: 27 }
		));

		let state = finish_refined_restore(restore);
		assert_eq!(state.send_sequence(), 9);
		assert_eq!(state.receive_sequence(), 12);
		assert_eq!(state.receive_cache_len(), 2);
		assert_eq!(*state.send_chain(), 100);
		assert_eq!(*state.receive_chain(), 200);
		assert_eq!(state.receive_entry_at(0).unwrap().0, 2);
		assert_eq!(state.receive_entry_at(0).unwrap().1.generation, 22);
		assert_eq!(state.receive_entry_at(1).unwrap().0, 7);
		assert_eq!(state.receive_entry_at(1).unwrap().1.generation, 27);
	}

	#[test]
	fn refined_restore_preserves_reachability_only_for_authenticated_snapshot_material() {
		let initial_send_chain = 10;
		let initial_receive_chain = 20;
		let mut source = RefinedRatchet::<u64, u64, TestMaterial>::new(
			initial_send_chain,
			initial_receive_chain,
		);
		let send = TestAeadContext::new(80, true);
		assert!(refined_seal_next(&mut source, test_step, &send, test_aead).is_some());
		assert!(refined_seal_next(&mut source, test_step, &send, test_aead).is_some());
		assert_eq!(
			refined_advance_receive_until(&mut source, 5, test_step),
			Some(5)
		);
		assert_eq!(
			refined_finish_receive(&mut source, 2, true),
			ReceiveDisposition::Consumed
		);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&source
		));

		let mut correct = start_refined_restore(
			source.send_sequence(),
			source.receive_sequence(),
			*source.send_chain(),
			*source.receive_chain(),
		);
		for sequence in 1..=source.receive_sequence() {
			if let Some(material) = refined_receive_key(&source, sequence) {
				assert!(refined_restore_receive_key(
					&mut correct,
					sequence,
					TestMaterial {
						generation: material.generation,
					}
				));
			}
		}
		let correct = finish_refined_restore(correct);
		assert!(test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&correct
		));

		let mut arbitrary = start_refined_restore(
			source.send_sequence(),
			source.receive_sequence(),
			*source.send_chain(),
			*source.receive_chain(),
		);
		for sequence in 1..=source.receive_sequence() {
			if let Some(material) = refined_receive_key(&source, sequence) {
				let generation = if sequence == 3 {
					material.generation + 1_000
				} else {
					material.generation
				};
				assert!(refined_restore_receive_key(
					&mut arbitrary,
					sequence,
					TestMaterial { generation }
				));
			}
		}
		let arbitrary = finish_refined_restore(arbitrary);

		// Restoration is the explicit trust-boundary exception.
		// The builder validates structure and tags. Authenticated persistence must vouch for derivations.
		assert_eq!(
			refined_receive_key(&arbitrary, 3).unwrap().generation,
			1_023
		);
		assert!(!test_is_reachable(
			initial_send_chain,
			initial_receive_chain,
			&arbitrary
		));
	}

	#[test]
	fn refined_restore_rejects_an_occupied_append_slot() {
		let mut restore = start_refined_restore::<u64, u64, TestMaterial>(9, 12, 100, 200);
		restore.receive_slots[0] = Some(CachedReceiveKey {
			sequence: 99,
			material: TestMaterial { generation: 99 },
		});

		assert!(!refined_restore_receive_key(
			&mut restore,
			2,
			TestMaterial { generation: 22 }
		));
		assert_eq!(restore.logical, start_restore(9, 12));
		assert_eq!(
			restore.receive_slots[0]
				.as_ref()
				.unwrap()
				.material
				.generation,
			99
		);
	}

	#[test]
	fn peer_mismatch_is_state_neutral() {
		let peer = PeerRatchetState {
			peer_id: 7,
			ratchet: RatchetState::new(11),
		};
		let untouched = advance_send_for_peer(8, peer);
		let selected = advance_send_for_peer(7, peer);
		let replacement = RatchetState::new(99);
		let generic_untouched = replace_ratchet_for_peer(8, peer, replacement);
		let generic_selected = replace_ratchet_for_peer(7, peer, replacement);

		assert_eq!(untouched.peer, peer);
		assert_eq!(untouched.sequence, None);
		assert_eq!(generic_untouched, peer);
		assert_eq!(generic_selected.peer_id, peer.peer_id);
		assert_eq!(generic_selected.ratchet, replacement);
		assert_eq!(selected.peer.peer_id, peer.peer_id);
		assert_eq!(selected.peer.ratchet.send_sequence(), 12);
		assert_eq!(selected.sequence, Some(12));
	}
}
