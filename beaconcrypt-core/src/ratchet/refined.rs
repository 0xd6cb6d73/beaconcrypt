// SPDX-License-Identifier: 0BSD

// Pinned Aeneas does not translate the `Try::branch` emitted by `?` reliably.
#![allow(clippy::question_mark)]

use super::control::{
	RECEIVE_CACHE_CAPACITY, RatchetRestore, RatchetState, ReceiveDisposition,
	finish_receive_with_removal, finish_restore, lookup_receive_key, restore_receive_key_with_slot,
	start_restore,
};

#[cfg(test)]
use super::control::{
	RATCHET_MAX_GAP, SendKey, advance_receive, advance_receive_target, advance_send, finish_send,
	plan_receive_until,
};

/// One opaque ratchet-step result.
///
/// The shared kernel treats both fields parametrically.
/// The concrete effect continuations interpret fixed-output KDF replies into this partition.
/// Logical tests may construct arbitrary values through this type.
#[cfg_attr(
	feature = "proverif",
	hax_lib::fstar::before("friend Beaconcrypt_core.Ratchet.Control")
)]
pub struct RatchetStep<Chain, Material> {
	pub chain: Chain,
	pub material: Material,
}

/// Concrete receive material sealed together with the logical sequence that
/// caused the kernel to store it.
///
/// Private fields prevent adapters from manufacturing or retagging cached
/// material independently of the checked receive and restoration transitions.
pub struct CachedReceiveKey<Material> {
	pub(super) sequence: u64,
	pub(super) material: Material,
}

pub(super) fn empty_material_slots<Material>()
-> [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY] {
	// Pinned hax cannot extract `array::from_fn` or an inline-const repeat. This
	// literal keeps `Material` non-`Copy` and extracts as transparent `None`s.
	[
		None, None, None, None, None, None, None, None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None, None, None, None, None, None, None, None,
		None, None, None, None, None, None, None, None, None, None, None, None, None, None, None,
		None, None, None, None, None,
	]
}

/// Ratchet control state refined by the concrete chain states and receive-key
/// material governed by that control state.
///
/// The concrete types remain generic so hax/F* can prove the bookkeeping for
/// arbitrary opaque HKDF inputs and outputs. Each concrete receive value is
/// sealed with its sequence, and private fields ensure Rust callers can only
/// construct and mutate that correspondence through this kernel.
pub struct RefinedRatchet<SendChain, ReceiveChain, Material> {
	pub(super) control: RatchetState,
	pub(super) send_chain: SendChain,
	pub(super) receive_chain: ReceiveChain,
	pub(super) receive_slots: [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
}

/// Kernel-private receive preparation that owns only the delta needed for a
/// successful publication. Neither variant is a live or serializable ratchet.
pub(super) enum PreparedReceive<ReceiveChain, Material> {
	PreparedReceiveCachedCase(PreparedCachedReceive),
	PreparedReceiveFutureCase(PendingReceive<ReceiveChain, Material>),
}

/// Prevalidated metadata for consuming an already cached receive key.
pub(super) struct PreparedCachedReceive {
	pub(super) sequence: u64,
	pub(super) target_slot: u8,
	pub(super) last_slot: u8,
	pub(super) committed_control: RatchetState,
}

/// Final metadata produced while deriving a future receive into a caller-owned
/// staging buffer.
///
/// Keeping the fixed-capacity buffer out of this recursive result ensures the
/// Rust implementation has exactly one live staging array regardless of gap.
#[cfg(test)]
struct PreparedFutureTarget<ReceiveChain, Material> {
	committed_control: RatchetState,
	final_receive_chain: ReceiveChain,
	target_sequence: u64,
	target_material: Material,
	first_slot: u8,
	skipped: u8,
}

/// Privately derived future receive delta.
///
/// The target material is deliberately separate from `staged_slots`, so a
/// successful publication can retain only skipped material while dropping the
/// authenticated target.
pub(super) struct PendingReceive<ReceiveChain, Material> {
	pub(super) committed_control: RatchetState,
	pub(super) final_receive_chain: ReceiveChain,
	pub(super) staged_slots: [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
	pub(super) target_sequence: u64,
	pub(super) target_material: Material,
	pub(super) first_slot: u8,
	pub(super) skipped: u8,
}

impl<SendChain, ReceiveChain, Material> RefinedRatchet<SendChain, ReceiveChain, Material> {
	/// Construct a fresh refined ratchet with empty counters and receive slots.
	pub fn new(send_chain: SendChain, receive_chain: ReceiveChain) -> Self {
		Self::from_counters(0, 0, send_chain, receive_chain)
	}

	/// Construct a refined ratchet with arbitrary counters and no cached receive
	/// material. This is also useful for checked exhaustion fixtures.
	pub fn from_counters(
		send_sequence: u64,
		receive_sequence: u64,
		send_chain: SendChain,
		receive_chain: ReceiveChain,
	) -> Self {
		Self {
			control: RatchetState::from_counters(send_sequence, receive_sequence),
			send_chain,
			receive_chain,
			receive_slots: empty_material_slots(),
		}
	}

	pub const fn send_sequence(&self) -> u64 {
		self.control.send_sequence()
	}

	pub const fn receive_sequence(&self) -> u64 {
		self.control.receive_sequence()
	}

	pub const fn receive_cache_len(&self) -> u8 {
		self.control.receive_cache_len()
	}

	pub const fn send_chain(&self) -> &SendChain {
		&self.send_chain
	}

	pub const fn receive_chain(&self) -> &ReceiveChain {
		&self.receive_chain
	}

	/// Return the logical sequence and concrete material paired in one active
	/// physical slot.
	pub fn receive_entry_at(&self, slot: u8) -> Option<(u64, &Material)> {
		let sequence = match self.control.receive_key_at(slot) {
			Some(sequence) => sequence,
			None => return None,
		};
		let slot_index = slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return None;
		}
		let cached = match self.receive_slots[slot_index].as_ref() {
			Some(cached) => cached,
			None => return None,
		};
		if !(cached.sequence == sequence) {
			return None;
		}
		Some((cached.sequence, &cached.material))
	}
}

/// A kernel-private concrete send key paired with its logical one-use capability.
///
/// This token is deliberately neither `Copy` nor `Clone`, and it never crosses
/// the public kernel boundary. [`refined_seal_next`] lends its material to the
/// opaque sealing callback and consumes the complete token before returning.
#[cfg(test)]
pub(crate) struct RefinedSendKey<Material> {
	pub(super) logical: SendKey,
	pub(super) material: Material,
}

#[cfg(test)]
impl<Material> RefinedSendKey<Material> {
	pub const fn sequence(&self) -> Option<u64> {
		self.logical.sequence()
	}

	pub const fn material(&self) -> &Material {
		&self.material
	}
}

/// Advance the send control state and concrete chain with the same opaque step.
///
/// Exhaustion is neutral and does not invoke `step`. Success publishes the new
/// chain and counter together and returns the exact step material beside the
/// logical capability for the allocated sequence.
#[cfg(test)]
pub(crate) fn refined_advance_send<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	step: fn(&SendChain) -> RatchetStep<SendChain, Material>,
) -> Option<RefinedSendKey<Material>> {
	let advanced = advance_send(state.control);
	let sequence = advanced.sequence?;
	if advanced.key.sequence() != Some(sequence) || advanced.state.send_sequence() != sequence {
		return None;
	}

	let stepped = step(&state.send_chain);
	state.send_chain = stepped.chain;
	state.control = advanced.state;
	Some(RefinedSendKey {
		logical: advanced.key,
		material: stepped.material,
	})
}

/// Consume a concrete/logical send token after its single permitted use.
#[cfg(test)]
pub(crate) fn refined_finish_send<Material>(key: RefinedSendKey<Material>) -> bool {
	let finished = finish_send(key.logical);
	finished.consumed && !finished.key.is_available()
}

/// Advance the send ratchet and seal with the exact material allocated for the
/// resulting sequence.
///
/// The opaque callback is the only code outside the kernel that can observe
/// the sequence/material pair. The pair is borrowed only for that call and is
/// consumed before this operation returns, regardless of whether sealing
/// succeeds.
#[cfg(test)]
pub(crate) fn refined_seal_next<SendChain, ReceiveChain, Material, Context, Output>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	step: fn(&SendChain) -> RatchetStep<SendChain, Material>,
	context: &Context,
	seal: fn(&Material, u64, &Context) -> Option<Output>,
) -> Option<Output> {
	let key = refined_advance_send(state, step)?;
	let Some(sequence) = key.sequence() else {
		let _ = refined_finish_send(key);
		return None;
	};
	let output = seal(key.material(), sequence, context);
	if !refined_finish_send(key) {
		return None;
	}
	output
}

/// Derive and cache exactly one receive key through the shared refined kernel.
///
/// Logical admission and slot validation happen before the sole opaque step.
/// Rejection therefore leaves the concrete chain and slots untouched.
#[allow(dead_code)]
#[cfg(test)]
pub(crate) fn refined_advance_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
) -> Option<u64> {
	let advanced = advance_receive(state.control);
	let sequence = advanced.sequence?;
	let slot = advanced.slot?;
	let slot_index = slot as usize;
	if advanced.state.receive_key_at(slot) != Some(sequence)
		|| slot_index >= RECEIVE_CACHE_CAPACITY
		|| state.receive_slots[slot_index].is_some()
	{
		return None;
	}

	let stepped = step(&state.receive_chain);
	state.receive_chain = stepped.chain;
	state.receive_slots[slot_index] = Some(CachedReceiveKey {
		sequence,
		material: stepped.material,
	});
	state.control = advanced.state;
	Some(sequence)
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
pub(super) fn refined_receive_slots_are_empty<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	first_slot: u8,
	remaining: u8,
) -> bool {
	let mut slot = first_slot;
	let mut left = remaining;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		let slot_index = slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return false;
		}
		if state.receive_slots[slot_index].is_some() {
			return false;
		}

		slot += 1;
		left -= 1;
	}

	true
}

/// Preflight an existing cached target and compute its successful logical
/// removal without changing the live refined ratchet.
pub(super) fn prepare_cached_receive<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	sequence: u64,
) -> Option<PreparedCachedReceive> {
	let target_slot = match lookup_receive_key(state.control, sequence) {
		Some(target_slot) => target_slot,
		None => return None,
	};
	let target_index = target_slot as usize;
	if target_index >= RECEIVE_CACHE_CAPACITY {
		return None;
	}
	if !(state.control.receive_key_at(target_slot) == Some(sequence)) {
		return None;
	}
	let target = match state.receive_slots[target_index].as_ref() {
		Some(target) => target,
		None => return None,
	};
	if !(target.sequence == sequence) {
		return None;
	}

	let len = state.control.receive_cache_len();
	if len == 0 {
		return None;
	}
	let last_slot = len - 1;
	let last_index = last_slot as usize;
	if last_index >= RECEIVE_CACHE_CAPACITY {
		return None;
	}
	let last_sequence = match state.control.receive_key_at(last_slot) {
		Some(last_sequence) => last_sequence,
		None => return None,
	};
	let last = match state.receive_slots[last_index].as_ref() {
		Some(last) => last,
		None => return None,
	};
	if !(last.sequence == last_sequence) {
		return None;
	}

	let finished = finish_receive_with_removal(state.control, sequence, target_slot, true);
	let removal = match finished.removal {
		Some(removal) => removal,
		None => return None,
	};
	match finished.disposition {
		ReceiveDisposition::Consumed => {}
		ReceiveDisposition::Missing | ReceiveDisposition::Retained => return None,
	}
	if !(removal.target_slot == target_slot) {
		return None;
	}
	if !(removal.last_slot == last_slot) {
		return None;
	}
	Some(PreparedCachedReceive {
		sequence,
		target_slot,
		last_slot,
		committed_control: finished.state,
	})
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
#[cfg(test)]
/// Derive a future target into a private delta without assigning any live
/// chain, slot, or logical control field.
///
/// The traversal is iterative so its call-stack consumption is independent of
/// the admitted receive gap. Exactly one derived chain and one material value
/// are live for the current iteration, in addition to the caller-owned staging
/// array.
#[allow(clippy::too_many_arguments)]
fn prepare_future_receive_steps<ReceiveChain, Material>(
	entry_chain: &ReceiveChain,
	control: RatchetState,
	target: u64,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
	remaining: u8,
	first_slot: u8,
	skipped: u8,
	staged_slots: &mut [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
) -> Option<PreparedFutureTarget<ReceiveChain, Material>> {
	if remaining == 0 {
		return None;
	}

	let mut current_chain: Option<ReceiveChain> = None;
	let mut current_control = control;
	let mut left = remaining;
	let mut skipped_count = skipped;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		if left == 1 {
			let advanced = advance_receive_target(current_control);
			let sequence = match advanced.sequence {
				Some(sequence) => sequence,
				None => return None,
			};
			if sequence != target {
				return None;
			}

			let stepped = match current_chain.as_ref() {
				Some(chain) => step(chain),
				None => step(entry_chain),
			};

			return Some(PreparedFutureTarget {
				committed_control: advanced.state,
				final_receive_chain: stepped.chain,
				target_sequence: sequence,
				target_material: stepped.material,
				first_slot,
				skipped: skipped_count,
			});
		}

		let advanced = advance_receive(current_control);
		let sequence = match advanced.sequence {
			Some(sequence) => sequence,
			None => return None,
		};
		let slot = match advanced.slot {
			Some(slot) => slot,
			None => return None,
		};
		let slot_index = slot as usize;

		if advanced.state.receive_key_at(slot) != Some(sequence) {
			return None;
		}
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return None;
		}
		if slot_index != first_slot as usize + skipped_count as usize {
			return None;
		}
		if staged_slots[slot_index].is_some() {
			return None;
		}

		let stepped = match current_chain.as_ref() {
			Some(chain) => step(chain),
			None => step(entry_chain),
		};

		let RatchetStep { chain, material } = stepped;

		if sequence >= target {
			return None;
		}

		staged_slots[slot_index] = Some(CachedReceiveKey { sequence, material });

		current_chain = Some(chain);
		current_control = advanced.state;
		skipped_count += 1;
		left -= 1;
	}

	None
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
pub(super) fn receive_control_prefix_matches(
	entry: RatchetState,
	committed: RatchetState,
	slot: u8,
	remaining: u8,
) -> bool {
	let mut current_slot = slot;
	let mut left = remaining;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		if current_slot as usize >= RECEIVE_CACHE_CAPACITY {
			return false;
		}
		if !(entry.receive_key_at(current_slot) == committed.receive_key_at(current_slot)) {
			return false;
		}

		current_slot += 1;
		left -= 1;
	}

	true
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
pub(super) fn pending_receive_slots_are_valid<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	pending: &PendingReceive<ReceiveChain, Material>,
	slot: u8,
	expected_sequence: u64,
	remaining: u8,
) -> bool {
	let mut current_slot = slot;
	let mut expected = expected_sequence;
	let mut left = remaining;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		let slot_index = current_slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return false;
		}
		if state.receive_slots[slot_index].is_some() {
			return false;
		}

		let staged = match pending.staged_slots[slot_index].as_ref() {
			Some(staged) => staged,
			None => return false,
		};

		if !(staged.sequence == expected) {
			return false;
		}

		if !(pending.committed_control.receive_key_at(current_slot) == Some(expected)) {
			return false;
		}

		left -= 1;
		if left == 0 {
			break;
		}

		if expected == u64::MAX {
			return false;
		}

		current_slot += 1;
		expected += 1;
	}

	true
}

/// Validate the complete private publication invariant before it can escape
/// preparation. Publication itself can therefore be a total movement phase.
pub(super) fn pending_receive_is_valid<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	pending: &PendingReceive<ReceiveChain, Material>,
	requested: u64,
) -> bool {
	let entry_receive_sequence = state.control.receive_sequence();
	if !(pending.target_sequence == requested) {
		return false;
	}
	if requested <= entry_receive_sequence {
		return false;
	}
	if !(pending.first_slot == state.control.receive_cache_len()) {
		return false;
	}
	if !(pending.committed_control.send_sequence() == state.control.send_sequence()) {
		return false;
	}
	if !(pending.committed_control.receive_sequence() == requested) {
		return false;
	}
	if !(requested - entry_receive_sequence == pending.skipped as u64 + 1) {
		return false;
	}
	if lookup_receive_key(pending.committed_control, requested).is_some() {
		return false;
	}

	let committed_len = pending.first_slot as usize + pending.skipped as usize;
	if committed_len > RECEIVE_CACHE_CAPACITY {
		return false;
	}
	if !(pending.committed_control.receive_cache_len() as usize == committed_len) {
		return false;
	}
	if !receive_control_prefix_matches(
		state.control,
		pending.committed_control,
		0,
		pending.first_slot,
	) {
		return false;
	}
	if committed_len < RECEIVE_CACHE_CAPACITY {
		if state.receive_slots[committed_len].is_some() {
			return false;
		}
		if pending.staged_slots[committed_len].is_some() {
			return false;
		}
	}

	let expected_first = entry_receive_sequence + 1;
	pending_receive_slots_are_valid(
		state,
		pending,
		pending.first_slot,
		expected_first,
		pending.skipped,
	)
}

/// Plan and privately prepare the complete target transaction while leaving
/// the live refined ratchet unchanged.
#[cfg(test)]
pub(super) fn prepare_receive<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	target: u64,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
) -> Option<PreparedReceive<ReceiveChain, Material>> {
	let plan = plan_receive_until(state.control, target);
	let sequence = plan.sequence?;
	if plan.derivations == 0 {
		return prepare_cached_receive(state, sequence)
			.map(PreparedReceive::PreparedReceiveCachedCase);
	}
	let skipped = plan.derivations - 1;
	if skipped > RATCHET_MAX_GAP {
		return None;
	}

	let remaining = plan.derivations as u8;
	let first_slot = state.control.receive_cache_len();
	if !refined_receive_slots_are_empty(state, first_slot, skipped as u8) {
		return None;
	}
	let mut staged_slots = empty_material_slots();
	let PreparedFutureTarget {
		committed_control,
		final_receive_chain,
		target_sequence,
		target_material,
		first_slot,
		skipped,
	} = prepare_future_receive_steps(
		&state.receive_chain,
		state.control,
		sequence,
		step,
		remaining,
		first_slot,
		0,
		&mut staged_slots,
	)?;
	let pending = PendingReceive {
		committed_control,
		final_receive_chain,
		staged_slots,
		target_sequence,
		target_material,
		first_slot,
		skipped,
	};
	if !pending_receive_is_valid(state, &pending, target) {
		return None;
	}
	Some(PreparedReceive::PreparedReceiveFutureCase(pending))
}

/// Publish a prevalidated cached removal with no remaining failure branch.
pub(super) fn publish_cached_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	prepared: PreparedCachedReceive,
) {
	let target_index = prepared.target_slot as usize;
	let last_index = prepared.last_slot as usize;
	// Preparation proves these bounds. Keep the defensive branch so the
	// extracted total function carries the array-index precondition directly.
	if target_index >= RECEIVE_CACHE_CAPACITY {
		return;
	}
	if last_index >= RECEIVE_CACHE_CAPACITY {
		return;
	}
	if target_index == last_index {
		let _ = state.receive_slots[last_index].take();
	} else {
		let moved = state.receive_slots[last_index].take();
		state.receive_slots[target_index] = moved;
	}
	state.control = prepared.committed_control;
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
pub(super) fn publish_future_receive_slots<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	staged_slots: &mut [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
	slot: u8,
	remaining: u8,
) {
	let mut current_slot = slot;
	let mut left = remaining;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		let slot_index = current_slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return;
		}

		let moved = staged_slots[slot_index].take();
		state.receive_slots[slot_index] = moved;

		current_slot += 1;
		left -= 1;
	}
}

/// Publish a validated future delta. The target material remains in `pending`
/// and is dropped instead of ever entering the live cache.
pub(super) fn publish_future_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	mut pending: PendingReceive<ReceiveChain, Material>,
) {
	let first_index = pending.first_slot as usize;
	let skipped = pending.skipped as usize;
	// The private validator establishes this complete range before the open
	// callback. Repeat the range check here before the first mutation so even a
	// malformed internal value cannot publish a prefix.
	if first_index > RECEIVE_CACHE_CAPACITY {
		return;
	}
	if skipped > RECEIVE_CACHE_CAPACITY - first_index {
		return;
	}
	publish_future_receive_slots(
		state,
		&mut pending.staged_slots,
		pending.first_slot,
		pending.skipped,
	);
	state.receive_chain = pending.final_receive_chain;
	state.control = pending.committed_control;
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
/// Commit an already-preflighted suffix of receive steps.
///
/// Admission bounds the counter and cache.
/// Preflight proves every append destination vacant.
/// Each internal one-step result is successful.
/// This helper exposes no fallible intermediate result.
#[allow(dead_code)]
#[cfg(test)]
fn refined_execute_receive_steps<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
	remaining: u8,
) {
	let mut left = remaining;

	while left > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(left as usize);

		let _ = refined_advance_receive(state, step);
		left -= 1;
	}
}

/// Plan and execute every receive step needed for `target` inside the kernel.
///
/// Every destination slot is checked before the first callback.
/// Rejection is therefore neutral.
/// An accepted transaction has no intermediate failure branch.
/// It cannot publish only a prefix of the planned refinement.
#[allow(dead_code)]
#[cfg(test)]
pub(crate) fn refined_advance_receive_until<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	target: u64,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
) -> Option<u64> {
	let plan = plan_receive_until(state.control, target);
	let target = plan.sequence?;
	if plan.derivations > RATCHET_MAX_GAP {
		return None;
	}
	let remaining = plan.derivations as u8;
	let first_slot = state.control.receive_cache_len();
	if !refined_receive_slots_are_empty(state, first_slot, remaining) {
		return None;
	}
	refined_execute_receive_steps(state, step, remaining);
	Some(target)
}

/// Look up concrete receive material only through the verified logical cache.
#[allow(dead_code)]
pub(crate) fn refined_receive_key<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	sequence: u64,
) -> Option<&Material> {
	let slot = match lookup_receive_key(state.control, sequence) {
		Some(slot) => slot,
		None => return None,
	};
	let slot_index = slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY {
		return None;
	}
	let cached = match state.receive_slots[slot_index].as_ref() {
		Some(cached) => cached,
		None => return None,
	};
	if !(cached.sequence == sequence) {
		return None;
	}
	Some(&cached.material)
}

/// Complete a receive attempt and mutate logical and concrete slots together.
///
/// Missing and retained outcomes are neutral. Successful authentication applies
/// the core-selected target/last swap-removal internally before publishing the
/// returned control state.
#[allow(dead_code)]
#[cfg(test)]
pub(crate) fn refined_finish_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	sequence: u64,
	authenticated: bool,
) -> ReceiveDisposition {
	let Some(slot) = lookup_receive_key(state.control, sequence) else {
		return ReceiveDisposition::Missing;
	};
	let slot_index = slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY {
		return ReceiveDisposition::Missing;
	}
	let target_matches = match state.receive_slots[slot_index].as_ref() {
		Some(cached) => cached.sequence == sequence,
		None => false,
	};
	if !target_matches {
		return ReceiveDisposition::Missing;
	}

	let finished = finish_receive_with_removal(state.control, sequence, slot, authenticated);
	match finished.disposition {
		ReceiveDisposition::Missing => ReceiveDisposition::Missing,
		ReceiveDisposition::Retained => ReceiveDisposition::Retained,
		ReceiveDisposition::Consumed => {
			let Some(removal) = finished.removal else {
				return ReceiveDisposition::Missing;
			};
			let target_index = removal.target_slot as usize;
			let last_index = removal.last_slot as usize;
			if removal.target_slot != slot
				|| target_index >= RECEIVE_CACHE_CAPACITY
				|| last_index >= RECEIVE_CACHE_CAPACITY
			{
				return ReceiveDisposition::Missing;
			}
			let Some(last_sequence) = state.control.receive_key_at(removal.last_slot) else {
				return ReceiveDisposition::Missing;
			};
			let target_matches = match state.receive_slots[target_index].as_ref() {
				Some(cached) => cached.sequence == sequence,
				None => false,
			};
			let last_matches = match state.receive_slots[last_index].as_ref() {
				Some(cached) => cached.sequence == last_sequence,
				None => false,
			};
			if !target_matches || !last_matches {
				return ReceiveDisposition::Missing;
			}

			if target_index == last_index {
				let _ = state.receive_slots[last_index].take();
			} else {
				let moved = state.receive_slots[last_index].take();
				state.receive_slots[target_index] = moved;
			}
			state.control = finished.state;
			ReceiveDisposition::Consumed
		}
	}
}

/// Select the exact sequence-tagged receive material, try to authenticate and
/// open the supplied frame context, and finish that same attempt atomically.
///
/// Returning `Some` from the opaque callback consumes the selected material.
/// Returning `None` preserves the complete entry state. Future derivations are
/// owned by a private pending delta and are published only after the callback
/// succeeds. Neither raw material nor an independently supplied authentication
/// Boolean crosses this public API.
#[cfg(test)]
pub(crate) fn refined_open_and_finish<SendChain, ReceiveChain, Material, Context, Plaintext>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	target: u64,
	step: fn(&ReceiveChain) -> RatchetStep<ReceiveChain, Material>,
	context: &Context,
	open: fn(&Material, u64, &Context) -> Option<Plaintext>,
) -> Option<Plaintext> {
	let prepared = prepare_receive(state, target, step)?;
	match prepared {
		PreparedReceive::PreparedReceiveCachedCase(prepared) => {
			let opened = {
				let slot_index = prepared.target_slot as usize;
				if slot_index >= RECEIVE_CACHE_CAPACITY {
					return None;
				}
				let cached = state.receive_slots[slot_index].as_ref()?;
				if cached.sequence != prepared.sequence {
					return None;
				}
				open(&cached.material, prepared.sequence, context)
			};
			match opened {
				None => None,
				Some(plaintext) => {
					publish_cached_receive(state, prepared);
					Some(plaintext)
				}
			}
		}
		PreparedReceive::PreparedReceiveFutureCase(pending) => {
			let opened = open(&pending.target_material, pending.target_sequence, context);
			match opened {
				None => None,
				Some(plaintext) => {
					publish_future_receive(state, pending);
					Some(plaintext)
				}
			}
		}
	}
}
/// Checked restoration builder for a complete refined ratchet.
pub struct RefinedRatchetRestore<SendChain, ReceiveChain, Material> {
	pub(super) logical: RatchetRestore,
	pub(super) send_chain: SendChain,
	pub(super) receive_chain: ReceiveChain,
	pub(super) receive_slots: [Option<CachedReceiveKey<Material>>; RECEIVE_CACHE_CAPACITY],
}

pub fn start_refined_restore<SendChain, ReceiveChain, Material>(
	send_sequence: u64,
	receive_sequence: u64,
	send_chain: SendChain,
	receive_chain: ReceiveChain,
) -> RefinedRatchetRestore<SendChain, ReceiveChain, Material> {
	RefinedRatchetRestore {
		logical: start_restore(send_sequence, receive_sequence),
		send_chain,
		receive_chain,
		receive_slots: empty_material_slots(),
	}
}

/// Restore one sorted logical sequence and its concrete material atomically.
pub fn refined_restore_receive_key<SendChain, ReceiveChain, Material>(
	restore: &mut RefinedRatchetRestore<SendChain, ReceiveChain, Material>,
	sequence: u64,
	material: Material,
) -> bool {
	let Some(step) = restore_receive_key_with_slot(restore.logical, sequence) else {
		return false;
	};
	let slot_index = step.slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY || restore.receive_slots[slot_index].is_some() {
		return false;
	}
	restore.receive_slots[slot_index] = Some(CachedReceiveKey { sequence, material });
	restore.logical = step.restore;
	true
}

pub fn finish_refined_restore<SendChain, ReceiveChain, Material>(
	restore: RefinedRatchetRestore<SendChain, ReceiveChain, Material>,
) -> RefinedRatchet<SendChain, ReceiveChain, Material> {
	RefinedRatchet {
		control: finish_restore(restore.logical),
		send_chain: restore.send_chain,
		receive_chain: restore.receive_chain,
		receive_slots: restore.receive_slots,
	}
}
