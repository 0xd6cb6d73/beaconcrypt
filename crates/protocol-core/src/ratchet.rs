// SPDX-License-Identifier: 0BSD

/// Maximum number of outstanding receive keys admitted by the ratchet.
pub const RATCHET_MAX_GAP: u64 = 50;

/// Physical capacity of the logical receive-key cache.
pub const RECEIVE_CACHE_CAPACITY: usize = RATCHET_MAX_GAP as usize;

/// Opaque fixed-capacity cache of logical receive-key sequence numbers.
///
/// Its representation is public to the hax/F* proof boundary, while private
/// fields prevent Rust callers from constructing states that bypass validation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SequenceCache {
	entries: [u64; RECEIVE_CACHE_CAPACITY],
	len: u8,
}

impl SequenceCache {
	const fn empty() -> Self {
		Self {
			entries: [0; RECEIVE_CACHE_CAPACITY],
			len: 0,
		}
	}

	fn append(self, sequence: u64) -> Option<(Self, u8)> {
		if sequence == 0 || self.len as usize >= RECEIVE_CACHE_CAPACITY {
			return None;
		}

		let slot = self.len;
		let mut entries = self.entries;
		entries[slot as usize] = sequence;
		Some((
			Self {
				entries,
				len: slot + 1,
			},
			slot,
		))
	}

	const fn entry(&self, slot: u8) -> Option<u64> {
		let slot_index = slot as usize;
		if slot < self.len && slot_index < RECEIVE_CACHE_CAPACITY {
			Some(self.entries[slot_index])
		} else {
			None
		}
	}
}

/// Pure protocol state for one peer's symmetric ratchet.
///
/// Cryptographic chain state and concrete message-key bytes deliberately stay
/// outside this low-level type. [`RefinedRatchet`] binds each cached sequence to
/// exactly one concrete material value in the shared kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RatchetState {
	send_sequence: u64,
	receive_sequence: u64,
	receive_cache: SequenceCache,
}

impl RatchetState {
	/// Construct a state with no receive history or cached receive keys.
	pub const fn new(send_sequence: u64) -> Self {
		Self::from_counters(send_sequence, 0)
	}

	/// Construct a state with counters but no outstanding receive keys.
	pub const fn from_counters(send_sequence: u64, receive_sequence: u64) -> Self {
		Self {
			send_sequence,
			receive_sequence,
			receive_cache: SequenceCache::empty(),
		}
	}

	pub const fn send_sequence(&self) -> u64 {
		self.send_sequence
	}

	pub const fn receive_sequence(&self) -> u64 {
		self.receive_sequence
	}

	pub const fn receive_cache_len(&self) -> u8 {
		self.receive_cache.len
	}

	/// Return the logical receive-key sequence stored in `slot`.
	pub const fn receive_key_at(&self, slot: u8) -> Option<u64> {
		self.receive_cache.entry(slot)
	}
}

impl Default for RatchetState {
	fn default() -> Self {
		Self::new(0)
	}
}

/// One-use logical capability paired with concrete send material by the refined kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SendKey {
	sequence: u64,
	available: bool,
}

impl SendKey {
	const fn unavailable() -> Self {
		Self {
			sequence: 0,
			available: false,
		}
	}

	pub const fn sequence(&self) -> Option<u64> {
		if self.available {
			Some(self.sequence)
		} else {
			None
		}
	}

	pub const fn is_available(&self) -> bool {
		self.available
	}
}

/// Result of attempting to allocate the next sending sequence number.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SendAdvance {
	pub state: RatchetState,
	pub sequence: Option<u64>,
	pub key: SendKey,
}

/// Advance the sending sequence once, unless its `u64` counter is exhausted.
///
/// The returned key is a low-level logical capability. [`refined_advance_send`]
/// pairs it with the concrete material returned by the opaque step for the same
/// sequence and requires that pair to be finished after its one use.
pub fn advance_send(state: RatchetState) -> SendAdvance {
	if state.send_sequence == u64::MAX {
		SendAdvance {
			state,
			sequence: None,
			key: SendKey::unavailable(),
		}
	} else {
		let next = state.send_sequence + 1;
		let key = SendKey {
			sequence: next,
			available: true,
		};
		SendAdvance {
			state: RatchetState {
				send_sequence: next,
				..state
			},
			sequence: Some(next),
			key,
		}
	}
}

/// Result of consuming a logical send-key capability.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SendFinish {
	pub key: SendKey,
	pub consumed: bool,
}

/// Consume a send key exactly once.
///
/// The refined kernel performs this transition after both successful and failed
/// encryption, matching beaconcrypt's existing one-use send-key policy.
pub fn finish_send(key: SendKey) -> SendFinish {
	if key.available {
		SendFinish {
			key: SendKey {
				sequence: key.sequence,
				available: false,
			},
			consumed: true,
		}
	} else {
		SendFinish {
			key,
			consumed: false,
		}
	}
}

/// Admission plan for a receive sequence.
///
/// `sequence == None` is a state-neutral rejection. A zero derivation count
/// deliberately preserves the current low-level behavior for old, consumed,
/// and zero sequences: a later key lookup decides whether the key exists.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceivePlan {
	pub sequence: Option<u64>,
	pub derivations: u64,
}

/// Decide whether `target` can be reached without exceeding the receive gap or
/// the total outstanding-key capacity.
pub fn plan_receive_until(state: RatchetState, target: u64) -> ReceivePlan {
	if target <= state.receive_sequence {
		return ReceivePlan {
			sequence: Some(target),
			derivations: 0,
		};
	}

	let derivations = target - state.receive_sequence;
	let cached = state.receive_cache.len as u64;
	if derivations > RATCHET_MAX_GAP || cached > RATCHET_MAX_GAP - derivations {
		ReceivePlan {
			sequence: None,
			derivations: 0,
		}
	} else {
		ReceivePlan {
			sequence: Some(target),
			derivations,
		}
	}
}

/// Result of deriving one logical receive key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveAdvance {
	pub state: RatchetState,
	pub sequence: Option<u64>,
	pub slot: Option<u8>,
}

/// Advance the receive chain by exactly one key.
///
/// The refined executor calls this exactly `ReceivePlan::derivations` times and
/// binds one opaque step output to each successful logical advance. Exhaustion
/// and a full cache are state-neutral.
pub fn advance_receive(state: RatchetState) -> ReceiveAdvance {
	if state.receive_sequence == u64::MAX {
		return ReceiveAdvance {
			state,
			sequence: None,
			slot: None,
		};
	}

	let next = state.receive_sequence + 1;
	if let Some((receive_cache, slot)) = state.receive_cache.append(next) {
		ReceiveAdvance {
			state: RatchetState {
				receive_sequence: next,
				receive_cache,
				..state
			},
			sequence: Some(next),
			slot: Some(slot),
		}
	} else {
		ReceiveAdvance {
			state,
			sequence: None,
			slot: None,
		}
	}
}

/// Outcome of authenticating a cached receive key.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReceiveDisposition {
	/// The slot did not contain the requested sequence.
	Missing,
	/// Authentication failed, so the exact key remains available for retry.
	Retained,
	/// Authentication succeeded and the exact key was removed.
	Consumed,
}

/// Result of completing a receive attempt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveFinish {
	pub state: RatchetState,
	pub disposition: ReceiveDisposition,
}

/// Physical swap-removal indices selected by the logical receive transition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveRemoval {
	/// Slot containing the authenticated target before removal.
	pub target_slot: u8,
	/// Final active slot before removal.
	pub last_slot: u8,
}

/// Logical completion result plus the exact concrete removal operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveFinishWithRemoval {
	pub state: RatchetState,
	pub disposition: ReceiveDisposition,
	pub removal: Option<ReceiveRemoval>,
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
fn lookup_receive_key_from(
	state: RatchetState,
	sequence: u64,
	slot: u8,
	remaining: u8,
) -> Option<u8> {
	if remaining == 0 {
		return None;
	}
	if (slot as usize) >= RECEIVE_CACHE_CAPACITY {
		return None;
	}
	if slot >= state.receive_cache.len {
		return None;
	}
	if state.receive_cache.entries[slot as usize] == sequence {
		return Some(slot);
	}
	lookup_receive_key_from(state, sequence, slot + 1, remaining - 1)
}

/// Return the physical slot currently containing `sequence`.
pub fn lookup_receive_key(state: RatchetState, sequence: u64) -> Option<u8> {
	lookup_receive_key_from(state, sequence, 0, RECEIVE_CACHE_CAPACITY as u8)
}

/// Complete authentication for a receive key identified by both slot and
/// sequence.
///
/// Requiring both values prevents a stale slot from consuming a different key.
/// Removal uses a visible fixed-array swap, avoiding assumed collection models
/// in the prover backend.
pub fn finish_receive(
	state: RatchetState,
	target: u64,
	slot: u8,
	authenticated: bool,
) -> ReceiveFinish {
	let finished = finish_receive_with_removal(state, target, slot, authenticated);
	ReceiveFinish {
		state: finished.state,
		disposition: finished.disposition,
	}
}

/// Complete a receive attempt and return the physical swap-removal plan.
///
/// Missing or retained keys return no plan and leave `state` unchanged. A
/// consumed key returns the target slot and the old final active slot.
pub fn finish_receive_with_removal(
	state: RatchetState,
	target: u64,
	slot: u8,
	authenticated: bool,
) -> ReceiveFinishWithRemoval {
	let len = state.receive_cache.len;
	let len_index = len as usize;
	let slot_index = slot as usize;
	if len_index > RECEIVE_CACHE_CAPACITY
		|| slot_index >= len_index
		|| state.receive_cache.entries[slot_index] != target
	{
		return ReceiveFinishWithRemoval {
			state,
			disposition: ReceiveDisposition::Missing,
			removal: None,
		};
	}

	if !authenticated {
		return ReceiveFinishWithRemoval {
			state,
			disposition: ReceiveDisposition::Retained,
			removal: None,
		};
	}

	let last_slot = len - 1;
	let mut entries = state.receive_cache.entries;
	entries[slot_index] = entries[last_slot as usize];
	entries[last_slot as usize] = 0;
	ReceiveFinishWithRemoval {
		state: RatchetState {
			receive_cache: SequenceCache {
				entries,
				len: last_slot,
			},
			..state
		},
		disposition: ReceiveDisposition::Consumed,
		removal: Some(ReceiveRemoval {
			target_slot: slot,
			last_slot,
		}),
	}
}

/// Builder for restoring a ratchet from a sorted list of cached sequences.
///
/// Keeping restoration as a typestate prevents callers from manufacturing an
/// invalid `RatchetState`. [`RefinedRatchetRestore`] extends it so persistence
/// can append each sorted logical sequence and its concrete material atomically.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RatchetRestore {
	state: RatchetState,
	last_sequence: u64,
}

pub const fn start_restore(send_sequence: u64, receive_sequence: u64) -> RatchetRestore {
	RatchetRestore {
		state: RatchetState::from_counters(send_sequence, receive_sequence),
		last_sequence: 0,
	}
}

/// One checked persistence-restoration append and its allocated slot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceiveRestoreStep {
	pub restore: RatchetRestore,
	pub slot: u8,
}

/// Append one sorted receive sequence during restoration and return its slot.
pub fn restore_receive_key_with_slot(
	restore: RatchetRestore,
	sequence: u64,
) -> Option<ReceiveRestoreStep> {
	if sequence == 0
		|| sequence > restore.state.receive_sequence
		|| sequence <= restore.last_sequence
	{
		return None;
	}

	let (receive_cache, slot) = restore.state.receive_cache.append(sequence)?;
	Some(ReceiveRestoreStep {
		restore: RatchetRestore {
			state: RatchetState {
				receive_cache,
				..restore.state
			},
			last_sequence: sequence,
		},
		slot,
	})
}

pub fn restore_receive_key(restore: RatchetRestore, sequence: u64) -> Option<RatchetRestore> {
	restore_receive_key_with_slot(restore, sequence).map(|step| step.restore)
}

pub const fn finish_restore(restore: RatchetRestore) -> RatchetState {
	restore.state
}

/// One opaque ratchet-step result.
///
/// The shared kernel treats both fields parametrically. Production supplies the
/// HKDF implementation that computes them from the previous chain state.
pub struct RatchetStep<Chain, Material> {
	pub chain: Chain,
	pub material: Material,
}

fn empty_material_slots<Material>() -> [Option<Material>; RECEIVE_CACHE_CAPACITY] {
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
/// arbitrary opaque HKDF inputs and outputs. Private fields ensure Rust callers
/// can only construct and mutate the correspondence through this kernel.
#[derive(Clone)]
pub struct RefinedRatchet<SendChain, ReceiveChain, Material> {
	control: RatchetState,
	send_chain: SendChain,
	receive_chain: ReceiveChain,
	receive_slots: [Option<Material>; RECEIVE_CACHE_CAPACITY],
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
		let sequence = self.control.receive_key_at(slot)?;
		let slot_index = slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return None;
		}
		let material = self.receive_slots[slot_index].as_ref()?;
		Some((sequence, material))
	}
}

/// A stack-local concrete send key paired with its logical one-use capability.
///
/// This token is deliberately neither `Copy` nor `Clone`. Borrow its material
/// for one encryption attempt, then consume it with `refined_finish_send`.
pub struct RefinedSendKey<Material> {
	logical: SendKey,
	material: Material,
}

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
pub fn refined_advance_send<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	info: &[u8],
	step: fn(&SendChain, &[u8]) -> RatchetStep<SendChain, Material>,
) -> Option<RefinedSendKey<Material>> {
	let advanced = advance_send(state.control);
	let sequence = advanced.sequence?;
	if advanced.key.sequence() != Some(sequence) || advanced.state.send_sequence() != sequence {
		return None;
	}

	let stepped = step(&state.send_chain, info);
	state.send_chain = stepped.chain;
	state.control = advanced.state;
	Some(RefinedSendKey {
		logical: advanced.key,
		material: stepped.material,
	})
}

/// Consume a concrete/logical send token after its single permitted use.
pub fn refined_finish_send<Material>(key: RefinedSendKey<Material>) -> bool {
	let finished = finish_send(key.logical);
	finished.consumed && !finished.key.is_available()
}

/// Derive and cache exactly one receive key through the shared refined kernel.
///
/// Logical admission and slot validation happen before the sole opaque step.
/// Rejection therefore leaves the concrete chain and slots untouched.
pub fn refined_advance_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	info: &[u8],
	step: fn(&ReceiveChain, &[u8]) -> RatchetStep<ReceiveChain, Material>,
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

	let stepped = step(&state.receive_chain, info);
	state.receive_chain = stepped.chain;
	state.receive_slots[slot_index] = Some(stepped.material);
	state.control = advanced.state;
	Some(sequence)
}

#[cfg_attr(
	feature = "proverif",
	hax_lib::decreases(hax_lib::int::ToInt::to_int(remaining))
)]
fn refined_receive_slots_are_empty<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	first_slot: u8,
	remaining: u8,
) -> bool {
	if remaining == 0 {
		return true;
	}
	let slot_index = first_slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY || state.receive_slots[slot_index].is_some() {
		return false;
	}
	refined_receive_slots_are_empty(state, first_slot + 1, remaining - 1)
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
fn refined_execute_receive_steps<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	info: &[u8],
	step: fn(&ReceiveChain, &[u8]) -> RatchetStep<ReceiveChain, Material>,
	remaining: u8,
) {
	if remaining == 0 {
		return;
	}
	let _ = refined_advance_receive(state, info, step);
	refined_execute_receive_steps(state, info, step, remaining - 1)
}

/// Plan and execute every receive step needed for `target` inside the kernel.
///
/// Every destination slot is checked before the first callback.
/// Rejection is therefore neutral.
/// An accepted transaction has no intermediate failure branch.
/// It cannot publish only a prefix of the planned refinement.
pub fn refined_advance_receive_until<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	info: &[u8],
	target: u64,
	step: fn(&ReceiveChain, &[u8]) -> RatchetStep<ReceiveChain, Material>,
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
	refined_execute_receive_steps(state, info, step, remaining);
	Some(target)
}

/// Look up concrete receive material only through the verified logical cache.
pub fn refined_receive_key<SendChain, ReceiveChain, Material>(
	state: &RefinedRatchet<SendChain, ReceiveChain, Material>,
	sequence: u64,
) -> Option<&Material> {
	let slot = lookup_receive_key(state.control, sequence)?;
	let slot_index = slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY {
		return None;
	}
	state.receive_slots[slot_index].as_ref()
}

/// Complete a receive attempt and mutate logical and concrete slots together.
///
/// Missing and retained outcomes are neutral. Successful authentication applies
/// the core-selected target/last swap-removal internally before publishing the
/// returned control state.
pub fn refined_finish_receive<SendChain, ReceiveChain, Material>(
	state: &mut RefinedRatchet<SendChain, ReceiveChain, Material>,
	sequence: u64,
	authenticated: bool,
) -> ReceiveDisposition {
	let Some(slot) = lookup_receive_key(state.control, sequence) else {
		return ReceiveDisposition::Missing;
	};
	let slot_index = slot as usize;
	if slot_index >= RECEIVE_CACHE_CAPACITY || state.receive_slots[slot_index].is_none() {
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
				|| state.receive_slots[target_index].is_none()
				|| state.receive_slots[last_index].is_none()
			{
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

/// Checked restoration builder for a complete refined ratchet.
#[derive(Clone)]
pub struct RefinedRatchetRestore<SendChain, ReceiveChain, Material> {
	logical: RatchetRestore,
	send_chain: SendChain,
	receive_chain: ReceiveChain,
	receive_slots: [Option<Material>; RECEIVE_CACHE_CAPACITY],
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
	restore.receive_slots[slot_index] = Some(material);
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

/// Ratchet state associated with one peer identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PeerRatchetState {
	pub peer_id: u64,
	pub ratchet: RatchetState,
}

/// Commit the result of any pure ratchet transition only to the selected peer.
///
/// Compatibility proofs use this pointwise operation to state that applying a
/// replacement over a uniquely keyed peer map leaves every other peer unchanged.
pub fn replace_ratchet_for_peer(
	requested_peer: u64,
	peer: PeerRatchetState,
	replacement: RatchetState,
) -> PeerRatchetState {
	if requested_peer != peer.peer_id {
		peer
	} else {
		PeerRatchetState {
			peer_id: peer.peer_id,
			ratchet: replacement,
		}
	}
}

/// Result of applying a send transition pointwise to a peer.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PeerSendAdvance {
	pub peer: PeerRatchetState,
	pub sequence: Option<u64>,
	pub key: SendKey,
}

/// Advance only the peer whose identifier matches `requested_peer`.
///
/// Applying this function pointwise to a uniquely keyed peer map gives the
/// frame rule: every non-selected peer is returned byte-for-byte unchanged.
pub fn advance_send_for_peer(requested_peer: u64, peer: PeerRatchetState) -> PeerSendAdvance {
	if requested_peer != peer.peer_id {
		PeerSendAdvance {
			peer,
			sequence: None,
			key: SendKey::unavailable(),
		}
	} else {
		let advanced = advance_send(peer.ratchet);
		PeerSendAdvance {
			peer: replace_ratchet_for_peer(requested_peer, peer, advanced.state),
			sequence: advanced.sequence,
			key: advanced.key,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{
		PeerRatchetState, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetState, RatchetStep,
		ReceiveDisposition, RefinedRatchet, RefinedSendKey, SendKey, SequenceCache,
		advance_receive, advance_send, advance_send_for_peer, empty_material_slots, finish_receive,
		finish_receive_with_removal, finish_refined_restore, finish_restore, finish_send,
		lookup_receive_key, plan_receive_until, refined_advance_receive,
		refined_advance_receive_until, refined_advance_send, refined_finish_receive,
		refined_finish_send, refined_receive_key, refined_restore_receive_key,
		replace_ratchet_for_peer, restore_receive_key, restore_receive_key_with_slot,
		start_refined_restore, start_restore,
	};

	#[derive(Debug, Eq, PartialEq)]
	struct TestMaterial {
		generation: u64,
		info_len: usize,
	}

	fn test_step(chain: &u64, info: &[u8]) -> RatchetStep<u64, TestMaterial> {
		let next = chain + 1;
		RatchetStep {
			chain: next,
			material: TestMaterial {
				generation: next,
				info_len: info.len(),
			},
		}
	}

	fn rejected_test_step(_chain: &u64, _info: &[u8]) -> RatchetStep<u64, TestMaterial> {
		panic!("rejected receive transaction invoked its KDF callback")
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
		let key = refined_advance_send(&mut state, b"send", test_step).unwrap();

		assert_eq!(key.sequence(), Some(8));
		assert_eq!(key.material().generation, 11);
		assert_eq!(key.material().info_len, 4);
		assert_eq!(*state.send_chain(), 11);
		assert_eq!(*state.receive_chain(), 20);
		assert_eq!(state.send_sequence(), 8);
		assert_eq!(state.receive_sequence(), 0);
		assert!(refined_finish_send(key));
	}

	#[test]
	fn refined_send_finish_rejects_an_unavailable_logical_key() {
		let key = RefinedSendKey {
			logical: SendKey::unavailable(),
			material: TestMaterial {
				generation: 0,
				info_len: 0,
			},
		};

		assert!(!refined_finish_send(key));
	}

	#[test]
	fn refined_send_exhaustion_is_concretely_neutral() {
		let mut state =
			RefinedRatchet::<u64, u64, TestMaterial>::from_counters(u64::MAX, 4, 10, 20);

		assert!(refined_advance_send(&mut state, b"send", test_step).is_none());
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
		let boundary = plan_receive_until(state, RATCHET_MAX_GAP);
		let rejected = plan_receive_until(state, RATCHET_MAX_GAP + 1);

		assert_eq!(boundary.sequence, Some(RATCHET_MAX_GAP));
		assert_eq!(boundary.derivations, RATCHET_MAX_GAP);
		assert_eq!(rejected.sequence, None);
		assert_eq!(rejected.derivations, 0);
		assert_eq!(state, RatchetState::default());
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
			refined_advance_receive_until(&mut state, b"recv", 4, test_step),
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
			assert_eq!(material.info_len, 4);
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
				refined_advance_receive_until(&mut state, b"recv", distance, test_step,),
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
			refined_advance_receive_until(
				&mut state,
				b"recv",
				RATCHET_MAX_GAP + 1,
				rejected_test_step,
			),
			None
		);
		assert_eq!(state.receive_sequence(), 0);
		assert_eq!(state.receive_cache_len(), 0);
		assert_eq!(*state.receive_chain(), 20);
		assert!(state.receive_entry_at(0).is_none());

		assert_eq!(
			refined_advance_receive_until(&mut state, b"recv", 3, test_step),
			Some(3)
		);
		assert_eq!(*state.receive_chain(), 23);
	}

	#[test]
	fn refined_receive_transaction_rejects_a_later_occupied_slot_before_stepping() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		state.receive_slots[1] = Some(TestMaterial {
			generation: 99,
			info_len: 0,
		});

		assert_eq!(
			refined_advance_receive_until(&mut state, b"recv", 2, rejected_test_step),
			None
		);
		assert_eq!(state.control, RatchetState::default());
		assert_eq!(*state.receive_chain(), 20);
		assert!(state.receive_slots[0].is_none());
		assert_eq!(state.receive_slots[1].as_ref().unwrap().generation, 99);
	}

	#[test]
	fn refined_receive_rejects_an_occupied_append_slot() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		state.receive_slots[0] = Some(TestMaterial {
			generation: 99,
			info_len: 0,
		});

		assert_eq!(
			refined_advance_receive(&mut state, b"recv", rejected_test_step),
			None
		);
		assert_eq!(state.control, RatchetState::default());
		assert_eq!(*state.receive_chain(), 20);
		assert_eq!(state.receive_slots[0].as_ref().unwrap().generation, 99);
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
		missing_last.receive_slots[0] = Some(TestMaterial {
			generation: 21,
			info_len: 4,
		});
		assert_eq!(
			refined_finish_receive(&mut missing_last, 1, true),
			ReceiveDisposition::Missing
		);
		assert_eq!(missing_last.control, control);
		assert_eq!(
			missing_last.receive_slots[0].as_ref().unwrap().generation,
			21
		);
	}

	#[test]
	fn refined_receive_failure_retains_and_success_swaps_material() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);
		assert_eq!(
			refined_advance_receive_until(&mut state, b"recv", 4, test_step),
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
	fn refined_receive_one_step_uses_the_next_empty_slot() {
		let mut state = RefinedRatchet::<u64, u64, TestMaterial>::new(10, 20);

		assert_eq!(
			refined_advance_receive(&mut state, b"recv", test_step),
			Some(1)
		);
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
			TestMaterial {
				generation: 22,
				info_len: 4,
			}
		));
		assert!(!refined_restore_receive_key(
			&mut restore,
			2,
			TestMaterial {
				generation: 999,
				info_len: 0,
			}
		));
		assert!(refined_restore_receive_key(
			&mut restore,
			7,
			TestMaterial {
				generation: 27,
				info_len: 4,
			}
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
	fn refined_restore_rejects_an_occupied_append_slot() {
		let mut restore = start_refined_restore::<u64, u64, TestMaterial>(9, 12, 100, 200);
		restore.receive_slots[0] = Some(TestMaterial {
			generation: 99,
			info_len: 0,
		});

		assert!(!refined_restore_receive_key(
			&mut restore,
			2,
			TestMaterial {
				generation: 22,
				info_len: 4,
			}
		));
		assert_eq!(restore.logical, start_restore(9, 12));
		assert_eq!(restore.receive_slots[0].as_ref().unwrap().generation, 99);
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
