// SPDX-License-Identifier: 0BSD

// Pinned Aeneas does not translate the `Try::branch` emitted by `?` reliably.
#![allow(clippy::question_mark)]

/// Maximum number of skipped receive keys retained for out-of-order delivery.
pub const RATCHET_MAX_GAP: u64 = 50;

/// Physical capacity of the logical receive-key cache.
pub const RECEIVE_CACHE_CAPACITY: usize = RATCHET_MAX_GAP as usize;

/// Opaque fixed-capacity cache of logical receive-key sequence numbers.
///
/// Its representation is public to the Hax/Lean proof boundary, while private
/// fields prevent Rust callers from constructing states that bypass validation.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct SequenceCache {
	pub(super) entries: [u64; RECEIVE_CACHE_CAPACITY],
	pub(super) len: u8,
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
/// Cryptographic chain state and concrete message-key bytes stay outside this type.
/// [`crate::ratchet::RefinedRatchet`] pairs sequences with concrete material.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct RatchetState {
	pub(super) send_sequence: u64,
	pub(super) receive_sequence: u64,
	pub(super) receive_cache: SequenceCache,
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
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct SendKey {
	pub(super) sequence: u64,
	pub(super) available: bool,
}

impl SendKey {
	pub(super) const fn unavailable() -> Self {
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
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
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
pub(crate) fn advance_send(state: RatchetState) -> SendAdvance {
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
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct SendFinish {
	pub key: SendKey,
	pub consumed: bool,
}

/// Consume a send key exactly once.
///
/// The refined kernel performs this transition after both successful and failed
/// encryption, matching beaconcrypt's existing one-use send-key policy.
pub(crate) fn finish_send(key: SendKey) -> SendFinish {
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
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceivePlan {
	pub sequence: Option<u64>,
	pub derivations: u64,
}

/// Decide whether `target` can be reached without exceeding the receive gap or
/// the total outstanding-key capacity.
///
/// A future target is derived but never inserted into the receive cache. Thus
/// `derivations` counts the target step in addition to the skipped keys, while
/// admission charges only the preceding skipped keys against the gap and cache.
pub(crate) fn plan_receive_until(state: RatchetState, target: u64) -> ReceivePlan {
	if target <= state.receive_sequence {
		return ReceivePlan {
			sequence: Some(target),
			derivations: 0,
		};
	}

	let derivations = target - state.receive_sequence;
	let skipped = derivations - 1;
	let cached = state.receive_cache.len as u64;
	if skipped > RATCHET_MAX_GAP || cached > RATCHET_MAX_GAP - skipped {
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

/// Result of deriving a future target without inserting it into the cache.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceiveTargetAdvance {
	pub state: RatchetState,
	pub sequence: Option<u64>,
}

/// Advance the receive sequence for the target key itself.
///
/// Unlike [`advance_receive`], this transition does not allocate a cache slot:
/// a successfully authenticated future target is consumed directly, while a
/// failed open rolls back to the entry state that owns this private result.
pub(crate) fn advance_receive_target(state: RatchetState) -> ReceiveTargetAdvance {
	if state.receive_sequence == u64::MAX {
		ReceiveTargetAdvance {
			state,
			sequence: None,
		}
	} else {
		let next = state.receive_sequence + 1;
		ReceiveTargetAdvance {
			state: RatchetState {
				receive_sequence: next,
				..state
			},
			sequence: Some(next),
		}
	}
}

/// Result of deriving one logical receive key.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceiveAdvance {
	pub state: RatchetState,
	pub sequence: Option<u64>,
	pub slot: Option<u8>,
}

/// Advance the receive chain by one skipped key and allocate its cache slot.
///
/// A future receive calls this once per skipped message, then uses
/// [`advance_receive_target`] for the uncached target. Exhaustion and a full
/// cache are state-neutral.
pub(crate) fn advance_receive(state: RatchetState) -> ReceiveAdvance {
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
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub enum ReceiveDisposition {
	/// The slot did not contain the requested sequence.
	Missing,
	/// Authentication failed, so the exact key remains available for retry.
	Retained,
	/// Authentication succeeded and the exact key was removed.
	Consumed,
}

/// Result of completing a receive attempt.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceiveFinish {
	pub state: RatchetState,
	pub disposition: ReceiveDisposition,
}

/// Physical swap-removal indices selected by the logical receive transition.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceiveRemoval {
	/// Slot containing the authenticated target before removal.
	pub target_slot: u8,
	/// Final active slot before removal.
	pub last_slot: u8,
}

/// Logical completion result plus the exact concrete removal operation.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct ReceiveFinishWithRemoval {
	pub state: RatchetState,
	pub disposition: ReceiveDisposition,
	pub removal: Option<ReceiveRemoval>,
}

/// Return the physical slot currently containing `sequence`.
///
/// The bounded scan is iterative so stack consumption is independent of
/// `RECEIVE_CACHE_CAPACITY`. The explicit remaining counter is retained as the
/// extraction-visible termination measure.
pub(crate) fn lookup_receive_key(state: RatchetState, sequence: u64) -> Option<u8> {
	let mut slot = 0u8;
	let mut remaining = RECEIVE_CACHE_CAPACITY as u8;

	while remaining > 0 {
		#[cfg(feature = "proverif")]
		hax_lib::loop_decreases!(remaining as usize);

		let slot_index = slot as usize;
		if slot_index >= RECEIVE_CACHE_CAPACITY {
			return None;
		}
		if slot >= state.receive_cache.len {
			return None;
		}
		if state.receive_cache.entries[slot_index] == sequence {
			return Some(slot);
		}

		slot += 1;
		remaining -= 1;
	}

	None
}

/// Complete authentication for a receive key identified by both slot and
/// sequence.
///
/// Requiring both values prevents a stale slot from consuming a different key.
/// Removal uses a visible fixed-array swap, avoiding assumed collection models
/// in the prover backend.
#[allow(dead_code)]
pub(crate) fn finish_receive(
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
pub(crate) fn finish_receive_with_removal(
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
		|| !(state.receive_cache.entries[slot_index] == target)
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
/// This typestate prevents callers from manufacturing an invalid `RatchetState`.
/// [`crate::ratchet::RefinedRatchetRestore`] additionally binds concrete material.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct RatchetRestore {
	pub(super) state: RatchetState,
	pub(super) last_sequence: u64,
}

pub const fn start_restore(send_sequence: u64, receive_sequence: u64) -> RatchetRestore {
	RatchetRestore {
		state: RatchetState::from_counters(send_sequence, receive_sequence),
		last_sequence: 0,
	}
}

/// One checked persistence-restoration append and its allocated slot.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
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

	let (receive_cache, slot) = match restore.state.receive_cache.append(sequence) {
		Some(value) => value,
		None => return None,
	};
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
/// Ratchet state associated with one peer identifier.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
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
	if !(requested_peer == peer.peer_id) {
		peer
	} else {
		PeerRatchetState {
			peer_id: peer.peer_id,
			ratchet: replacement,
		}
	}
}

/// Result of applying a send transition pointwise to a peer.
#[derive(Clone, Copy)]
#[cfg_attr(not(hax_compilation), derive(Debug, Eq, PartialEq))]
pub struct PeerSendAdvance {
	pub peer: PeerRatchetState,
	pub sequence: Option<u64>,
	pub key: SendKey,
}

/// Advance only the peer whose identifier matches `requested_peer`.
///
/// Applying this function pointwise to a uniquely keyed peer map gives the
/// frame rule: every non-selected peer is returned byte-for-byte unchanged.
#[allow(dead_code)]
pub(crate) fn advance_send_for_peer(
	requested_peer: u64,
	peer: PeerRatchetState,
) -> PeerSendAdvance {
	if !(requested_peer == peer.peer_id) {
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
