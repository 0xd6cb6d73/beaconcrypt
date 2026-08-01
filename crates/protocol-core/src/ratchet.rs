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
/// outside this type. Each cached sequence is a logical capability that the
/// adapter must refine to exactly one concrete receive key.
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

/// One-use logical capability for the concrete send key derived by an adapter.
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
/// The returned key is a logical capability: the crypto adapter derives the
/// concrete key for the same sequence and must finish it after its one use.
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
/// The high-level adapter performs this transition after both successful and
/// failed encryption, matching beaconcrypt's existing one-use send-key policy.
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
/// An adapter calls this exactly `ReceivePlan::derivations` times and derives
/// one concrete KDF output per successful step. Exhaustion and a full cache are
/// state-neutral.
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
	let len = state.receive_cache.len;
	let len_index = len as usize;
	let slot_index = slot as usize;
	if len_index > RECEIVE_CACHE_CAPACITY
		|| slot_index >= len_index
		|| state.receive_cache.entries[slot_index] != target
	{
		return ReceiveFinish {
			state,
			disposition: ReceiveDisposition::Missing,
		};
	}

	if !authenticated {
		return ReceiveFinish {
			state,
			disposition: ReceiveDisposition::Retained,
		};
	}

	let last_slot = len - 1;
	let mut entries = state.receive_cache.entries;
	entries[slot_index] = entries[last_slot as usize];
	entries[last_slot as usize] = 0;
	ReceiveFinish {
		state: RatchetState {
			receive_cache: SequenceCache {
				entries,
				len: last_slot,
			},
			..state
		},
		disposition: ReceiveDisposition::Consumed,
	}
}

/// Builder for restoring a ratchet from a sorted list of cached sequences.
///
/// Keeping restoration as a typestate prevents callers from manufacturing an
/// invalid `RatchetState`. The persistence adapter can sort its concrete map,
/// append every key here, and then compare the resulting logical set.
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

pub fn restore_receive_key(restore: RatchetRestore, sequence: u64) -> Option<RatchetRestore> {
	if sequence == 0
		|| sequence > restore.state.receive_sequence
		|| sequence <= restore.last_sequence
	{
		return None;
	}

	let (receive_cache, _) = restore.state.receive_cache.append(sequence)?;
	Some(RatchetRestore {
		state: RatchetState {
			receive_cache,
			..restore.state
		},
		last_sequence: sequence,
	})
}

pub const fn finish_restore(restore: RatchetRestore) -> RatchetState {
	restore.state
}

/// Ratchet state associated with one peer identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PeerRatchetState {
	pub peer_id: u64,
	pub ratchet: RatchetState,
}

/// Commit the result of any pure ratchet transition only to the selected peer.
///
/// Send and receive adapters use this pointwise operation after computing a
/// replacement `RatchetState`. Applying it over a uniquely keyed peer map gives
/// the common frame rule for every ratchet transition.
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
		PeerRatchetState, RATCHET_MAX_GAP, RECEIVE_CACHE_CAPACITY, RatchetState,
		ReceiveDisposition, advance_receive, advance_send, advance_send_for_peer, finish_receive,
		finish_restore, finish_send, plan_receive_until, replace_ratchet_for_peer,
		restore_receive_key, start_restore,
	};

	fn find_receive_key(state: &RatchetState, sequence: u64) -> Option<u8> {
		(0..state.receive_cache_len()).find(|&slot| state.receive_key_at(slot) == Some(sequence))
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

		let slot = find_receive_key(&state, RATCHET_MAX_GAP).unwrap();
		state = finish_receive(state, RATCHET_MAX_GAP, slot, true).state;
		assert_eq!(state.receive_cache_len(), RATCHET_MAX_GAP as u8 - 1);
		assert_eq!(
			plan_receive_until(state, RATCHET_MAX_GAP * 2).sequence,
			None
		);
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
		let slot = find_receive_key(&state, 4).unwrap();
		let failed = finish_receive(state, 4, slot, false);

		assert_eq!(failed.disposition, ReceiveDisposition::Retained);
		assert_eq!(failed.state, state);
		assert_eq!(failed.state.receive_key_at(slot), Some(4));
	}

	#[test]
	fn successful_receive_consumes_only_target_and_replay_is_rejected() {
		let state = execute_receive_plan(RatchetState::default(), 4);
		let target_slot = find_receive_key(&state, 3).unwrap();
		let consumed = finish_receive(state, 3, target_slot, true);

		assert_eq!(consumed.disposition, ReceiveDisposition::Consumed);
		assert_eq!(consumed.state.receive_cache_len(), 3);
		assert_eq!(find_receive_key(&consumed.state, 3), None);
		assert!(find_receive_key(&consumed.state, 1).is_some());
		assert!(find_receive_key(&consumed.state, 2).is_some());
		assert!(find_receive_key(&consumed.state, 4).is_some());

		let replay = finish_receive(consumed.state, 3, target_slot, true);
		assert_eq!(replay.disposition, ReceiveDisposition::Missing);
		assert_eq!(replay.state, consumed.state);
	}

	#[test]
	fn old_skipped_key_does_not_turn_capacity_into_a_sliding_window() {
		let mut state = execute_receive_plan(RatchetState::default(), RATCHET_MAX_GAP);
		for sequence in 2..=RATCHET_MAX_GAP {
			let slot = find_receive_key(&state, sequence).unwrap();
			state = finish_receive(state, sequence, slot, true).state;
		}

		for target in RATCHET_MAX_GAP + 1..=200 {
			state = execute_receive_plan(state, target);
			let slot = find_receive_key(&state, target).unwrap();
			state = finish_receive(state, target, slot, true).state;
		}

		assert_eq!(state.receive_sequence(), 200);
		assert_eq!(state.receive_cache_len(), 1);
		assert!(find_receive_key(&state, 1).is_some());
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
	fn restore_rejects_more_than_the_cache_capacity() {
		let mut restore = start_restore(0, RECEIVE_CACHE_CAPACITY as u64 + 1);
		for sequence in 1..=RECEIVE_CACHE_CAPACITY as u64 {
			restore = restore_receive_key(restore, sequence).unwrap();
		}
		assert!(restore_receive_key(restore, RECEIVE_CACHE_CAPACITY as u64 + 1).is_none());
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
