/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_protocol_core.Ratchet.Lemmas

open Rust_primitives.Integers
open Beaconcrypt_protocol_core.Ratchet

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

/// Logical view of the active part of the fixed receive-key cache.  The Rust
/// array has length 50 by construction; validity additionally constrains the
/// logical length and the values stored before it.
let cache_len (cache:t_SequenceCache) : nat = v cache.f_len

let cache_entry (cache:t_SequenceCache) (i:nat{i < 50}) : u64 =
  Seq.index cache.f_entries i

let cache_has (cache:t_SequenceCache) (sequence:u64) : prop =
  exists (i:nat{i < 50}).
    i < cache_len cache /\ cache_entry cache i == sequence

let valid_cache (receive_sequence:u64) (cache:t_SequenceCache) : prop =
  cache_len cache <= 50 /\
  (forall (i:nat{i < 50}).
     i < cache_len cache ==>
       v (cache_entry cache i) > 0 /\
       v (cache_entry cache i) <= v receive_sequence) /\
  (forall (i:nat{i < 50}) (j:nat{j < 50}).
     i < cache_len cache /\ j < cache_len cache /\
     cache_entry cache i == cache_entry cache j ==> i == j)

let valid_state (state:t_RatchetState) : prop =
  valid_cache state.f_receive_sequence state.f_receive_cache

/// Restoration additionally tracks an upper bound for every sequence already
/// appended.  The next accepted sequence must be strictly greater than this
/// bound, which is what prevents duplicate imported keys.
let valid_restore (restore:t_RatchetRestore) : prop =
  valid_state restore.f_state /\
  (forall (i:nat{i < 50}).
     i < cache_len restore.f_state.f_receive_cache ==>
       v (cache_entry restore.f_state.f_receive_cache i) <=
       v restore.f_last_sequence)

let cache_slot
    (cache:t_SequenceCache)
    (sequence:u64)
    (slot:u8)
  : prop =
  v slot < cache_len cache /\
  v slot < 50 /\
  cache_entry cache (v slot) == sequence

/// Empty-cache constructors establish the receive invariant for arbitrary
/// counter values.
let from_counters_is_valid (send_sequence receive_sequence:u64)
  : Lemma (valid_state (impl_RatchetState__from_counters send_sequence receive_sequence))
  = ()

let start_restore_is_valid (send_sequence receive_sequence:u64)
  : Lemma (valid_restore (start_restore send_sequence receive_sequence))
  = ()

/// A successful send-counter allocation is exactly one greater than the old
/// counter.  Stating the result through `v` also makes the no-wrap property
/// explicit: this is mathematical addition, not modular arithmetic.
let advance_send_is_monotonic (state: t_RatchetState)
  : Lemma
      (match (advance_send state).f_sequence with
       | Core_models.Option.Option_Some next ->
           (advance_send state).f_state.f_send_sequence == next /\
           v next == v state.f_send_sequence + 1
       | Core_models.Option.Option_None ->
           (advance_send state).f_state == state /\
           state.f_send_sequence == Core_models.Num.impl_u64__MAX)
  = ()

/// Exhaustion is a state-neutral result and cannot manufacture sequence zero.
let advance_send_exhaustion_is_neutral
    (state: t_RatchetState { state.f_send_sequence == Core_models.Num.impl_u64__MAX })
  : Lemma
      ((advance_send state).f_state == state /\
       (advance_send state).f_sequence == Core_models.Option.Option_None)
  = ()

/// Send advancement touches no receive state, and therefore preserves the
/// receive-cache invariant.
let advance_send_preserves_receive_state (state:t_RatchetState)
  : Lemma
      ((advance_send state).f_state.f_receive_sequence == state.f_receive_sequence /\
       (advance_send state).f_state.f_receive_cache == state.f_receive_cache /\
       (valid_state state ==> valid_state (advance_send state).f_state))
  = ()

/// A successful allocation and its logical capability name the same key.
let advance_send_key_matches_sequence (state:t_RatchetState)
  : Lemma
      (match (advance_send state).f_sequence with
       | Core_models.Option.Option_Some sequence ->
           (advance_send state).f_key.f_available /\
           (advance_send state).f_key.f_sequence == sequence
       | Core_models.Option.Option_None ->
           not (advance_send state).f_key.f_available)
  = ()

/// Finishing an available send capability consumes exactly that capability.
let finish_send_consumes_available
    (key:t_SendKey { key.f_available })
  : Lemma
      ((finish_send key).f_consumed /\
       not (finish_send key).f_key.f_available /\
       (finish_send key).f_key.f_sequence == key.f_sequence)
  = ()

/// An unavailable capability cannot be consumed a second time.
let finish_send_rejects_reuse
    (key:t_SendKey { not key.f_available })
  : Lemma
      (not (finish_send key).f_consumed /\
       (finish_send key).f_key == key)
  = ()

let finish_send_is_one_use (key:t_SendKey)
  : Lemma
      (not (finish_send (finish_send key).f_key).f_consumed /\
       (finish_send (finish_send key).f_key).f_key == (finish_send key).f_key)
  = ()

/// Requests for old/current sequences require no derivation.  In particular,
/// this deliberately does not claim the key is still cached.
let plan_old_receive_is_zero_cost
    (state:t_RatchetState)
    (target:u64 { v target <= v state.f_receive_sequence })
  : Lemma
      ((plan_receive_until state target).f_sequence ==
         Core_models.Option.Option_Some target /\
       (plan_receive_until state target).f_derivations == mk_u64 0)
  = ()

/// An admitted future request stays inside both the forward window and the
/// total outstanding-key bound.
let plan_future_receive_is_bounded
    (state:t_RatchetState)
    (target:u64 { v target > v state.f_receive_sequence })
  : Lemma
      (match (plan_receive_until state target).f_sequence with
       | Core_models.Option.Option_Some sequence ->
           sequence == target /\
           v (plan_receive_until state target).f_derivations ==
             v target - v state.f_receive_sequence /\
           v (plan_receive_until state target).f_derivations > 0 /\
           v (plan_receive_until state target).f_derivations <= 50 /\
           cache_len state.f_receive_cache +
             v (plan_receive_until state target).f_derivations <= 50
       | Core_models.Option.Option_None ->
           (plan_receive_until state target).f_derivations == mk_u64 0)
  = ()

let plan_receive_rejects_large_gap
    (state:t_RatchetState)
    (target:u64 {
       v target > v state.f_receive_sequence /\
       v target - v state.f_receive_sequence > 50 })
  : Lemma
      ((plan_receive_until state target).f_sequence == Core_models.Option.Option_None /\
       (plan_receive_until state target).f_derivations == mk_u64 0)
  = ()

let plan_receive_rejects_capacity_overflow
    (state:t_RatchetState)
    (target:u64 {
       v target > v state.f_receive_sequence /\
       v target - v state.f_receive_sequence <= 50 /\
       cache_len state.f_receive_cache +
         (v target - v state.f_receive_sequence) > 50 })
  : Lemma
      ((plan_receive_until state target).f_sequence == Core_models.Option.Option_None /\
       (plan_receive_until state target).f_derivations == mk_u64 0)
  = ()

/// A successful receive step advances exactly once, appends the new key, and
/// does not alter the sending counter.
let advance_receive_success_shape (state:t_RatchetState)
  : Lemma
      (match (advance_receive state).f_sequence, (advance_receive state).f_slot with
       | Core_models.Option.Option_Some sequence,
         Core_models.Option.Option_Some slot ->
           v sequence == v state.f_receive_sequence + 1 /\
           (advance_receive state).f_state.f_receive_sequence == sequence /\
           (advance_receive state).f_state.f_send_sequence == state.f_send_sequence /\
           cache_len (advance_receive state).f_state.f_receive_cache ==
             cache_len state.f_receive_cache + 1 /\
           v slot == cache_len state.f_receive_cache /\
           cache_slot (advance_receive state).f_state.f_receive_cache sequence slot
       | Core_models.Option.Option_None,
         Core_models.Option.Option_None ->
           (advance_receive state).f_state == state
       | _ -> False)
  = ()

/// Exhaustion and a full valid cache are neutral failures.
let advance_receive_exhaustion_is_neutral
    (state:t_RatchetState {
       state.f_receive_sequence == Core_models.Num.impl_u64__MAX })
  : Lemma
      ((advance_receive state).f_state == state /\
       (advance_receive state).f_sequence == Core_models.Option.Option_None /\
       (advance_receive state).f_slot == Core_models.Option.Option_None)
  = ()

let advance_receive_full_cache_is_neutral
    (state:t_RatchetState { cache_len state.f_receive_cache == 50 })
  : Lemma
      ((advance_receive state).f_state == state /\
       (advance_receive state).f_sequence == Core_models.Option.Option_None /\
       (advance_receive state).f_slot == Core_models.Option.Option_None)
  = ()

/// The next sequence is newer than every cached sequence in a valid state, so
/// append cannot introduce a duplicate.  This is the core skipped-key
/// uniqueness preservation theorem.
let advance_receive_preserves_validity
    (state:t_RatchetState { valid_state state })
  : Lemma (valid_state (advance_receive state).f_state)
  = ()

/// Wrong slot/sequence pairs cannot consume anything.
let finish_receive_missing_is_neutral
    (state:t_RatchetState)
    (target:u64)
    (slot:u8 { ~(cache_slot state.f_receive_cache target slot) })
    (authenticated:bool)
  : Lemma
      ((finish_receive state target slot authenticated).f_disposition ==
         ReceiveDisposition_Missing /\
       (finish_receive state target slot authenticated).f_state == state)
  = ()

/// Authentication failure retains the exact candidate and all ratchet state,
/// permitting a byte-for-byte retry.
let finish_receive_failure_retains_key
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      ((finish_receive state target slot false).f_disposition ==
         ReceiveDisposition_Retained /\
       (finish_receive state target slot false).f_state == state /\
       cache_slot
         (finish_receive state target slot false).f_state.f_receive_cache
         target
         slot)
  = ()

/// Successful authentication removes one logical entry and leaves both
/// counters unchanged.
let finish_receive_success_shape
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      ((finish_receive state target slot true).f_disposition ==
         ReceiveDisposition_Consumed /\
       cache_len (finish_receive state target slot true).f_state.f_receive_cache + 1 ==
         cache_len state.f_receive_cache /\
       (finish_receive state target slot true).f_state.f_send_sequence ==
         state.f_send_sequence /\
       (finish_receive state target slot true).f_state.f_receive_sequence ==
         state.f_receive_sequence)
  = ()

/// Swap-removal preserves the cache bound, key range, and uniqueness.
let finish_receive_preserves_validity
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8)
    (authenticated:bool)
  : Lemma (valid_state (finish_receive state target slot authenticated).f_state)
  = ()

/// Under the uniqueness invariant, successful authentication removes exactly
/// the target capability.  A second use of the old `(target, slot)` pair is a
/// neutral replay rejection.
let finish_receive_consumes_target
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      (~(cache_has (finish_receive state target slot true).f_state.f_receive_cache target))
  = ()

/// Every cached capability other than the authenticated target survives the
/// swap-removal.  Together with `finish_receive_consumes_target`, this states
/// that successful authentication removes exactly one logical key.
let finish_receive_preserves_other_key
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
    (other:u64 {
       other <> target /\ cache_has state.f_receive_cache other })
  : Lemma
      (cache_has
         (finish_receive state target slot true).f_state.f_receive_cache
         other)
  = ()

let finish_receive_replay_is_rejected
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      (let consumed = (finish_receive state target slot true).f_state in
       (finish_receive consumed target slot true).f_disposition ==
         ReceiveDisposition_Missing /\
       (finish_receive consumed target slot true).f_state == consumed)
  = ()

/// A one-step admissible future receive advances before authentication.  If
/// authentication then fails, the candidate key and the entire post-admission
/// state are retained; the result is therefore not neutral relative to the
/// state that existed before admission.
let admitted_receive_failure_retains_advanced_state
    (state:t_RatchetState {
       valid_state state /\ cache_len state.f_receive_cache < 50 })
    (target:u64 {
       v target == v state.f_receive_sequence + 1 })
  : Lemma
      (let plan = plan_receive_until state target in
       let advanced = advance_receive state in
       match advanced.f_sequence, advanced.f_slot with
       | Core_models.Option.Option_Some sequence,
         Core_models.Option.Option_Some slot ->
           let failed = finish_receive advanced.f_state sequence slot false in
           plan.f_sequence == Core_models.Option.Option_Some target /\
           plan.f_derivations == mk_u64 1 /\
           sequence == target /\
           failed.f_disposition == ReceiveDisposition_Retained /\
           failed.f_state == advanced.f_state /\
           cache_slot failed.f_state.f_receive_cache target slot /\
           v failed.f_state.f_receive_sequence ==
             v state.f_receive_sequence + 1 /\
           cache_len failed.f_state.f_receive_cache ==
             cache_len state.f_receive_cache + 1 /\
           failed.f_state <> state
       | _ -> False)
  =
  plan_future_receive_is_bounded state target;
  advance_receive_success_shape state;
  advance_receive_preserves_validity state;
  let advanced = advance_receive state in
  match advanced.f_sequence, advanced.f_slot with
  | Core_models.Option.Option_Some sequence,
    Core_models.Option.Option_Some slot ->
      finish_receive_failure_retains_key advanced.f_state sequence slot
  | _ -> ()

/// A retained receive key can be retried successfully exactly once.  The retry
/// consumes the target, and another use of the same sequence/slot pair is a
/// state-neutral replay rejection.
let failed_receive_retry_consumes_once
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      (let failed = finish_receive state target slot false in
       let retry_plan = plan_receive_until failed.f_state target in
       let retried = finish_receive failed.f_state target slot true in
       let replay = finish_receive retried.f_state target slot true in
       failed.f_disposition == ReceiveDisposition_Retained /\
       failed.f_state == state /\
       cache_slot failed.f_state.f_receive_cache target slot /\
       retry_plan.f_sequence == Core_models.Option.Option_Some target /\
       retry_plan.f_derivations == mk_u64 0 /\
       retried.f_disposition == ReceiveDisposition_Consumed /\
       ~(cache_has retried.f_state.f_receive_cache target) /\
       replay.f_disposition == ReceiveDisposition_Missing /\
       replay.f_state == retried.f_state)
  =
  finish_receive_failure_retains_key state target slot;
  plan_old_receive_is_zero_cost state target;
  finish_receive_success_shape state target slot;
  finish_receive_consumes_target state target slot;
  finish_receive_replay_is_rejected state target slot

/// Filling the final free cache slot through an admitted future receive and
/// then failing authentication retains a full cache.  The immediately next
/// future sequence is consequently rejected by planning without any further
/// ratchet transition.
let failed_receive_fills_cache_and_rejects_next_future
    (state:t_RatchetState {
       valid_state state /\ cache_len state.f_receive_cache == 49 })
    (target:u64 {
       v target == v state.f_receive_sequence + 1 })
    (next_target:u64 {
       v next_target == v target + 1 })
  : Lemma
      (let advanced = advance_receive state in
       match advanced.f_sequence, advanced.f_slot with
       | Core_models.Option.Option_Some sequence,
         Core_models.Option.Option_Some slot ->
           let failed = finish_receive advanced.f_state sequence slot false in
           let next_plan = plan_receive_until failed.f_state next_target in
           sequence == target /\
           failed.f_disposition == ReceiveDisposition_Retained /\
           failed.f_state == advanced.f_state /\
           cache_slot failed.f_state.f_receive_cache target slot /\
           cache_len failed.f_state.f_receive_cache == 50 /\
           next_plan.f_sequence == Core_models.Option.Option_None /\
           next_plan.f_derivations == mk_u64 0
       | _ -> False)
  =
  admitted_receive_failure_retains_advanced_state state target;
  advance_receive_preserves_validity state;
  let advanced = advance_receive state in
  match advanced.f_sequence, advanced.f_slot with
  | Core_models.Option.Option_Some sequence,
    Core_models.Option.Option_Some slot ->
      finish_receive_failure_retains_key advanced.f_state sequence slot;
      let failed = finish_receive advanced.f_state sequence slot false in
      plan_receive_rejects_capacity_overflow failed.f_state next_target
  | _ -> ()

/// Consuming any present key from a full valid cache frees exactly one slot.
/// The immediately next future sequence is therefore admitted with one
/// derivation; this is the control-state justification for refilling the slot
/// exercised by the finite ProVerif trace.
let successful_receive_releases_capacity_for_next_future
    (state:t_RatchetState {
       valid_state state /\ cache_len state.f_receive_cache == 50 })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
    (next_target:u64 {
       v next_target == v state.f_receive_sequence + 1 })
  : Lemma
      (let consumed = (finish_receive state target slot true).f_state in
       cache_len consumed.f_receive_cache == 49 /\
       consumed.f_receive_sequence == state.f_receive_sequence /\
       (plan_receive_until consumed next_target).f_sequence ==
         Core_models.Option.Option_Some next_target /\
       (plan_receive_until consumed next_target).f_derivations == mk_u64 1)
  =
  finish_receive_success_shape state target slot;
  let consumed = (finish_receive state target slot true).f_state in
  plan_future_receive_is_bounded consumed next_target

/// A successful, ordered restoration append preserves both the ratchet
/// invariant and the builder's strictly-new upper bound.  Rejection returns no
/// state and therefore cannot introduce an invalid one.
let restore_receive_key_preserves_validity
    (restore:t_RatchetRestore { valid_restore restore })
    (sequence:u64)
  : Lemma
      (match restore_receive_key restore sequence with
       | Core_models.Option.Option_Some restored -> valid_restore restored
       | Core_models.Option.Option_None -> True)
  = ()

let finish_restore_is_valid
    (restore:t_RatchetRestore { valid_restore restore })
  : Lemma (valid_state (finish_restore restore))
  = ()

/// A mismatching peer identifier is a pointwise frame rule: every component is
/// returned unchanged for any send or receive replacement.
let replace_ratchet_for_other_peer_is_neutral
    (requested_peer:u64)
    (peer:t_PeerRatchetState { requested_peer <> peer.f_peer_id })
    (replacement:t_RatchetState)
  : Lemma (replace_ratchet_for_peer requested_peer peer replacement == peer)
  = ()

let replace_ratchet_for_selected_peer
    (peer:t_PeerRatchetState)
    (replacement:t_RatchetState)
  : Lemma
      ((replace_ratchet_for_peer peer.f_peer_id peer replacement).f_peer_id ==
         peer.f_peer_id /\
       (replace_ratchet_for_peer peer.f_peer_id peer replacement).f_ratchet ==
         replacement)
  = ()

/// The concrete send wrapper also returns no capability on peer mismatch.
let advance_send_for_other_peer_is_neutral
    (requested_peer:u64)
    (peer:t_PeerRatchetState { requested_peer <> peer.f_peer_id })
  : Lemma
      ((advance_send_for_peer requested_peer peer).f_peer == peer /\
       (advance_send_for_peer requested_peer peer).f_sequence ==
         Core_models.Option.Option_None /\
       not (advance_send_for_peer requested_peer peer).f_key.f_available)
  = ()

let advance_send_for_selected_peer_matches
    (peer:t_PeerRatchetState)
  : Lemma
      ((advance_send_for_peer peer.f_peer_id peer).f_peer.f_peer_id == peer.f_peer_id /\
       (advance_send_for_peer peer.f_peer_id peer).f_peer.f_ratchet ==
         (advance_send peer.f_ratchet).f_state /\
       (advance_send_for_peer peer.f_peer_id peer).f_sequence ==
         (advance_send peer.f_ratchet).f_sequence)
  = ()
