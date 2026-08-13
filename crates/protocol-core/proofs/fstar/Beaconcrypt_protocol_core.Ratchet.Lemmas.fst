/// SPDX-License-Identifier: 0BSD
module Beaconcrypt_protocol_core.Ratchet.Lemmas

open Rust_primitives.Integers
open Rust_primitives.Arrays
open Beaconcrypt_protocol_core.Ratchet

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

/// The extracted splitter assigns every HKDF byte to exactly the production
/// key, next-chain, or nonce field, with no adapter-owned offset arithmetic.
let ratchet_kdf_output_split_is_exact
    (output:t_Array u8 (mk_usize 76))
  : Lemma
      (let split = split_ratchet_kdf_output output in
       Seq.length split.f_key.f_bytes == 32 /\
       Seq.length split.f_next_chain.f_bytes == 32 /\
       Seq.length split.f_nonce.f_bytes == 12 /\
       (forall (i:nat{i < 32}).
          Seq.index split.f_key.f_bytes i == Seq.index output i) /\
       (forall (i:nat{i < 32}).
          Seq.index split.f_next_chain.f_bytes i == Seq.index output (i + 32)) /\
       (forall (i:nat{i < 12}).
          Seq.index split.f_nonce.f_bytes i == Seq.index output (i + 64)))
  = ()

/// Every symmetric-ratchet primitive invocation is a core-owned request containing the exact supplied input and the fixed protocol domain-separation label.
let symmetric_ratchet_kdf_request_is_exact
    (input:t_Array u8 (mk_usize 32))
  : Lemma
      (let request = impl_SymmetricRatchetKdfRequest__new input in
       request.f_input == input /\
       request.f_info == v_SYM_RATCHET_INFO)
  = ()

/// The extracted concrete adapter applies the opaque primitive to a core-owned request for the exact old chain and fixed label, then returns fixed-width fields with the proved partition.
let ratchet_step_uses_exact_chain_and_partition
    (old_chain:t_RatchetChain)
    (kdf:t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76))
  : Lemma
      (let request = impl_SymmetricRatchetKdfRequest__new old_chain.f_bytes in
       let output = kdf request in
       let stepped = derive_ratchet_step old_chain kdf in
       request.f_input == old_chain.f_bytes /\
       request.f_info == v_SYM_RATCHET_INFO /\
       (forall (i:nat{i < 32}).
          Seq.index stepped.f_material.f_key.f_bytes i ==
            Seq.index output i) /\
       (forall (i:nat{i < 32}).
          Seq.index stepped.f_chain.f_bytes i ==
            Seq.index output (i + 32)) /\
       (forall (i:nat{i < 12}).
          Seq.index stepped.f_material.f_nonce.f_bytes i ==
            Seq.index output (i + 64)))
  = symmetric_ratchet_kdf_request_is_exact old_chain.f_bytes

/// The production-specialized step applies the executor sealed into the old chain and carries that identical executor into the next chain.
let concrete_ratchet_step_preserves_executor
    (old_chain:t_ConcreteRatchetChain)
  : Lemma
      ((concrete_ratchet_step old_chain).f_chain.f_kdf == old_chain.f_kdf)
  = ()

let ratchet_chain_bytes_extensionality
    (left right:t_RatchetChain)
  : Lemma
      (requires (left.f_bytes == right.f_bytes))
      (ensures (left == right))
  = ()

let concrete_ratchet_chain_extensionality
    (left right:t_ConcreteRatchetChain)
  : Lemma
      (requires
        (left.f_chain == right.f_chain /\
         left.f_kdf == right.f_kdf))
      (ensures (left == right))
  = ()

/// Fixed-width integer values are determined by their mathematical view.
let u64_value_extensionality
    (left right:u64)
  : Lemma
      (requires (v left == v right))
      (ensures (left == right))
  = match left, right with
    | Rust_primitives.Integers.MkInt _,
      Rust_primitives.Integers.MkInt _ -> ()

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

/// Any successful bounded lookup names an active matching slot inside the part of the cache traversed by that lookup.
let rec lookup_receive_key_from_sound
    (state:t_RatchetState)
    (sequence:u64)
    (slot remaining:u8)
  : Lemma
      (ensures (match lookup_receive_key_from state sequence slot remaining with
       | Core_models.Option.Option_Some found ->
           v slot <= v found /\
           v found < v slot + v remaining /\
           cache_slot state.f_receive_cache sequence found
       | Core_models.Option.Option_None -> True))
      (decreases (v remaining))
  =
  if remaining = mk_u8 0 then ()
  else if v slot >= 50 then ()
  else if v slot >= cache_len state.f_receive_cache then ()
  else if cache_entry state.f_receive_cache (v slot) = sequence then ()
  else
    lookup_receive_key_from_sound
      state sequence (slot +! mk_u8 1) (remaining -! mk_u8 1)

/// A bounded lookup that returns `None` excludes the requested sequence from every active slot in the traversed range.
let rec lookup_receive_key_from_none_excludes_range
    (state:t_RatchetState)
    (sequence:u64)
    (slot remaining:u8)
  : Lemma
      (ensures
        (lookup_receive_key_from state sequence slot remaining ==
           Core_models.Option.Option_None ==>
         forall (i:nat{i < 50}).
           v slot <= i /\
           i < cache_len state.f_receive_cache /\
           i < v slot + v remaining ==>
             cache_entry state.f_receive_cache i <> sequence))
      (decreases (v remaining))
  =
  if remaining = mk_u8 0 then ()
  else if v slot >= 50 then ()
  else if v slot >= cache_len state.f_receive_cache then ()
  else if cache_entry state.f_receive_cache (v slot) = sequence then ()
  else
    lookup_receive_key_from_none_excludes_range
      state sequence (slot +! mk_u8 1) (remaining -! mk_u8 1)

/// Public lookup soundness: every returned slot is active and stores exactly the requested logical sequence.
let lookup_receive_key_sound
    (state:t_RatchetState { valid_state state })
    (sequence:u64)
  : Lemma
      (match lookup_receive_key state sequence with
       | Core_models.Option.Option_Some slot ->
           cache_slot state.f_receive_cache sequence slot
       | Core_models.Option.Option_None -> True)
  = lookup_receive_key_from_sound state sequence (mk_u8 0) (mk_u8 50)

/// Public lookup completeness in its negative form. `None` is authoritative: no active logical receive capability has the requested sequence.
let lookup_receive_key_none_is_absent
    (state:t_RatchetState { valid_state state })
    (sequence:u64)
  : Lemma
      (lookup_receive_key state sequence == Core_models.Option.Option_None ==>
       ~(cache_has state.f_receive_cache sequence))
  = lookup_receive_key_from_none_excludes_range
      state sequence (mk_u8 0) (mk_u8 50)

/// Contrapositive completeness used by adapters and later correspondence proofs: every active logical sequence is found by public lookup.
let lookup_receive_key_is_complete
    (state:t_RatchetState { valid_state state })
    (sequence:u64)
  : Lemma
      (cache_has state.f_receive_cache sequence ==>
       lookup_receive_key state sequence <> Core_models.Option.Option_None)
  = lookup_receive_key_none_is_absent state sequence

/// Valid-cache uniqueness strengthens soundness to the exact unique active slot characterized by the lookup result.
let lookup_receive_key_returns_unique_slot
    (state:t_RatchetState { valid_state state })
    (sequence:u64)
  : Lemma
      (match lookup_receive_key state sequence with
       | Core_models.Option.Option_Some slot ->
           cache_slot state.f_receive_cache sequence slot /\
           (forall (other:u8).
              cache_slot state.f_receive_cache sequence other ==> other == slot)
       | Core_models.Option.Option_None ->
           ~(cache_has state.f_receive_cache sequence))
  =
  lookup_receive_key_sound state sequence;
  lookup_receive_key_none_is_absent state sequence

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

/// An unavailable capability value cannot be consumed a second time.
/// This is token-local: it does not prove that an available predecessor was not copied, that only one live state lineage exists, or that persistence cannot roll back.
let finish_send_rejects_reuse
    (key:t_SendKey { not key.f_available })
  : Lemma
      (not (finish_send key).f_consumed /\
       (finish_send key).f_key == key)
  = ()

/// Reapplying finish to this returned unavailable value is rejected.
/// Like the preceding lemma, this is not a trace-level ownership or no-rollback theorem.
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

/// Every receive plan exposes a derivation count that fits the u8 executor bound.
let plan_receive_derivations_are_bounded
    (state:t_RatchetState)
    (target:u64)
  : Lemma
      (v (plan_receive_until state target).f_derivations <= 50)
  =
  let plan = plan_receive_until state target in
  if v target > v state.f_receive_sequence then
    let future_target:(x:u64 { v x > v state.f_receive_sequence }) = target in
    plan_future_receive_is_bounded state future_target;
    match plan.f_sequence with
    | Core_models.Option.Option_Some _ -> ()
    | Core_models.Option.Option_None -> ()
  else
    let old_target:(x:u64 { v x <= v state.f_receive_sequence }) = target in
    plan_old_receive_is_zero_cost state old_target

/// A receive plan fixes its returned target and characterizes the zero-versus-positive derivation count independently of concrete chain types.
let plan_receive_shape
    (state:t_RatchetState)
    (target:u64)
  : Lemma
      (let plan = plan_receive_until state target in
       v plan.f_derivations <= 50 /\
       (match plan.f_sequence with
        | Core_models.Option.Option_Some planned_target ->
            planned_target == target /\
            (v target > v state.f_receive_sequence ==>
              v plan.f_derivations > 0) /\
            (v target <= v state.f_receive_sequence ==>
              plan.f_derivations == mk_u64 0)
        | Core_models.Option.Option_None ->
            plan.f_derivations == mk_u64 0))
  =
  let plan = plan_receive_until state target in
  plan_receive_derivations_are_bounded state target;
  if v target > v state.f_receive_sequence then
    let future_target:(x:u64 { v x > v state.f_receive_sequence }) = target in
    plan_future_receive_is_bounded state future_target;
    match plan.f_sequence with
    | Core_models.Option.Option_Some _ -> ()
    | Core_models.Option.Option_None -> ()
  else
    let old_target:(x:u64 { v x <= v state.f_receive_sequence }) = target in
    plan_old_receive_is_zero_cost state old_target

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

/// The compatibility wrapper is exactly the state/disposition projection of the detailed operation for every input and outcome.
let finish_receive_wrapper_matches_detailed
    (state:t_RatchetState)
    (target:u64)
    (slot:u8)
    (authenticated:bool)
  : Lemma
      ((finish_receive state target slot authenticated).f_state ==
         (finish_receive_with_removal state target slot authenticated).f_state /\
       (finish_receive state target slot authenticated).f_disposition ==
         (finish_receive_with_removal state target slot authenticated).f_disposition)
  = ()

/// Every detailed `Missing` result is state-neutral and carries no removal plan.
let finish_receive_with_removal_missing_result_is_neutral
    (state:t_RatchetState)
    (target:u64)
    (slot:u8)
    (authenticated:bool)
  : Lemma
      (let finished = finish_receive_with_removal state target slot authenticated in
       finished.f_disposition == ReceiveDisposition_Missing ==>
         finished.f_removal == Core_models.Option.Option_None /\
         finished.f_state == state)
  = ()

/// Every detailed `Retained` result is state-neutral and carries no removal plan.
let finish_receive_with_removal_retained_result_is_neutral
    (state:t_RatchetState)
    (target:u64)
    (slot:u8)
    (authenticated:bool)
  : Lemma
      (let finished = finish_receive_with_removal state target slot authenticated in
       finished.f_disposition == ReceiveDisposition_Retained ==>
         finished.f_removal == Core_models.Option.Option_None /\
         finished.f_state == state)
  = ()

/// A wrong slot/sequence pair returns no removal plan and leaves the complete ratchet state unchanged.
let finish_receive_with_removal_missing_is_neutral
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { ~(cache_slot state.f_receive_cache target slot) })
    (authenticated:bool)
  : Lemma
      ((finish_receive_with_removal state target slot authenticated).f_disposition ==
         ReceiveDisposition_Missing /\
       (finish_receive_with_removal state target slot authenticated).f_state == state /\
       (finish_receive_with_removal state target slot authenticated).f_removal ==
         Core_models.Option.Option_None)
  = ()

/// Authentication failure for a matching candidate returns no removal plan, retains all state, and leaves that exact candidate in the same slot.
let finish_receive_with_removal_failure_retains_key
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      ((finish_receive_with_removal state target slot false).f_disposition ==
         ReceiveDisposition_Retained /\
       (finish_receive_with_removal state target slot false).f_state == state /\
       (finish_receive_with_removal state target slot false).f_removal ==
         Core_models.Option.Option_None /\
       cache_slot
         (finish_receive_with_removal state target slot false).f_state.f_receive_cache
         target
         slot)
  = ()

/// Successful detailed completion reports the exact old target/last slots, decrements the logical length once, and exposes the logical move mirrored by the concrete fixed array.
let finish_receive_with_removal_success_shape
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      (let finished = finish_receive_with_removal state target slot true in
       finished.f_disposition == ReceiveDisposition_Consumed /\
       (match finished.f_removal with
        | Core_models.Option.Option_Some removal ->
            removal.f_target_slot == slot /\
            v removal.f_last_slot + 1 == cache_len state.f_receive_cache /\
            cache_len finished.f_state.f_receive_cache + 1 ==
              cache_len state.f_receive_cache /\
            finished.f_state.f_send_sequence == state.f_send_sequence /\
            finished.f_state.f_receive_sequence == state.f_receive_sequence /\
            (removal.f_target_slot <> removal.f_last_slot ==>
             cache_entry finished.f_state.f_receive_cache (v removal.f_target_slot) ==
               cache_entry state.f_receive_cache (v removal.f_last_slot))
        | Core_models.Option.Option_None -> False))
  = ()

/// The detailed transition preserves the same logical validity theorem as its compatibility projection.
let finish_receive_with_removal_preserves_validity
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8)
    (authenticated:bool)
  : Lemma
      (valid_state
        (finish_receive_with_removal state target slot authenticated).f_state)
  =
  finish_receive_preserves_validity state target slot authenticated;
  finish_receive_wrapper_matches_detailed state target slot authenticated

/// Detailed successful completion removes the target capability itself.
let finish_receive_with_removal_consumes_target
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
  : Lemma
      (~(cache_has
        (finish_receive_with_removal state target slot true).f_state.f_receive_cache
        target))
  =
  finish_receive_consumes_target state target slot;
  finish_receive_wrapper_matches_detailed state target slot true

/// Every non-target capability survives detailed swap-removal.
let finish_receive_with_removal_preserves_other_key
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
    (other:u64 {
       other <> target /\ cache_has state.f_receive_cache other })
  : Lemma
      (cache_has
        (finish_receive_with_removal state target slot true).f_state.f_receive_cache
        other)
  =
  finish_receive_preserves_other_key state target slot other;
  finish_receive_wrapper_matches_detailed state target slot true

/// Preservation is exact: the surviving non-target sequence occupies one unique active slot in the detailed result.
let finish_receive_with_removal_preserves_other_key_exactly_once
    (state:t_RatchetState { valid_state state })
    (target:u64)
    (slot:u8 { cache_slot state.f_receive_cache target slot })
    (other:u64 {
       other <> target /\ cache_has state.f_receive_cache other })
  : Lemma
      (let cache =
         (finish_receive_with_removal state target slot true).f_state.f_receive_cache in
       cache_has cache other /\
       (forall (i:nat{i < 50}) (j:nat{j < 50}).
          i < cache_len cache /\ j < cache_len cache /\
          cache_entry cache i == other /\ cache_entry cache j == other ==>
            i == j))
  =
  finish_receive_with_removal_preserves_other_key state target slot other;
  finish_receive_with_removal_preserves_validity state target slot true

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

/// The compatibility restoration API accepts and rejects exactly the same inputs as the slot-returning operation and projects its restore state.
let restore_receive_key_wrapper_matches_slot
    (restore:t_RatchetRestore)
    (sequence:u64)
  : Lemma
      (match restore_receive_key_with_slot restore sequence,
             restore_receive_key restore sequence with
       | Core_models.Option.Option_Some step,
         Core_models.Option.Option_Some restored -> restored == step.f_restore
       | Core_models.Option.Option_None,
         Core_models.Option.Option_None -> True
       | _ -> False)
  = ()

/// Every successful checked restoration returns the exact append slot, grows the cache once, and places the restored sequence in that returned slot.
let restore_receive_key_with_slot_success_shape
    (restore:t_RatchetRestore { valid_restore restore })
    (sequence:u64)
  : Lemma
      (match restore_receive_key_with_slot restore sequence with
       | Core_models.Option.Option_Some step ->
           v step.f_slot == cache_len restore.f_state.f_receive_cache /\
           cache_len step.f_restore.f_state.f_receive_cache ==
             cache_len restore.f_state.f_receive_cache + 1 /\
           cache_slot step.f_restore.f_state.f_receive_cache sequence step.f_slot
       | Core_models.Option.Option_None -> True)
  = ()

/// The detailed restoration result preserves the builder invariant; rejected inputs return no state.
let restore_receive_key_with_slot_preserves_validity
    (restore:t_RatchetRestore { valid_restore restore })
    (sequence:u64)
  : Lemma
      (match restore_receive_key_with_slot restore sequence with
       | Core_models.Option.Option_Some step -> valid_restore step.f_restore
       | Core_models.Option.Option_None -> True)
  =
  restore_receive_key_preserves_validity restore sequence;
  restore_receive_key_wrapper_matches_slot restore sequence

let finish_restore_is_valid
    (restore:t_RatchetRestore { valid_restore restore })
  : Lemma (valid_state (finish_restore restore))
  = ()

/// Logical view of one sealed receive-key slot in the refined fixed array.
let refined_slot_value
    (#v_Material:Type0)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (i:nat{i < 50})
  : Core_models.Option.t_Option (t_CachedReceiveKey v_Material) =
  Seq.index slots i

let refined_slot_value_is_index
    (#v_Material:Type0)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (i:nat{i < 50})
  : Lemma
      (refined_slot_value slots i == Seq.index slots i)
  = ()

/// Every active slot carries the exact logical sequence beside its material,
/// and every inactive slot is empty.
let material_slots_match
    (#v_Material:Type0)
    (cache:t_SequenceCache)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
  : prop =
  forall (i:nat{i < 50}).
    match refined_slot_value slots i with
    | Core_models.Option.Option_Some cached ->
        i < cache_len cache /\ cached.f_sequence == cache_entry cache i
    | Core_models.Option.Option_None -> cache_len cache <= i

/// Proof-only structural representation of a generic list containing exactly `n` empty material slots.
let rec none_material_list
    (#v_Material:Type0)
    (n:nat)
  : Tot
      (xs:list
        (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) {
         List.Tot.length xs == n })
      (decreases n)
  =
  if n = 0 then []
  else
    (Core_models.Option.Option_None <:
       Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) ::
      none_material_list #v_Material (n - 1)

let rec none_material_list_index
    (#v_Material:Type0)
    (n:nat)
    (i:nat{i < n})
  : Lemma
      (ensures
        (List.Tot.index (none_material_list #v_Material n) i ==
          Core_models.Option.Option_None))
      (decreases n)
  =
  if n = 0 then ()
  else if i = 0 then ()
  else none_material_list_index #v_Material (n - 1) (i - 1)

/// Each concrete position in the fixed source-level empty array is None.
let empty_material_slot_is_none
    (#v_Material:Type0)
    (i:nat{i < 50})
  : Lemma
      (refined_slot_value (empty_material_slots #v_Material ()) i ==
        Core_models.Option.Option_None)
  =
  let xs = none_material_list #v_Material 50 in
  let slots = empty_material_slots #v_Material () in
  FStar.Pervasives.assert_norm (slots == Seq.seq_of_list xs);
  FStar.Seq.Base.lemma_eq_refl slots (Seq.seq_of_list xs);
  if i = 0 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (0 < Seq.length slots);
     assert (0 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 0 == Seq.index (Seq.seq_of_list xs) 0);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 0;
     none_material_list_index #v_Material 50 0;
     refined_slot_value_is_index slots 0;
     assert
       (refined_slot_value slots 0 == Core_models.Option.Option_None);
     ())
  else if i = 1 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (1 < Seq.length slots);
     assert (1 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 1 == Seq.index (Seq.seq_of_list xs) 1);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 1;
     none_material_list_index #v_Material 50 1;
     refined_slot_value_is_index slots 1;
     assert
       (refined_slot_value slots 1 == Core_models.Option.Option_None);
     ())
  else if i = 2 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (2 < Seq.length slots);
     assert (2 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 2 == Seq.index (Seq.seq_of_list xs) 2);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 2;
     none_material_list_index #v_Material 50 2;
     refined_slot_value_is_index slots 2;
     assert
       (refined_slot_value slots 2 == Core_models.Option.Option_None);
     ())
  else if i = 3 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (3 < Seq.length slots);
     assert (3 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 3 == Seq.index (Seq.seq_of_list xs) 3);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 3;
     none_material_list_index #v_Material 50 3;
     refined_slot_value_is_index slots 3;
     assert
       (refined_slot_value slots 3 == Core_models.Option.Option_None);
     ())
  else if i = 4 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (4 < Seq.length slots);
     assert (4 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 4 == Seq.index (Seq.seq_of_list xs) 4);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 4;
     none_material_list_index #v_Material 50 4;
     refined_slot_value_is_index slots 4;
     assert
       (refined_slot_value slots 4 == Core_models.Option.Option_None);
     ())
  else if i = 5 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (5 < Seq.length slots);
     assert (5 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 5 == Seq.index (Seq.seq_of_list xs) 5);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 5;
     none_material_list_index #v_Material 50 5;
     refined_slot_value_is_index slots 5;
     assert
       (refined_slot_value slots 5 == Core_models.Option.Option_None);
     ())
  else if i = 6 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (6 < Seq.length slots);
     assert (6 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 6 == Seq.index (Seq.seq_of_list xs) 6);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 6;
     none_material_list_index #v_Material 50 6;
     refined_slot_value_is_index slots 6;
     assert
       (refined_slot_value slots 6 == Core_models.Option.Option_None);
     ())
  else if i = 7 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (7 < Seq.length slots);
     assert (7 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 7 == Seq.index (Seq.seq_of_list xs) 7);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 7;
     none_material_list_index #v_Material 50 7;
     refined_slot_value_is_index slots 7;
     assert
       (refined_slot_value slots 7 == Core_models.Option.Option_None);
     ())
  else if i = 8 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (8 < Seq.length slots);
     assert (8 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 8 == Seq.index (Seq.seq_of_list xs) 8);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 8;
     none_material_list_index #v_Material 50 8;
     refined_slot_value_is_index slots 8;
     assert
       (refined_slot_value slots 8 == Core_models.Option.Option_None);
     ())
  else if i = 9 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (9 < Seq.length slots);
     assert (9 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 9 == Seq.index (Seq.seq_of_list xs) 9);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 9;
     none_material_list_index #v_Material 50 9;
     refined_slot_value_is_index slots 9;
     assert
       (refined_slot_value slots 9 == Core_models.Option.Option_None);
     ())
  else if i = 10 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (10 < Seq.length slots);
     assert (10 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 10 == Seq.index (Seq.seq_of_list xs) 10);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 10;
     none_material_list_index #v_Material 50 10;
     refined_slot_value_is_index slots 10;
     assert
       (refined_slot_value slots 10 == Core_models.Option.Option_None);
     ())
  else if i = 11 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (11 < Seq.length slots);
     assert (11 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 11 == Seq.index (Seq.seq_of_list xs) 11);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 11;
     none_material_list_index #v_Material 50 11;
     refined_slot_value_is_index slots 11;
     assert
       (refined_slot_value slots 11 == Core_models.Option.Option_None);
     ())
  else if i = 12 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (12 < Seq.length slots);
     assert (12 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 12 == Seq.index (Seq.seq_of_list xs) 12);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 12;
     none_material_list_index #v_Material 50 12;
     refined_slot_value_is_index slots 12;
     assert
       (refined_slot_value slots 12 == Core_models.Option.Option_None);
     ())
  else if i = 13 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (13 < Seq.length slots);
     assert (13 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 13 == Seq.index (Seq.seq_of_list xs) 13);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 13;
     none_material_list_index #v_Material 50 13;
     refined_slot_value_is_index slots 13;
     assert
       (refined_slot_value slots 13 == Core_models.Option.Option_None);
     ())
  else if i = 14 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (14 < Seq.length slots);
     assert (14 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 14 == Seq.index (Seq.seq_of_list xs) 14);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 14;
     none_material_list_index #v_Material 50 14;
     refined_slot_value_is_index slots 14;
     assert
       (refined_slot_value slots 14 == Core_models.Option.Option_None);
     ())
  else if i = 15 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (15 < Seq.length slots);
     assert (15 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 15 == Seq.index (Seq.seq_of_list xs) 15);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 15;
     none_material_list_index #v_Material 50 15;
     refined_slot_value_is_index slots 15;
     assert
       (refined_slot_value slots 15 == Core_models.Option.Option_None);
     ())
  else if i = 16 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (16 < Seq.length slots);
     assert (16 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 16 == Seq.index (Seq.seq_of_list xs) 16);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 16;
     none_material_list_index #v_Material 50 16;
     refined_slot_value_is_index slots 16;
     assert
       (refined_slot_value slots 16 == Core_models.Option.Option_None);
     ())
  else if i = 17 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (17 < Seq.length slots);
     assert (17 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 17 == Seq.index (Seq.seq_of_list xs) 17);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 17;
     none_material_list_index #v_Material 50 17;
     refined_slot_value_is_index slots 17;
     assert
       (refined_slot_value slots 17 == Core_models.Option.Option_None);
     ())
  else if i = 18 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (18 < Seq.length slots);
     assert (18 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 18 == Seq.index (Seq.seq_of_list xs) 18);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 18;
     none_material_list_index #v_Material 50 18;
     refined_slot_value_is_index slots 18;
     assert
       (refined_slot_value slots 18 == Core_models.Option.Option_None);
     ())
  else if i = 19 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (19 < Seq.length slots);
     assert (19 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 19 == Seq.index (Seq.seq_of_list xs) 19);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 19;
     none_material_list_index #v_Material 50 19;
     refined_slot_value_is_index slots 19;
     assert
       (refined_slot_value slots 19 == Core_models.Option.Option_None);
     ())
  else if i = 20 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (20 < Seq.length slots);
     assert (20 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 20 == Seq.index (Seq.seq_of_list xs) 20);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 20;
     none_material_list_index #v_Material 50 20;
     refined_slot_value_is_index slots 20;
     assert
       (refined_slot_value slots 20 == Core_models.Option.Option_None);
     ())
  else if i = 21 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (21 < Seq.length slots);
     assert (21 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 21 == Seq.index (Seq.seq_of_list xs) 21);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 21;
     none_material_list_index #v_Material 50 21;
     refined_slot_value_is_index slots 21;
     assert
       (refined_slot_value slots 21 == Core_models.Option.Option_None);
     ())
  else if i = 22 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (22 < Seq.length slots);
     assert (22 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 22 == Seq.index (Seq.seq_of_list xs) 22);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 22;
     none_material_list_index #v_Material 50 22;
     refined_slot_value_is_index slots 22;
     assert
       (refined_slot_value slots 22 == Core_models.Option.Option_None);
     ())
  else if i = 23 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (23 < Seq.length slots);
     assert (23 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 23 == Seq.index (Seq.seq_of_list xs) 23);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 23;
     none_material_list_index #v_Material 50 23;
     refined_slot_value_is_index slots 23;
     assert
       (refined_slot_value slots 23 == Core_models.Option.Option_None);
     ())
  else if i = 24 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (24 < Seq.length slots);
     assert (24 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 24 == Seq.index (Seq.seq_of_list xs) 24);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 24;
     none_material_list_index #v_Material 50 24;
     refined_slot_value_is_index slots 24;
     assert
       (refined_slot_value slots 24 == Core_models.Option.Option_None);
     ())
  else if i = 25 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (25 < Seq.length slots);
     assert (25 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 25 == Seq.index (Seq.seq_of_list xs) 25);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 25;
     none_material_list_index #v_Material 50 25;
     refined_slot_value_is_index slots 25;
     assert
       (refined_slot_value slots 25 == Core_models.Option.Option_None);
     ())
  else if i = 26 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (26 < Seq.length slots);
     assert (26 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 26 == Seq.index (Seq.seq_of_list xs) 26);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 26;
     none_material_list_index #v_Material 50 26;
     refined_slot_value_is_index slots 26;
     assert
       (refined_slot_value slots 26 == Core_models.Option.Option_None);
     ())
  else if i = 27 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (27 < Seq.length slots);
     assert (27 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 27 == Seq.index (Seq.seq_of_list xs) 27);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 27;
     none_material_list_index #v_Material 50 27;
     refined_slot_value_is_index slots 27;
     assert
       (refined_slot_value slots 27 == Core_models.Option.Option_None);
     ())
  else if i = 28 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (28 < Seq.length slots);
     assert (28 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 28 == Seq.index (Seq.seq_of_list xs) 28);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 28;
     none_material_list_index #v_Material 50 28;
     refined_slot_value_is_index slots 28;
     assert
       (refined_slot_value slots 28 == Core_models.Option.Option_None);
     ())
  else if i = 29 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (29 < Seq.length slots);
     assert (29 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 29 == Seq.index (Seq.seq_of_list xs) 29);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 29;
     none_material_list_index #v_Material 50 29;
     refined_slot_value_is_index slots 29;
     assert
       (refined_slot_value slots 29 == Core_models.Option.Option_None);
     ())
  else if i = 30 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (30 < Seq.length slots);
     assert (30 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 30 == Seq.index (Seq.seq_of_list xs) 30);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 30;
     none_material_list_index #v_Material 50 30;
     refined_slot_value_is_index slots 30;
     assert
       (refined_slot_value slots 30 == Core_models.Option.Option_None);
     ())
  else if i = 31 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (31 < Seq.length slots);
     assert (31 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 31 == Seq.index (Seq.seq_of_list xs) 31);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 31;
     none_material_list_index #v_Material 50 31;
     refined_slot_value_is_index slots 31;
     assert
       (refined_slot_value slots 31 == Core_models.Option.Option_None);
     ())
  else if i = 32 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (32 < Seq.length slots);
     assert (32 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 32 == Seq.index (Seq.seq_of_list xs) 32);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 32;
     none_material_list_index #v_Material 50 32;
     refined_slot_value_is_index slots 32;
     assert
       (refined_slot_value slots 32 == Core_models.Option.Option_None);
     ())
  else if i = 33 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (33 < Seq.length slots);
     assert (33 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 33 == Seq.index (Seq.seq_of_list xs) 33);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 33;
     none_material_list_index #v_Material 50 33;
     refined_slot_value_is_index slots 33;
     assert
       (refined_slot_value slots 33 == Core_models.Option.Option_None);
     ())
  else if i = 34 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (34 < Seq.length slots);
     assert (34 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 34 == Seq.index (Seq.seq_of_list xs) 34);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 34;
     none_material_list_index #v_Material 50 34;
     refined_slot_value_is_index slots 34;
     assert
       (refined_slot_value slots 34 == Core_models.Option.Option_None);
     ())
  else if i = 35 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (35 < Seq.length slots);
     assert (35 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 35 == Seq.index (Seq.seq_of_list xs) 35);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 35;
     none_material_list_index #v_Material 50 35;
     refined_slot_value_is_index slots 35;
     assert
       (refined_slot_value slots 35 == Core_models.Option.Option_None);
     ())
  else if i = 36 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (36 < Seq.length slots);
     assert (36 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 36 == Seq.index (Seq.seq_of_list xs) 36);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 36;
     none_material_list_index #v_Material 50 36;
     refined_slot_value_is_index slots 36;
     assert
       (refined_slot_value slots 36 == Core_models.Option.Option_None);
     ())
  else if i = 37 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (37 < Seq.length slots);
     assert (37 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 37 == Seq.index (Seq.seq_of_list xs) 37);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 37;
     none_material_list_index #v_Material 50 37;
     refined_slot_value_is_index slots 37;
     assert
       (refined_slot_value slots 37 == Core_models.Option.Option_None);
     ())
  else if i = 38 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (38 < Seq.length slots);
     assert (38 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 38 == Seq.index (Seq.seq_of_list xs) 38);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 38;
     none_material_list_index #v_Material 50 38;
     refined_slot_value_is_index slots 38;
     assert
       (refined_slot_value slots 38 == Core_models.Option.Option_None);
     ())
  else if i = 39 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (39 < Seq.length slots);
     assert (39 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 39 == Seq.index (Seq.seq_of_list xs) 39);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 39;
     none_material_list_index #v_Material 50 39;
     refined_slot_value_is_index slots 39;
     assert
       (refined_slot_value slots 39 == Core_models.Option.Option_None);
     ())
  else if i = 40 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (40 < Seq.length slots);
     assert (40 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 40 == Seq.index (Seq.seq_of_list xs) 40);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 40;
     none_material_list_index #v_Material 50 40;
     refined_slot_value_is_index slots 40;
     assert
       (refined_slot_value slots 40 == Core_models.Option.Option_None);
     ())
  else if i = 41 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (41 < Seq.length slots);
     assert (41 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 41 == Seq.index (Seq.seq_of_list xs) 41);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 41;
     none_material_list_index #v_Material 50 41;
     refined_slot_value_is_index slots 41;
     assert
       (refined_slot_value slots 41 == Core_models.Option.Option_None);
     ())
  else if i = 42 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (42 < Seq.length slots);
     assert (42 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 42 == Seq.index (Seq.seq_of_list xs) 42);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 42;
     none_material_list_index #v_Material 50 42;
     refined_slot_value_is_index slots 42;
     assert
       (refined_slot_value slots 42 == Core_models.Option.Option_None);
     ())
  else if i = 43 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (43 < Seq.length slots);
     assert (43 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 43 == Seq.index (Seq.seq_of_list xs) 43);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 43;
     none_material_list_index #v_Material 50 43;
     refined_slot_value_is_index slots 43;
     assert
       (refined_slot_value slots 43 == Core_models.Option.Option_None);
     ())
  else if i = 44 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (44 < Seq.length slots);
     assert (44 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 44 == Seq.index (Seq.seq_of_list xs) 44);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 44;
     none_material_list_index #v_Material 50 44;
     refined_slot_value_is_index slots 44;
     assert
       (refined_slot_value slots 44 == Core_models.Option.Option_None);
     ())
  else if i = 45 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (45 < Seq.length slots);
     assert (45 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 45 == Seq.index (Seq.seq_of_list xs) 45);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 45;
     none_material_list_index #v_Material 50 45;
     refined_slot_value_is_index slots 45;
     assert
       (refined_slot_value slots 45 == Core_models.Option.Option_None);
     ())
  else if i = 46 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (46 < Seq.length slots);
     assert (46 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 46 == Seq.index (Seq.seq_of_list xs) 46);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 46;
     none_material_list_index #v_Material 50 46;
     refined_slot_value_is_index slots 46;
     assert
       (refined_slot_value slots 46 == Core_models.Option.Option_None);
     ())
  else if i = 47 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (47 < Seq.length slots);
     assert (47 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 47 == Seq.index (Seq.seq_of_list xs) 47);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 47;
     none_material_list_index #v_Material 50 47;
     refined_slot_value_is_index slots 47;
     assert
       (refined_slot_value slots 47 == Core_models.Option.Option_None);
     ())
  else if i = 48 then
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (48 < Seq.length slots);
     assert (48 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 48 == Seq.index (Seq.seq_of_list xs) 48);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 48;
     none_material_list_index #v_Material 50 48;
     refined_slot_value_is_index slots 48;
     assert
       (refined_slot_value slots 48 == Core_models.Option.Option_None);
     ())
  else
    (assert (FStar.Seq.Base.equal slots (Seq.seq_of_list xs));
     assert (49 < Seq.length slots);
     assert (49 < Seq.length (Seq.seq_of_list xs));
     assert
       (Seq.index slots 49 == Seq.index (Seq.seq_of_list xs) 49);
     FStar.Seq.Properties.lemma_seq_of_list_index xs 49;
     none_material_list_index #v_Material 50 49;
     refined_slot_value_is_index slots 49;
     assert
       (refined_slot_value slots 49 == Core_models.Option.Option_None);
     ())

/// The explicit source-level empty array establishes the material occupancy invariant.
let empty_material_slots_are_none
    (#v_Material:Type0)
  : Lemma
      (forall (i:nat{i < 50}).
         refined_slot_value (empty_material_slots #v_Material ()) i ==
           Core_models.Option.Option_None)
  =
  FStar.Classical.forall_intro
    #(i:nat{i < 50})
    #(fun i ->
        refined_slot_value (empty_material_slots #v_Material ()) i ==
          Core_models.Option.Option_None)
    (empty_material_slot_is_none #v_Material)

/// The refined invariant connects the verified control cache to the concrete fixed material slots.
let valid_refined
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
  : prop =
  valid_state state.f_control /\
  material_slots_match state.f_control.f_receive_cache state.f_receive_slots

/// Canonical result of applying one fixed abstract ratchet step `count` times from an initial directional chain. Unlike the adjacent-state step lemmas, this proof-only function fixes both the origin and callback for the complete lifetime of a state.
let rec chain_after
    (#v_Chain #v_Material:Type0)
    (initial:v_Chain)
    (step:v_Chain -> t_RatchetStep v_Chain v_Material)
    (count:nat)
  : Tot v_Chain (decreases count) =
  if count = 0 then initial
  else
    (step
      (chain_after #v_Chain #v_Material
        initial step (count - 1))).f_chain

/// Canonical material allocated at a logical sequence. Sequence zero is a control sentinel and is excluded by `cached_materials_are_derived`.
let material_at
    (#v_Chain #v_Material:Type0)
    (initial:v_Chain)
    (step:v_Chain -> t_RatchetStep v_Chain v_Material)
    (sequence:nat)
  : v_Material =
  if sequence = 0 then (step initial).f_material
  else
    (step
      (chain_after #v_Chain #v_Material
        initial step (sequence - 1))).f_material

/// Every physically present cached record has material produced by the fixed receive derivation at the sequence sealed into that record.
let cached_materials_are_derived
    (#v_ReceiveChain #v_Material:Type0)
    (initial_receive:v_ReceiveChain)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
  : prop =
  forall (i:nat{i < 50}).
    match refined_slot_value slots i with
    | Core_models.Option.Option_Some cached ->
        v cached.f_sequence > 0 /\
        cached.f_material ==
          material_at #v_ReceiveChain #v_Material
            initial_receive receive_step (v cached.f_sequence)
    | Core_models.Option.Option_None -> True

/// Derivational reachability from fixed initial directional chains under fixed abstract KDF steps. It strengthens `valid_refined`: both live counters name exact KDF iteration counts, and every cached tag names its exact iteration's material rather than merely agreeing with the logical cache.
let reachable
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
  : prop =
  valid_refined state /\
  state.f_send_chain ==
    chain_after #v_SendChain #v_Material
      initial_send send_step (v state.f_control.f_send_sequence) /\
  state.f_receive_chain ==
    chain_after #v_ReceiveChain #v_Material
      initial_receive receive_step (v state.f_control.f_receive_sequence) /\
  cached_materials_are_derived #v_ReceiveChain #v_Material
    initial_receive receive_step state.f_receive_slots

/// Concrete reachability specializes the generic lifetime invariant to the extracted chain and material types and the sole core-selected step.
let concrete_reachable
    (initial_send initial_receive:t_ConcreteRatchetChain)
    (state:t_ConcreteRatchetKernel)
  : prop =
  reachable #t_ConcreteRatchetChain #t_ConcreteRatchetChain
    #t_RatchetMaterial initial_send initial_receive
    concrete_ratchet_step concrete_ratchet_step state.f_refined

let chain_after_successor
    (#v_Chain #v_Material:Type0)
    (initial:v_Chain)
    (step:v_Chain -> t_RatchetStep v_Chain v_Material)
    (count:nat)
  : Lemma
      (chain_after #v_Chain #v_Material initial step (count + 1) ==
        (step
          (chain_after #v_Chain #v_Material
            initial step count)).f_chain)
  = ()

let material_at_successor
    (#v_Chain #v_Material:Type0)
    (initial:v_Chain)
    (step:v_Chain -> t_RatchetStep v_Chain v_Material)
    (count:nat)
  : Lemma
      (material_at #v_Chain #v_Material initial step (count + 1) ==
        (step
          (chain_after #v_Chain #v_Material
            initial step count)).f_material)
  = ()

let empty_material_slots_are_derived
    (#v_ReceiveChain #v_Material:Type0)
    (initial_receive:v_ReceiveChain)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (cached_materials_are_derived #v_ReceiveChain #v_Material
        initial_receive receive_step (empty_material_slots #v_Material ()))
  =
  empty_material_slots_are_none #v_Material;
  let pointwise (i:nat{i < 50})
    : Lemma
        (match
           refined_slot_value (empty_material_slots #v_Material ()) i
         with
         | Core_models.Option.Option_Some cached ->
             v cached.f_sequence > 0 /\
             cached.f_material ==
               material_at #v_ReceiveChain #v_Material
                 initial_receive receive_step (v cached.f_sequence)
         | Core_models.Option.Option_None -> True)
    = ()
  in
  FStar.Classical.forall_intro pointwise

/// A sequence and its concrete material occupy the same unique active slot.
let refined_slot
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (material:v_Material)
    (slot:u8{v slot < 50})
  : prop =
  cache_slot state.f_control.f_receive_cache sequence slot /\
  refined_slot_value state.f_receive_slots (v slot) ==
    Core_models.Option.Option_Some
      ({ f_sequence = sequence; f_material = material } <:
        t_CachedReceiveKey v_Material)

/// A packed append preserves every earlier sequence/material association pointwise.
let packed_prefix_unchanged
    (#v_Material:Type0)
    (old_cache new_cache:t_SequenceCache)
    (old_slots new_slots:
      t_Array
        (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
        (mk_usize 50))
  : prop =
  forall (i:nat{i < 50}).
    i < cache_len old_cache ==>
      cache_entry new_cache i == cache_entry old_cache i /\
      refined_slot_value new_slots i == refined_slot_value old_slots i

let packed_prefix_unchanged_refl
    (#v_Material:Type0)
    (cache:t_SequenceCache)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
  : Lemma (packed_prefix_unchanged cache cache slots slots)
  =
  let pointwise (i:nat{i < 50})
    : Lemma
        (i < cache_len cache ==>
          cache_entry cache i == cache_entry cache i /\
          refined_slot_value slots i == refined_slot_value slots i)
    = ()
  in
  FStar.Classical.forall_intro pointwise

let packed_prefix_unchanged_transitive
    (#v_Material:Type0)
    (cache0 cache1 cache2:t_SequenceCache)
    (slots0 slots1 slots2:
      t_Array
        (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
        (mk_usize 50))
  : Lemma
      (requires
        (packed_prefix_unchanged cache0 cache1 slots0 slots1 /\
         packed_prefix_unchanged cache1 cache2 slots1 slots2 /\
         cache_len cache0 <= cache_len cache1))
      (ensures
        (packed_prefix_unchanged cache0 cache2 slots0 slots2))
  =
  let pointwise (i:nat{i < 50})
    : Lemma
        (i < cache_len cache0 ==>
          cache_entry cache2 i == cache_entry cache0 i /\
          refined_slot_value slots2 i == refined_slot_value slots0 i)
    =
    if i < cache_len cache0 then
      (assert (i < cache_len cache1);
       assert
         (cache_entry cache1 i == cache_entry cache0 i /\
          refined_slot_value slots1 i == refined_slot_value slots0 i);
       assert
         (cache_entry cache2 i == cache_entry cache1 i /\
          refined_slot_value slots2 i == refined_slot_value slots1 i))
    else ()
  in
  FStar.Classical.forall_intro pointwise

/// Appending one canonically derived tagged record to a derived packed prefix preserves derivational provenance for the complete slot array.
let cached_materials_after_append_are_derived
    (#v_ReceiveChain #v_Material:Type0)
    (initial_receive:v_ReceiveChain)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (old_cache new_cache:t_SequenceCache)
    (old_slots new_slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (sequence:u64 { v sequence > 0 })
    (material:v_Material {
       material == material_at #v_ReceiveChain #v_Material
         initial_receive receive_step (v sequence) })
    (slot:nat { slot < 50 /\ slot == cache_len old_cache })
  : Lemma
      (requires
        (cached_materials_are_derived #v_ReceiveChain #v_Material
           initial_receive receive_step old_slots /\
         cache_len new_cache == cache_len old_cache + 1 /\
         packed_prefix_unchanged old_cache new_cache old_slots new_slots /\
         material_slots_match new_cache new_slots /\
         refined_slot_value new_slots slot ==
           Core_models.Option.Option_Some
             ({ f_sequence = sequence; f_material = material } <:
               t_CachedReceiveKey v_Material)))
      (ensures
        (cached_materials_are_derived #v_ReceiveChain #v_Material
          initial_receive receive_step new_slots))
  =
  let pointwise (i:nat{i < 50})
    : Lemma
        (match refined_slot_value new_slots i with
         | Core_models.Option.Option_Some cached ->
             v cached.f_sequence > 0 /\
             cached.f_material ==
               material_at #v_ReceiveChain #v_Material
                 initial_receive receive_step (v cached.f_sequence)
         | Core_models.Option.Option_None -> True)
    =
    if i < cache_len old_cache then
      (assert
        (refined_slot_value new_slots i ==
          refined_slot_value old_slots i);
       match refined_slot_value old_slots i with
       | Core_models.Option.Option_Some cached -> ()
       | Core_models.Option.Option_None -> ())
    else
      match refined_slot_value new_slots i with
      | Core_models.Option.Option_None -> ()
      | Core_models.Option.Option_Some cached ->
          assert (i < cache_len new_cache);
          assert (i == slot);
          ()
  in
  FStar.Classical.forall_intro pointwise

/// One admitted receive step consumes the prior chain and associates the exact pure callback result with the appended sequence.
let refined_receive_step_matches
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (old_state next_state:
      t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : prop =
  let stepped = step old_state.f_receive_chain  in
  valid_refined old_state /\
  valid_refined next_state /\
  next_state.f_send_chain == old_state.f_send_chain /\
  next_state.f_control.f_send_sequence ==
    old_state.f_control.f_send_sequence /\
  next_state.f_receive_chain == stepped.f_chain /\
  sequence == next_state.f_control.f_receive_sequence /\
  v next_state.f_control.f_receive_sequence ==
    v old_state.f_control.f_receive_sequence + 1 /\
  cache_len next_state.f_control.f_receive_cache ==
    cache_len old_state.f_control.f_receive_cache + 1 /\
  packed_prefix_unchanged
    old_state.f_control.f_receive_cache
    next_state.f_control.f_receive_cache
    old_state.f_receive_slots
    next_state.f_receive_slots /\
  (exists (slot:u8{v slot < 50}).
     v slot == cache_len old_state.f_control.f_receive_cache /\
     refined_slot next_state sequence stepped.f_material slot)

/// Pure callback-result trace for exactly `remaining` successful receive transitions.
let rec refined_receive_steps_are_ordered
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (old_state final_state:
      t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (remaining:u8)
  : Tot prop (decreases (v remaining)) =
  valid_refined old_state /\
  valid_refined final_state /\
  packed_prefix_unchanged
    old_state.f_control.f_receive_cache
    final_state.f_control.f_receive_cache
    old_state.f_receive_slots
    final_state.f_receive_slots /\
  (if remaining = mk_u8 0 then final_state == old_state
   else
     let next_remaining = remaining -! mk_u8 1 in
     exists
       (next_state:t_RefinedRatchet
         v_SendChain v_ReceiveChain v_Material)
       (sequence:u64).
       refined_receive_step_matches
         old_state next_state sequence  step /\
       refined_receive_steps_are_ordered
         next_state final_state  step next_remaining)

/// The restoration builder maintains the same packed correspondence plus the sorted logical builder invariant.
let valid_refined_restore
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (restore:t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material)
  : prop =
  valid_restore restore.f_logical /\
  material_slots_match
    restore.f_logical.f_state.f_receive_cache
    restore.f_receive_slots

/// Conditional restoration invariant: trusted persistence provenance must establish the canonical live chains initially and the canonical material premise for every append.
let reachable_restore
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (restore:t_RefinedRatchetRestore
      v_SendChain v_ReceiveChain v_Material)
  : prop =
  valid_refined_restore restore /\
  restore.f_send_chain ==
    chain_after #v_SendChain #v_Material
      initial_send send_step
      (v restore.f_logical.f_state.f_send_sequence) /\
  restore.f_receive_chain ==
    chain_after #v_ReceiveChain #v_Material
      initial_receive receive_step
      (v restore.f_logical.f_state.f_receive_sequence) /\
  cached_materials_are_derived #v_ReceiveChain #v_Material
    initial_receive receive_step restore.f_receive_slots

/// Fresh refined constructors establish the complete logical/material invariant for arbitrary chain values.
let refined_from_counters_is_valid
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (send_sequence receive_sequence:u64)
    (send_chain:v_SendChain)
    (receive_chain:v_ReceiveChain)
  : Lemma
      (valid_refined
        (impl_10__from_counters #v_SendChain #v_ReceiveChain #v_Material
          send_sequence receive_sequence send_chain receive_chain))
  = from_counters_is_valid send_sequence receive_sequence;
    empty_material_slots_are_none #v_Material

let refined_new_is_valid
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (send_chain:v_SendChain)
    (receive_chain:v_ReceiveChain)
  : Lemma
      (valid_refined
        (impl_10__new #v_SendChain #v_ReceiveChain #v_Material
          send_chain receive_chain))
  = refined_from_counters_is_valid #v_SendChain #v_ReceiveChain #v_Material
      (mk_u64 0) (mk_u64 0) send_chain receive_chain

/// The arbitrary-counter constructor establishes reachability only when both supplied live chains are already the canonical derivations named by those counters.
let refined_from_counters_is_reachable
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (send_sequence receive_sequence:u64)
    (send_chain:v_SendChain)
    (receive_chain:v_ReceiveChain)
  : Lemma
      (requires
        (send_chain ==
           chain_after #v_SendChain #v_Material
             initial_send send_step (v send_sequence) /\
         receive_chain ==
           chain_after #v_ReceiveChain #v_Material
             initial_receive receive_step (v receive_sequence)))
      (ensures
        (reachable #v_SendChain #v_ReceiveChain #v_Material
          initial_send initial_receive send_step receive_step
          (impl_10__from_counters #v_SendChain #v_ReceiveChain #v_Material
            send_sequence receive_sequence send_chain receive_chain)))
  =
  refined_from_counters_is_valid #v_SendChain #v_ReceiveChain #v_Material
    send_sequence receive_sequence send_chain receive_chain;
  empty_material_slots_are_derived #v_ReceiveChain #v_Material
    initial_receive receive_step

/// Fresh initialization is unconditionally reachable from the two supplied directional chains under any fixed pair of pure abstract steps.
let refined_new_is_reachable
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (reachable #v_SendChain #v_ReceiveChain #v_Material
        initial_send initial_receive send_step receive_step
        (impl_10__new #v_SendChain #v_ReceiveChain #v_Material
          initial_send initial_receive))
  =
  refined_from_counters_is_reachable
    #v_SendChain #v_ReceiveChain #v_Material
    initial_send initial_receive send_step receive_step
    (mk_u64 0) (mk_u64 0) initial_send initial_receive

/// A fresh production-specialized kernel is reachable from its exact supplied chains under the executor sealed into both directions.
let concrete_kernel_new_is_reachable
    (send_chain receive_chain:t_RatchetChain)
    (kdf:t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76))
  : Lemma
      (let initial_send =
         ({ f_chain = send_chain; f_kdf = kdf } <: t_ConcreteRatchetChain) in
       let initial_receive =
         ({ f_chain = receive_chain; f_kdf = kdf } <: t_ConcreteRatchetChain) in
       concrete_reachable initial_send initial_receive
         (impl_ConcreteRatchetKernel__new send_chain receive_chain kdf))
  =
  refined_new_is_reachable
    #t_ConcreteRatchetChain #t_ConcreteRatchetChain #t_RatchetMaterial
    ({ f_chain = send_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
    ({ f_chain = receive_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
    concrete_ratchet_step concrete_ratchet_step

/// Send exhaustion and every other rejected allocation preserve the complete refined state and are independent of the opaque step result.
let refined_advance_send_rejection_is_neutral
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
  : Lemma
      (let state', result = refined_advance_send state  step in
       result == Core_models.Option.Option_None ==> state' == state)
  = ()

/// A successful send publishes the counter and exact next chain returned by one opaque step and returns that same step's material in the one-use token.
let refined_advance_send_success_uses_step
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
  : Lemma
      (let state', result = refined_advance_send state  step in
       match result with
       | Core_models.Option.Option_Some key ->
           let stepped = step state.f_send_chain  in
           state'.f_send_chain == stepped.f_chain /\
           state'.f_control.f_receive_sequence ==
             state.f_control.f_receive_sequence /\
           state'.f_control.f_receive_cache ==
             state.f_control.f_receive_cache /\
           state'.f_receive_chain == state.f_receive_chain /\
           state'.f_receive_slots == state.f_receive_slots /\
           key.f_material == stepped.f_material /\
           impl_11__sequence key ==
             Core_models.Option.Option_Some state'.f_control.f_send_sequence /\
           v state'.f_control.f_send_sequence ==
             v state.f_control.f_send_sequence + 1 /\
           refined_finish_send key
       | Core_models.Option.Option_None -> state' == state)
  = advance_send_is_monotonic state.f_control;
    advance_send_preserves_receive_state state.f_control;
    advance_send_key_matches_sequence state.f_control

/// Send advancement preserves the complete logical/material invariant, including across exhaustion.
let refined_advance_send_preserves_validity
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
  : Lemma
      (let state', _ = refined_advance_send state  step in
       valid_refined state')
  = advance_send_preserves_receive_state state.f_control;
    refined_advance_send_success_uses_step state  step

/// Send advancement preserves reachability under the same fixed step and returns the canonical material for the newly published send counter.
let refined_advance_send_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
  : Lemma
      (let state', result = refined_advance_send state send_step in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state' /\
       (match result with
        | Core_models.Option.Option_Some key ->
            key.f_material ==
              material_at #v_SendChain #v_Material
                initial_send send_step
                (v state'.f_control.f_send_sequence)
        | Core_models.Option.Option_None -> state' == state))
  =
  refined_advance_send_preserves_validity state send_step;
  refined_advance_send_success_uses_step state send_step;
  let state', result = refined_advance_send state send_step in
  match result with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some key ->
      chain_after_successor #v_SendChain #v_Material
        initial_send send_step (v state.f_control.f_send_sequence);
      material_at_successor #v_SendChain #v_Material
        initial_send send_step (v state.f_control.f_send_sequence)

/// The public seal operation passes the exact material produced from the old send chain, the allocated sequence, and the caller's context to one opaque callback, then returns that callback's result after consuming the private token.
let refined_seal_next_uses_exact_step_material
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Output:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       state.f_control.f_send_sequence <>
         Core_models.Num.impl_u64__MAX })
    (step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (context:v_Context)
    (seal:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Output)
  : Lemma
      (let stepped = step state.f_send_chain in
       let sealed_state, output =
         refined_seal_next state step context seal in
       sealed_state.f_send_chain == stepped.f_chain /\
       sealed_state.f_receive_chain == state.f_receive_chain /\
       sealed_state.f_receive_slots == state.f_receive_slots /\
       v sealed_state.f_control.f_send_sequence ==
         v state.f_control.f_send_sequence + 1 /\
       output ==
         seal stepped.f_material
           sealed_state.f_control.f_send_sequence context)
  = refined_advance_send_success_uses_step state step

/// The public seal operation preserves the complete refined invariant on both callback success and callback failure.
let refined_seal_next_preserves_validity
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Output:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (context:v_Context)
    (seal:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Output)
  : Lemma
      (let sealed_state, _ =
         refined_seal_next state step context seal in
       valid_refined sealed_state)
  = refined_advance_send_preserves_validity state step

/// Public sealing preserves derivational reachability on both callback success and callback failure because the private token is consumed after the same canonical send step.
let refined_seal_next_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Output:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (context:v_Context)
    (seal:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Output)
  : Lemma
      (let sealed_state, _ =
         refined_seal_next state send_step context seal in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step sealed_state)
  = refined_advance_send_preserves_reachability
      initial_send initial_receive send_step receive_step state

/// The production-facing seal wrapper preserves concrete reachability while selecting the core-fixed step internally.
let concrete_seal_next_preserves_reachability
    (#v_Context #v_Output:Type0)
    (initial_send initial_receive:t_ConcreteRatchetChain)
    (state:t_ConcreteRatchetKernel {
       concrete_reachable initial_send initial_receive state })
    (context:v_Context)
    (seal:t_RatchetMaterial -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Output)
  : Lemma
      (let sealed_state, _ = concrete_seal_next state context seal in
       concrete_reachable initial_send initial_receive sealed_state)
  =
  refined_seal_next_preserves_reachability
    #t_ConcreteRatchetChain #t_ConcreteRatchetChain #t_RatchetMaterial
    #v_Context #v_Output initial_send initial_receive
    concrete_ratchet_step concrete_ratchet_step state.f_refined context seal

/// Receive rejection is state-neutral and cannot depend on the opaque callback because validation precedes its application.
let refined_advance_receive_rejection_is_step_independent
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (step1 step2:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let state1, result1 = refined_advance_receive state  step1 in
       result1 == Core_models.Option.Option_None ==>
         state1 == state /\
         refined_advance_receive state  step2 ==
           (state, Core_models.Option.Option_None))
  = ()

/// A successful receive step associates the returned sequence with the exact material and next chain produced by the callback in the old append slot.
let refined_advance_receive_success_uses_step
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material { valid_refined state })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let state', result = refined_advance_receive state  step in
       match result with
       | Core_models.Option.Option_Some sequence ->
           let stepped = step state.f_receive_chain  in
           valid_refined state' /\
           state'.f_send_chain == state.f_send_chain /\
           state'.f_receive_chain == stepped.f_chain /\
           v state'.f_control.f_receive_sequence ==
             v state.f_control.f_receive_sequence + 1 /\
           cache_len state'.f_control.f_receive_cache ==
             cache_len state.f_control.f_receive_cache + 1 /\
           packed_prefix_unchanged
             state.f_control.f_receive_cache
             state'.f_control.f_receive_cache
             state.f_receive_slots
             state'.f_receive_slots /\
           (exists (slot:u8{v slot < 50}).
              v slot == cache_len state.f_control.f_receive_cache /\
              refined_slot state' sequence stepped.f_material slot)
       | Core_models.Option.Option_None -> state' == state)
  = advance_receive_success_shape state.f_control;
    advance_receive_preserves_validity state.f_control

/// Every one-step refined receive transition preserves the complete packed invariant.
let refined_advance_receive_preserves_validity
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material { valid_refined state })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let state', _ = refined_advance_receive state  step in
       valid_refined state')
  = refined_advance_receive_success_uses_step state  step

/// A successful one-step result realizes the central chain/material association relation.
let refined_advance_receive_success_matches
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let next_state, result =
         refined_advance_receive state  step in
       match result with
       | Core_models.Option.Option_Some sequence ->
           refined_receive_step_matches
             state next_state sequence  step
       | Core_models.Option.Option_None -> next_state == state)
  =
  advance_receive_success_shape state.f_control;
  refined_advance_receive_preserves_validity state  step;
  refined_advance_receive_success_uses_step state  step

/// One receive advancement under the fixed receive step preserves both live-chain iteration and canonical material provenance for the appended cache entry.
let refined_advance_receive_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
  : Lemma
      (let state', _ = refined_advance_receive state receive_step in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state')
  =
  refined_advance_receive_preserves_validity state receive_step;
  refined_advance_receive_success_uses_step state receive_step;
  let state', result = refined_advance_receive state receive_step in
  match result with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some sequence ->
      let stepped = receive_step state.f_receive_chain in
      chain_after_successor #v_ReceiveChain #v_Material
        initial_receive receive_step
        (v state.f_control.f_receive_sequence);
      material_at_successor #v_ReceiveChain #v_Material
        initial_receive receive_step
        (v state.f_control.f_receive_sequence);
      assert (v sequence > 0);
      assert
        (stepped.f_material ==
          material_at #v_ReceiveChain #v_Material
            initial_receive receive_step (v sequence));
      let slot:(i:nat{i < 50}) =
        cache_len state.f_control.f_receive_cache in
      assert
        (refined_slot_value state'.f_receive_slots slot ==
          Core_models.Option.Option_Some
            ({ f_sequence = sequence; f_material = stepped.f_material } <:
              t_CachedReceiveKey v_Material));
      cached_materials_after_append_are_derived
        #v_ReceiveChain #v_Material
        initial_receive receive_step
        state.f_control.f_receive_cache
        state'.f_control.f_receive_cache
        state.f_receive_slots state'.f_receive_slots
        sequence stepped.f_material slot

/// Every slot in a bounded inactive suffix is empty in a valid refined state, so whole-plan preflight cannot reject an admitted plan.
let rec refined_receive_slots_are_empty_for_valid
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (first_slot:u8 {
       cache_len state.f_control.f_receive_cache <= v first_slot })
    (remaining:u8 { v first_slot + v remaining <= 50 })
  : Lemma
      (ensures
        (refined_receive_slots_are_empty
          state first_slot remaining == true))
      (decreases (v remaining))
  =
  if remaining = mk_u8 0 then ()
  else
    let i:(x:nat { x < 50 }) = v first_slot in
    let slot_value = refined_slot_value state.f_receive_slots i in
    refined_slot_value_is_index state.f_receive_slots i;
    assert
      (material_slots_match
        state.f_control.f_receive_cache state.f_receive_slots);
    match slot_value with
    | Core_models.Option.Option_Some _ ->
        assert (i < cache_len state.f_control.f_receive_cache);
        ()
    | Core_models.Option.Option_None ->
        refined_receive_slots_are_empty_for_valid
          state
          (first_slot +! mk_u8 1)
          (remaining -! mk_u8 1)

/// Space in both the counter and packed cache makes the next refined receive step total; its result is the exact opaque callback result in the append slot.
let refined_advance_receive_with_space_succeeds
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state /\
       state.f_control.f_receive_sequence <>
         Core_models.Num.impl_u64__MAX /\
       cache_len state.f_control.f_receive_cache < 50 })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let next_state, result =
         refined_advance_receive state  step in
       match result with
       | Core_models.Option.Option_Some sequence ->
           refined_receive_step_matches
             state next_state sequence  step
       | Core_models.Option.Option_None -> False)
  =
  let slot:u8 = state.f_control.f_receive_cache.f_len in
  let i:(x:nat { x < 50 }) = v slot in
  let slot_value = refined_slot_value state.f_receive_slots i in
  refined_slot_value_is_index state.f_receive_slots i;
  assert
    (material_slots_match
      state.f_control.f_receive_cache state.f_receive_slots);
  (match slot_value with
   | Core_models.Option.Option_Some _ ->
       assert (i < cache_len state.f_control.f_receive_cache);
       ()
   | Core_models.Option.Option_None -> ());
  advance_receive_success_shape state.f_control;
  refined_advance_receive_success_matches state  step

/// The bounded commit recursion executes every planned transition: exact callback order, exact counter/cache growth, and pointwise preservation of the old packed prefix.
let rec refined_execute_receive_steps_is_exact
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (remaining:u8 {
       cache_len state.f_control.f_receive_cache + v remaining <= 50 /\
       v state.f_control.f_receive_sequence + v remaining <=
         v Core_models.Num.impl_u64__MAX })
  : Lemma
      (ensures
        (let final_state =
           refined_execute_receive_steps state  step remaining in
         refined_receive_steps_are_ordered
           state final_state  step remaining /\
         v final_state.f_control.f_receive_sequence ==
           v state.f_control.f_receive_sequence + v remaining /\
         cache_len final_state.f_control.f_receive_cache ==
           cache_len state.f_control.f_receive_cache + v remaining))
      (decreases (v remaining))
  =
  if remaining = mk_u8 0 then
    packed_prefix_unchanged_refl
      state.f_control.f_receive_cache state.f_receive_slots
  else
    let next_remaining = remaining -! mk_u8 1 in
    assert
      (state.f_control.f_receive_sequence <>
        Core_models.Num.impl_u64__MAX);
    assert (cache_len state.f_control.f_receive_cache < 50);
    refined_advance_receive_with_space_succeeds state  step;
    let next_state, result = refined_advance_receive state  step in
    match result with
    | Core_models.Option.Option_None -> ()
    | Core_models.Option.Option_Some sequence ->
        assert (valid_refined next_state);
        assert
          (refined_receive_step_matches
            state next_state sequence  step);
        refined_execute_receive_steps_is_exact
          next_state  step next_remaining;
        let final_state =
          refined_execute_receive_steps
            next_state  step next_remaining in
        assert
          (refined_receive_steps_are_ordered
            next_state final_state  step next_remaining);
        packed_prefix_unchanged_transitive
          state.f_control.f_receive_cache
          next_state.f_control.f_receive_cache
          final_state.f_control.f_receive_cache
          state.f_receive_slots
          next_state.f_receive_slots
          final_state.f_receive_slots;
        assert
          (exists
             (middle:t_RefinedRatchet
               v_SendChain v_ReceiveChain v_Material)
             (derived_sequence:u64).
               middle == next_state /\
               derived_sequence == sequence /\
               refined_receive_step_matches
                 state middle derived_sequence  step /\
               refined_receive_steps_are_ordered
                 middle final_state  step next_remaining);
        ()

/// Any bounded executor suffix preserves reachability because each internal transition uses the same fixed receive step.
let rec refined_execute_receive_steps_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (remaining:u8)
  : Lemma
      (ensures
        (reachable #v_SendChain #v_ReceiveChain #v_Material
          initial_send initial_receive send_step receive_step
          (refined_execute_receive_steps state receive_step remaining)))
      (decreases (v remaining))
  =
  if remaining = mk_u8 0 then ()
  else
    let next_remaining = remaining -! mk_u8 1 in
    refined_advance_receive_preserves_reachability
      initial_send initial_receive send_step receive_step state;
    let next_state, _ = refined_advance_receive state receive_step in
    assert
      (reachable #v_SendChain #v_ReceiveChain #v_Material
        initial_send initial_receive send_step receive_step next_state);
    refined_execute_receive_steps_preserves_reachability
      initial_send initial_receive send_step receive_step
      next_state next_remaining

/// Receive-until planning, preflight, and bounded execution preserve reachability for both admitted plans and every state-neutral rejection.
let refined_advance_receive_until_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (target:u64)
  : Lemma
      (let state', _ =
         refined_advance_receive_until state target receive_step in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state')
  =
  let plan = plan_receive_until state.f_control target in
  match plan.f_sequence with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some _ ->
      if plan.f_derivations >. v_RATCHET_MAX_GAP then ()
      else
        let remaining:u8 = cast plan.f_derivations <: u8 in
        let first_slot =
          impl_RatchetState__receive_cache_len state.f_control in
        if not
          (refined_receive_slots_are_empty
            state first_slot remaining)
        then ()
        else
          refined_execute_receive_steps_preserves_reachability
            initial_send initial_receive send_step receive_step
            state remaining

/// Once planning and concrete-slot preflight are admitted, the generated
/// transaction is definitionally the full bounded execution and its planned
/// target; there is no intermediate failure branch.
let refined_advance_receive_until_accepted_computes
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (requested reached:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (remaining:u8)
  : Lemma
      (requires
        (let plan = plan_receive_until state.f_control requested in
         plan.f_sequence == Core_models.Option.Option_Some reached /\
         not (plan.f_derivations >. v_RATCHET_MAX_GAP) /\
         remaining == (cast plan.f_derivations <: u8) /\
         refined_receive_slots_are_empty
           state
           (impl_RatchetState__receive_cache_len state.f_control)
           remaining == true))
      (ensures
        (refined_advance_receive_until state  requested step ==
          (refined_execute_receive_steps state  step remaining,
           Core_models.Option.Option_Some reached)))
  = ()

/// The complete transaction exactly realizes every admitted plan. Planning or preflight rejection is neutral; success returns the requested target with the full ordered refinement as one result.
let refined_advance_receive_until_executes_plan
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (target:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let plan = plan_receive_until state.f_control target in
       let remaining = cast plan.f_derivations <: u8 in
       let final_state, result =
         refined_advance_receive_until state  target step in
       valid_refined final_state /\
       (match plan.f_sequence, result with
       | Core_models.Option.Option_None,
         Core_models.Option.Option_None -> final_state == state
       | Core_models.Option.Option_Some planned_target,
         Core_models.Option.Option_Some reached ->
           planned_target == target /\
           reached == target /\
           refined_receive_steps_are_ordered
             state final_state  step remaining /\
           v final_state.f_control.f_receive_sequence ==
             v state.f_control.f_receive_sequence + v plan.f_derivations /\
           cache_len final_state.f_control.f_receive_cache ==
             cache_len state.f_control.f_receive_cache +
               v plan.f_derivations /\
           (v target > v state.f_control.f_receive_sequence ==>
             final_state.f_control.f_receive_sequence == target) /\
           (v target <= v state.f_control.f_receive_sequence ==>
             final_state == state)
       | _ -> False))
  =
  let plan = plan_receive_until state.f_control target in
  plan_receive_shape state.f_control target;
  assert (v plan.f_derivations <= 50);
  match plan.f_sequence with
  | Core_models.Option.Option_None ->
      assert
        (refined_advance_receive_until state  target step ==
          (state, Core_models.Option.Option_None));
      ()
  | Core_models.Option.Option_Some planned_target ->
      assert (planned_target == target);
      assert (plan.f_derivations <=. v_RATCHET_MAX_GAP);
      let remaining = cast plan.f_derivations <: u8 in
      let first_slot = state.f_control.f_receive_cache.f_len in
      if v target > v state.f_control.f_receive_sequence then
        (let future_target:(x:u64 {
           v x > v state.f_control.f_receive_sequence }) = target in
         plan_future_receive_is_bounded state.f_control future_target;
         assert
           (cache_len state.f_control.f_receive_cache +
             v remaining <= 50);
         assert
           (v state.f_control.f_receive_sequence + v remaining ==
             v target);
         refined_receive_slots_are_empty_for_valid
           state first_slot remaining;
         assert
           (refined_receive_slots_are_empty
             state first_slot remaining == true);
         assert (not (plan.f_derivations >. v_RATCHET_MAX_GAP));
         assert
           (impl_RatchetState__receive_cache_len state.f_control ==
             first_slot);
         refined_execute_receive_steps_is_exact
           state  step remaining;
         let final_state =
           refined_execute_receive_steps state  step remaining in
         assert (v remaining == v plan.f_derivations);
         assert (valid_refined final_state);
         assert
           (refined_receive_steps_are_ordered
             state final_state  step remaining);
         assert
           (v final_state.f_control.f_receive_sequence ==
             v state.f_control.f_receive_sequence + v remaining);
         assert
           (cache_len final_state.f_control.f_receive_cache ==
             cache_len state.f_control.f_receive_cache + v remaining);
         let final_sequence =
           final_state.f_control.f_receive_sequence in
         assert (v final_sequence == v target);
         u64_value_extensionality final_sequence target;
         assert (final_sequence == target);
         assert
           (final_state.f_control.f_receive_sequence == target);
         refined_advance_receive_until_accepted_computes
           state  target planned_target step remaining;
         assert
           (refined_advance_receive_until state  target step ==
             (final_state,
              Core_models.Option.Option_Some planned_target));
         ())
      else
        (assert (plan.f_derivations == mk_u64 0);
         assert (remaining == mk_u8 0);
         refined_receive_slots_are_empty_for_valid
           state first_slot remaining;
         assert
           (refined_receive_slots_are_empty
             state first_slot remaining == true);
         assert (not (plan.f_derivations >. v_RATCHET_MAX_GAP));
         assert
           (impl_RatchetState__receive_cache_len state.f_control ==
             first_slot);
         refined_execute_receive_steps_is_exact
           state  step remaining;
         assert
           (refined_execute_receive_steps state  step remaining ==
             state);
         refined_advance_receive_until_accepted_computes
           state  target planned_target step remaining;
         assert
           (refined_advance_receive_until state  target step ==
             (state,
              Core_models.Option.Option_Some planned_target));
         ())

/// Rejected whole-plan execution is unconditionally neutral for every valid refined state; no committed prefix can accompany `None`.
let refined_advance_receive_until_rejection_is_neutral
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (target:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let final_state, result =
         refined_advance_receive_until state  target step in
       result == Core_models.Option.Option_None ==>
         final_state == state /\
         (plan_receive_until state.f_control target).f_sequence ==
           Core_models.Option.Option_None)
  = refined_advance_receive_until_executes_plan state  target step

/// A successful whole-plan result contains the exact plan-length callback trace and preserves every old sequence/material association.
let refined_advance_receive_until_is_ordered
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (target:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (let plan = plan_receive_until state.f_control target in
       let remaining = cast plan.f_derivations <: u8 in
       let final_state, result =
         refined_advance_receive_until state  target step in
       match result with
       | Core_models.Option.Option_Some reached ->
           reached == target /\
           refined_receive_steps_are_ordered
             state final_state  step remaining
       | Core_models.Option.Option_None -> final_state == state)
  = refined_advance_receive_until_executes_plan state  target step

/// A zero-cost receive-until lookup invokes no step and leaves every refined field unchanged.
let refined_advance_receive_until_old_is_neutral
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (target:u64 { v target <= v state.f_control.f_receive_sequence })
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
  : Lemma
      (refined_advance_receive_until state  target step ==
        (state, Core_models.Option.Option_Some target))
  = plan_old_receive_is_zero_cost state.f_control target

/// Serialization's active-slot accessor exposes only a sealed pair whose tag
/// is the logical sequence stored at that same physical slot.
let refined_receive_entry_is_associated
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (slot:u8 {
       v slot < 50 /\
       v slot < cache_len state.f_control.f_receive_cache })
  : Lemma
      (match impl_10__receive_entry_at state slot with
       | Core_models.Option.Option_Some (sequence, material) ->
           refined_slot state sequence material slot
       | Core_models.Option.Option_None -> False)
  = ()

/// The active-slot accessor detects an internal tag/control disagreement.
let refined_receive_entry_mismatched_tag_is_rejected
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (slot:u8{v slot < 50})
    (sequence:u64)
    (cached:t_CachedReceiveKey v_Material {
       impl_RatchetState__receive_key_at state.f_control slot ==
         Core_models.Option.Option_Some sequence /\
       refined_slot_value state.f_receive_slots (v slot) ==
         Core_models.Option.Option_Some cached /\
       cached.f_sequence <> sequence })
  : Lemma
      (impl_10__receive_entry_at state slot ==
        Core_models.Option.Option_None)
  = ()

/// A physically populated lookup slot whose sealed tag disagrees with the
/// requested logical sequence is rejected rather than exposing its material.
let refined_receive_key_mismatched_tag_is_rejected
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (slot:u8{v slot < 50})
    (cached:t_CachedReceiveKey v_Material {
       lookup_receive_key state.f_control sequence ==
         Core_models.Option.Option_Some slot /\
       refined_slot_value state.f_receive_slots (v slot) ==
         Core_models.Option.Option_Some cached /\
       cached.f_sequence <> sequence })
  : Lemma
      (refined_receive_key state sequence ==
        Core_models.Option.Option_None)
  = ()

/// Concrete lookup returns material only from the unique logical slot for the requested sequence.
let refined_receive_key_is_associated
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material { valid_refined state })
    (sequence:u64)
  : Lemma
      (match refined_receive_key state sequence with
       | Core_models.Option.Option_Some material ->
           exists (slot:u8{v slot < 50}). refined_slot state sequence material slot
       | Core_models.Option.Option_None ->
           ~(exists (material:v_Material) (slot:u8{v slot < 50}).
               refined_slot state sequence material slot))
  =
  lookup_receive_key_returns_unique_slot state.f_control sequence;
  let logical = lookup_receive_key state.f_control sequence in
  match logical with
  | Core_models.Option.Option_None ->
      assert (~(cache_has state.f_control.f_receive_cache sequence));
      assert
        (refined_receive_key state sequence ==
          Core_models.Option.Option_None);
      assert
        (~(exists (material:v_Material) (slot:u8{v slot < 50}).
            refined_slot state sequence material slot));
      ()
  | Core_models.Option.Option_Some slot ->
      assert
        (cache_slot state.f_control.f_receive_cache sequence slot);
      let active_slot:(x:u8 { v x < 50 }) = slot in
      match refined_slot_value state.f_receive_slots (v active_slot) with
      | Core_models.Option.Option_None ->
          assert
            (cache_len state.f_control.f_receive_cache <= v active_slot);
          assert
            (v active_slot < cache_len state.f_control.f_receive_cache);
          ()
      | Core_models.Option.Option_Some cached ->
          assert (cached.f_sequence == sequence);
          let material = cached.f_material in
          assert
            (refined_receive_key state sequence ==
              Core_models.Option.Option_Some material);
          assert (refined_slot state sequence material active_slot);
          assert
            (exists (witness:u8{v witness < 50}).
               refined_slot state sequence material witness);
          ()

/// Lookup from a reachable state can expose only the canonical receive material derived for the requested sequence.
let refined_receive_key_is_derived
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (sequence:u64)
  : Lemma
      (match refined_receive_key state sequence with
       | Core_models.Option.Option_Some material ->
           v sequence > 0 /\
           material ==
             material_at #v_ReceiveChain #v_Material
               initial_receive receive_step (v sequence)
       | Core_models.Option.Option_None -> True)
  =
  refined_receive_key_is_associated state sequence;
  match refined_receive_key state sequence with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some material ->
      assert
        (exists (slot:u8{v slot < 50}).
          refined_slot state sequence material slot);
      ()

/// Missing and failed-authentication completion preserve every control, chain, and material field.
let refined_finish_receive_neutral_outcomes_preserve_full_state
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (authenticated:bool)
  : Lemma
      (let state', disposition = refined_finish_receive state sequence authenticated in
       disposition == ReceiveDisposition_Missing \/
       disposition == ReceiveDisposition_Retained ==>
         state' == state)
  = ()

/// A matching logical lookup paired with a differently tagged target token is
/// rejected before logical or concrete state can change.
let refined_finish_receive_mismatched_target_is_neutral
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (authenticated:bool)
    (slot:u8{v slot < 50})
    (cached:t_CachedReceiveKey v_Material {
       lookup_receive_key state.f_control sequence ==
         Core_models.Option.Option_Some slot /\
       refined_slot_value state.f_receive_slots (v slot) ==
         Core_models.Option.Option_Some cached /\
       cached.f_sequence <> sequence })
  : Lemma
      (refined_finish_receive state sequence authenticated ==
        (state, ReceiveDisposition_Missing))
  = ()

/// On a logically consumed path, a stale tag in the old-last concrete token
/// is detected before the swap and leaves the complete refined state intact.
let refined_finish_receive_mismatched_last_is_neutral
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence last_sequence:u64)
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (target_cached last_cached:t_CachedReceiveKey v_Material)
    (removal:t_ReceiveRemoval {
       lookup_receive_key state.f_control sequence ==
         Core_models.Option.Option_Some target_slot /\
       refined_slot_value state.f_receive_slots (v target_slot) ==
         Core_models.Option.Option_Some target_cached /\
       target_cached.f_sequence == sequence /\
       (finish_receive_with_removal
         state.f_control sequence target_slot true).f_disposition ==
           ReceiveDisposition_Consumed /\
       (finish_receive_with_removal
         state.f_control sequence target_slot true).f_removal ==
           Core_models.Option.Option_Some removal /\
       removal.f_target_slot == target_slot /\
       removal.f_last_slot == last_slot /\
       impl_RatchetState__receive_key_at state.f_control last_slot ==
         Core_models.Option.Option_Some last_sequence /\
       refined_slot_value state.f_receive_slots (v last_slot) ==
         Core_models.Option.Option_Some last_cached /\
       last_cached.f_sequence <> last_sequence })
  : Lemma
      (refined_finish_receive state sequence true ==
        (state, ReceiveDisposition_Missing))
  = ()

/// Logical view of the concrete sealed-token swap-removal performed by refined completion.
let material_slots_after_swap_remove
    (#v_Material:Type0)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (last_cached:t_CachedReceiveKey v_Material)
  : t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50) =
  let cleared =
    Seq.upd slots (v last_slot)
      (Core_models.Option.Option_None <:
        Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) in
  if target_slot = last_slot then cleared
  else
    Seq.upd cleared (v target_slot)
      (Core_models.Option.Option_Some last_cached <:
        Core_models.Option.t_Option (t_CachedReceiveKey v_Material))

/// Concrete swap-removal clears the old last slot, moves its exact material when needed, and preserves every other slot pointwise.
let material_slots_after_swap_remove_is_exact
    (#v_Material:Type0)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (last_cached:t_CachedReceiveKey v_Material)
  : Lemma
      (let slots' =
         material_slots_after_swap_remove
           slots target_slot last_slot last_cached in
       refined_slot_value slots' (v last_slot) ==
         Core_models.Option.Option_None /\
       (target_slot <> last_slot ==>
         refined_slot_value slots' (v target_slot) ==
           Core_models.Option.Option_Some last_cached) /\
       (forall (i:nat{i < 50}).
          i <> v target_slot /\ i <> v last_slot ==>
            refined_slot_value slots' i == refined_slot_value slots i))
  =
  let none =
    (Core_models.Option.Option_None <:
      Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) in
  let moved =
    (Core_models.Option.Option_Some last_cached <:
      Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) in
  let cleared = Seq.upd slots (v last_slot) none in
  FStar.Seq.Base.lemma_index_upd1 slots (v last_slot) none;
  if target_slot = last_slot then
    let unchanged (i:nat{i < 50})
      : Lemma
          (i <> v target_slot /\ i <> v last_slot ==>
            refined_slot_value cleared i == refined_slot_value slots i)
      = if i <> v last_slot then
          FStar.Seq.Base.lemma_index_upd2 slots (v last_slot) none i
        else ()
    in
    FStar.Classical.forall_intro unchanged
  else
    let slots' = Seq.upd cleared (v target_slot) moved in
    FStar.Seq.Base.lemma_index_upd1 cleared (v target_slot) moved;
    FStar.Seq.Base.lemma_index_upd2
      cleared (v target_slot) moved (v last_slot);
    let unchanged (i:nat{i < 50})
      : Lemma
          (i <> v target_slot /\ i <> v last_slot ==>
            refined_slot_value slots' i == refined_slot_value slots i)
      = if i <> v target_slot then
          if i <> v last_slot then
            (FStar.Seq.Base.lemma_index_upd2 slots (v last_slot) none i;
             FStar.Seq.Base.lemma_index_upd2
               cleared (v target_slot) moved i)
          else ()
        else ()
    in
    FStar.Classical.forall_intro unchanged

/// Moving the complete old-last record and clearing its former slot preserves canonical material provenance for every surviving physical cache entry.
let cached_materials_after_swap_remove_are_derived
    (#v_ReceiveChain #v_Material:Type0)
    (initial_receive:v_ReceiveChain)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (last_cached:t_CachedReceiveKey v_Material {
       refined_slot_value slots (v last_slot) ==
         Core_models.Option.Option_Some last_cached })
  : Lemma
      (requires
        (cached_materials_are_derived #v_ReceiveChain #v_Material
          initial_receive receive_step slots))
      (ensures
        (cached_materials_are_derived #v_ReceiveChain #v_Material
          initial_receive receive_step
          (material_slots_after_swap_remove
            slots target_slot last_slot last_cached)))
  =
  let slots' = material_slots_after_swap_remove
    slots target_slot last_slot last_cached in
  material_slots_after_swap_remove_is_exact
    slots target_slot last_slot last_cached;
  let pointwise (i:nat{i < 50})
    : Lemma
        (match refined_slot_value slots' i with
         | Core_models.Option.Option_Some cached ->
             v cached.f_sequence > 0 /\
             cached.f_material ==
               material_at #v_ReceiveChain #v_Material
                 initial_receive receive_step (v cached.f_sequence)
         | Core_models.Option.Option_None -> True)
    =
    if i = v last_slot then ()
    else if i = v target_slot then
      if target_slot = last_slot then ()
      else
        (assert
          (refined_slot_value slots' i ==
            Core_models.Option.Option_Some last_cached);
         assert
          (v last_cached.f_sequence > 0 /\
           last_cached.f_material ==
             material_at #v_ReceiveChain #v_Material
               initial_receive receive_step
               (v last_cached.f_sequence));
         ())
    else
      (assert
        (refined_slot_value slots' i == refined_slot_value slots i);
       match refined_slot_value slots i with
       | Core_models.Option.Option_Some cached -> ()
       | Core_models.Option.Option_None -> ())
  in
  FStar.Classical.forall_intro pointwise

/// The generated Option.take/update_at expression is definitionally the logical swap-removal view.
let generated_material_swap_remove_matches_view
    (#v_Material:Type0)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (last_cached:t_CachedReceiveKey v_Material)
  : Lemma
      (requires
        (Seq.index slots (v last_slot) ==
          Core_models.Option.Option_Some last_cached))
      (ensures
        (let target_index = cast (target_slot <: u8) <: usize in
         let last_index = cast (last_slot <: u8) <: usize in
         let tmp0, moved =
           Core_models.Option.impl__take #(t_CachedReceiveKey v_Material)
             (Seq.index slots (v last_slot)) in
         let cleared =
           Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
             slots last_index tmp0 in
         let actual =
           if target_index =. last_index then cleared
           else
             Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
               cleared target_index moved in
         actual ==
           material_slots_after_swap_remove
             slots target_slot last_slot last_cached))
  = if target_slot = last_slot then () else ()

/// On the admitted consumed path, the whole generated refined completion computes the swap-removal view.
let refined_finish_receive_success_computes_swap
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    (sequence:u64)
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (target_cached last_cached:t_CachedReceiveKey v_Material)
    (removal:t_ReceiveRemoval)
  : Lemma
      (requires
        (lookup_receive_key state.f_control sequence ==
           Core_models.Option.Option_Some target_slot /\
         (finish_receive_with_removal
           state.f_control sequence target_slot true).f_disposition ==
             ReceiveDisposition_Consumed /\
         (finish_receive_with_removal
           state.f_control sequence target_slot true).f_removal ==
             Core_models.Option.Option_Some removal /\
         removal.f_target_slot == target_slot /\
         removal.f_last_slot == last_slot /\
         Seq.index state.f_receive_slots (v target_slot) ==
           Core_models.Option.Option_Some target_cached /\
         target_cached.f_sequence == sequence /\
         Seq.index state.f_receive_slots (v last_slot) ==
           Core_models.Option.Option_Some last_cached /\
         impl_RatchetState__receive_key_at state.f_control last_slot ==
           Core_models.Option.Option_Some last_cached.f_sequence))
      (ensures
        (let finished =
           finish_receive_with_removal
             state.f_control sequence target_slot true in
         let slots' =
           material_slots_after_swap_remove
             state.f_receive_slots target_slot last_slot last_cached in
         let with_slots = { state with f_receive_slots = slots' } in
         let expected = { with_slots with f_control = finished.f_state } in
         refined_finish_receive state sequence true ==
           (expected, ReceiveDisposition_Consumed)))
  =
  generated_material_swap_remove_matches_view
    state.f_receive_slots target_slot last_slot last_cached;
  if target_slot = last_slot then () else ()

/// Logical swap-removal preserves every surviving physical entry except the
/// target slot, which receives the old last entry.
let finish_receive_with_removal_preserves_other_physical_slot
    (state:t_RatchetState { valid_state state })
    (sequence:u64)
    (target_slot:u8 { cache_slot state.f_receive_cache sequence target_slot })
  : Lemma
      (let finished =
         finish_receive_with_removal state sequence target_slot true in
       forall (i:nat{i < 50}).
         i < cache_len finished.f_state.f_receive_cache /\
         i <> v target_slot ==>
           cache_entry finished.f_state.f_receive_cache i ==
             cache_entry state.f_receive_cache i)
  =
  let finished =
    finish_receive_with_removal state sequence target_slot true in
  finish_receive_with_removal_success_shape state sequence target_slot;
  let pointwise (i:nat{i < 50})
    : Lemma
        (i < cache_len finished.f_state.f_receive_cache /\
         i <> v target_slot ==>
           cache_entry finished.f_state.f_receive_cache i ==
             cache_entry state.f_receive_cache i)
    = ()
  in
  FStar.Classical.forall_intro pointwise

/// Mirroring a logical swap-removal with the whole sealed token preserves both
/// occupancy and the token/control sequence equality.
let material_slots_after_swap_remove_matches
    (#v_Material:Type0)
    (old_cache new_cache:t_SequenceCache)
    (slots:t_Array
      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      (mk_usize 50))
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (last_cached:t_CachedReceiveKey v_Material)
  : Lemma
      (requires
        (material_slots_match old_cache slots /\
         v target_slot < cache_len old_cache /\
         v last_slot + 1 == cache_len old_cache /\
         cache_len new_cache + 1 == cache_len old_cache /\
         last_cached.f_sequence == cache_entry old_cache (v last_slot) /\
         (target_slot <> last_slot ==>
           cache_entry new_cache (v target_slot) ==
             last_cached.f_sequence) /\
         (forall (i:nat{i < 50}).
            i < cache_len new_cache /\ i <> v target_slot ==>
              cache_entry new_cache i == cache_entry old_cache i)))
      (ensures
        (material_slots_match new_cache
          (material_slots_after_swap_remove
            slots target_slot last_slot last_cached)))
  =
  let slots' =
    material_slots_after_swap_remove
      slots target_slot last_slot last_cached in
  material_slots_after_swap_remove_is_exact
    slots target_slot last_slot last_cached;
  let pointwise (i:nat{i < 50})
    : Lemma
        (match refined_slot_value slots' i with
         | Core_models.Option.Option_Some cached ->
             i < cache_len new_cache /\
             cached.f_sequence == cache_entry new_cache i
         | Core_models.Option.Option_None -> cache_len new_cache <= i)
    =
    if i = v last_slot then ()
    else if i = v target_slot then
      if target_slot = last_slot then () else ()
    else
      assert
        (refined_slot_value slots' i == refined_slot_value slots i);
      match refined_slot_value slots i with
      | Core_models.Option.Option_Some cached -> ()
      | Core_models.Option.Option_None -> ()
  in
  FStar.Classical.forall_intro pointwise

/// Successful completion moves the complete old-last tagged token into a
/// non-last target, clears the old last slot, and publishes the matching
/// logical removal atomically.
let refined_finish_receive_success_is_exact_swap_removal
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material { valid_refined state })
    (sequence:u64)
    (target_slot:u8{v target_slot < 50})
    (last_slot:u8{v last_slot < 50})
    (target_cached last_cached:t_CachedReceiveKey v_Material)
  : Lemma
      (requires
        (lookup_receive_key state.f_control sequence ==
           Core_models.Option.Option_Some target_slot /\
         v last_slot + 1 == cache_len state.f_control.f_receive_cache /\
         refined_slot_value state.f_receive_slots (v target_slot) ==
           Core_models.Option.Option_Some target_cached /\
         refined_slot_value state.f_receive_slots (v last_slot) ==
           Core_models.Option.Option_Some last_cached))
      (ensures
      (let state', disposition = refined_finish_receive state sequence true in
       disposition == ReceiveDisposition_Consumed /\
       valid_refined state' /\
       state'.f_send_chain == state.f_send_chain /\
       state'.f_receive_chain == state.f_receive_chain /\
       state'.f_control ==
         (finish_receive_with_removal
           state.f_control sequence target_slot true).f_state /\
       refined_slot_value state'.f_receive_slots (v last_slot) ==
         Core_models.Option.Option_None /\
       (target_slot <> last_slot ==>
         refined_slot_value state'.f_receive_slots (v target_slot) ==
           Core_models.Option.Option_Some last_cached) /\
       (forall (i:nat{i < 50}).
          i <> v target_slot /\ i <> v last_slot ==>
            refined_slot_value state'.f_receive_slots i ==
              refined_slot_value state.f_receive_slots i)))
  =
  lookup_receive_key_returns_unique_slot state.f_control sequence;
  assert
    (cache_slot state.f_control.f_receive_cache sequence target_slot);
  assert
    (material_slots_match
      state.f_control.f_receive_cache state.f_receive_slots);
  assert
    (target_cached.f_sequence ==
      cache_entry state.f_control.f_receive_cache (v target_slot));
  assert (target_cached.f_sequence == sequence);
  assert
    (last_cached.f_sequence ==
      cache_entry state.f_control.f_receive_cache (v last_slot));
  assert (last_slot <. state.f_control.f_receive_cache.f_len);
  assert
    ((cast (last_slot <: u8) <: usize) <.
      v_RECEIVE_CACHE_CAPACITY);
  assert
    (impl_RatchetState__receive_key_at state.f_control last_slot ==
      Core_models.Option.Option_Some
        (cache_entry state.f_control.f_receive_cache (v last_slot)));
  assert
    (impl_RatchetState__receive_key_at state.f_control last_slot ==
      Core_models.Option.Option_Some last_cached.f_sequence);
  let finished =
    finish_receive_with_removal state.f_control sequence target_slot true in
  finish_receive_with_removal_success_shape
    state.f_control sequence target_slot;
  finish_receive_with_removal_preserves_validity
    state.f_control sequence target_slot true;
  finish_receive_with_removal_preserves_other_physical_slot
    state.f_control sequence target_slot;
  match finished.f_removal with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some removal ->
      assert (removal.f_target_slot == target_slot);
      assert
        (v removal.f_last_slot + 1 ==
          cache_len state.f_control.f_receive_cache);
      assert (removal.f_last_slot == last_slot);
      let slots' =
        material_slots_after_swap_remove
          state.f_receive_slots target_slot last_slot last_cached in
      material_slots_after_swap_remove_is_exact
        state.f_receive_slots target_slot last_slot last_cached;
      material_slots_after_swap_remove_matches
        state.f_control.f_receive_cache
        finished.f_state.f_receive_cache
        state.f_receive_slots
        target_slot
        last_slot
        last_cached;
      let with_slots = { state with f_receive_slots = slots' } in
      let expected = { with_slots with f_control = finished.f_state } in
      assert (finished.f_disposition == ReceiveDisposition_Consumed);
      assert
        (finished.f_removal ==
          Core_models.Option.Option_Some removal);
      refined_finish_receive_success_computes_swap
        state
        sequence
        target_slot
        last_slot
        target_cached
        last_cached
        removal;
      assert
        (refined_finish_receive state sequence true ==
          (expected, ReceiveDisposition_Consumed));
      assert (valid_refined expected);
      ()

/// Every refined completion outcome preserves the logical/material invariant.
let refined_finish_receive_preserves_validity
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material { valid_refined state })
    (sequence:u64)
    (authenticated:bool)
  : Lemma
      (let state', _ = refined_finish_receive state sequence authenticated in
       valid_refined state')
  =
  let slot = lookup_receive_key state.f_control sequence in
  match slot with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some target_slot ->
      lookup_receive_key_sound state.f_control sequence;
      if authenticated then
        let last_slot = state.f_control.f_receive_cache.f_len -! mk_u8 1 in
        match refined_slot_value state.f_receive_slots (v target_slot),
              refined_slot_value state.f_receive_slots (v last_slot) with
        | Core_models.Option.Option_Some target_cached,
          Core_models.Option.Option_Some last_cached ->
            refined_finish_receive_success_is_exact_swap_removal
              state sequence target_slot last_slot target_cached last_cached
        | _ -> ()
      else ()

/// Missing and retained completion are identity transitions, while consumption moves a whole canonically derived record; therefore every completion outcome preserves reachability.
let refined_finish_receive_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (sequence:u64)
    (authenticated:bool)
  : Lemma
      (let state', _ =
         refined_finish_receive state sequence authenticated in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state')
  =
  refined_finish_receive_preserves_validity state sequence authenticated;
  refined_finish_receive_neutral_outcomes_preserve_full_state
    state sequence authenticated;
  let slot = lookup_receive_key state.f_control sequence in
  match slot with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some target_slot ->
      lookup_receive_key_sound state.f_control sequence;
      if authenticated then
        let last_slot = state.f_control.f_receive_cache.f_len -! mk_u8 1 in
        match refined_slot_value state.f_receive_slots (v target_slot),
              refined_slot_value state.f_receive_slots (v last_slot) with
        | Core_models.Option.Option_Some target_cached,
          Core_models.Option.Option_Some last_cached ->
            refined_finish_receive_success_is_exact_swap_removal
              state sequence target_slot last_slot target_cached last_cached;
            finish_receive_with_removal_success_shape
              state.f_control sequence target_slot;
            cached_materials_after_swap_remove_are_derived
              #v_ReceiveChain #v_Material
              initial_receive receive_step state.f_receive_slots
              target_slot last_slot last_cached
        | _ -> ()
      else ()

/// If the opaque open callback returns `None` for the exact material and sequence selected after admission, the public operation returns that complete admitted state unchanged.
let refined_open_none_retains_selected_material
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext:Type0)
    (state admitted:t_RefinedRatchet
      v_SendChain v_ReceiveChain v_Material)
    (target sequence:u64)
    (material:v_Material)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (context:v_Context)
    (open_callback:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (requires
        (refined_advance_receive_until state target step ==
           (admitted, Core_models.Option.Option_Some sequence) /\
         refined_receive_key admitted sequence ==
           Core_models.Option.Option_Some material /\
         open_callback material sequence context ==
           Core_models.Option.Option_None))
      (ensures
        (refined_open_and_finish state target step context open_callback ==
          (admitted, Core_models.Option.Option_None)))
  = ()

/// If the opaque open callback returns `Some` for the exact selected material, sequence, and context, the public operation returns that plaintext only with the state produced by consuming that same sequence.
let refined_open_some_consumes_selected_material
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext:Type0)
    (state admitted consumed:t_RefinedRatchet
      v_SendChain v_ReceiveChain v_Material)
    (target sequence:u64)
    (material:v_Material)
    (plaintext:v_Plaintext)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (context:v_Context)
    (open_callback:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (requires
        (refined_advance_receive_until state target step ==
           (admitted, Core_models.Option.Option_Some sequence) /\
         refined_receive_key admitted sequence ==
           Core_models.Option.Option_Some material /\
         open_callback material sequence context ==
           Core_models.Option.Option_Some plaintext /\
         refined_finish_receive admitted sequence true ==
           (consumed, ReceiveDisposition_Consumed)))
      (ensures
        (refined_open_and_finish state target step context open_callback ==
          (consumed, Core_models.Option.Option_Some plaintext)))
  = ()

/// The public open operation preserves the complete refined invariant across admission rejection, callback failure retention, and callback success consumption.
let refined_open_and_finish_preserves_validity
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext:Type0)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       valid_refined state })
    (target:u64)
    (step:v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material)
    (context:v_Context)
    (open_callback:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (let final_state, _ =
         refined_open_and_finish state target step context open_callback in
       valid_refined final_state)
  =
  refined_advance_receive_until_executes_plan state target step;
  let admitted, reached =
    refined_advance_receive_until state target step in
  assert (valid_refined admitted);
  match reached with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some sequence ->
      match refined_receive_key admitted sequence with
      | Core_models.Option.Option_None -> ()
      | Core_models.Option.Option_Some material ->
          match open_callback material sequence context with
          | Core_models.Option.Option_None -> ()
          | Core_models.Option.Option_Some _ ->
              refined_finish_receive_preserves_validity
                admitted sequence true

/// The public open transaction preserves reachability across admission rejection, failed-open retention, and authenticated consumption.
let refined_open_and_finish_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material {
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step state })
    (target:u64)
    (context:v_Context)
    (open_callback:v_Material -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (let final_state, _ =
         refined_open_and_finish
           state target receive_step context open_callback in
       reachable #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step final_state)
  =
  refined_advance_receive_until_preserves_reachability
    initial_send initial_receive send_step receive_step state target;
  let admitted, reached =
    refined_advance_receive_until state target receive_step in
  assert
    (reachable #v_SendChain #v_ReceiveChain #v_Material
      initial_send initial_receive send_step receive_step admitted);
  match reached with
  | Core_models.Option.Option_None -> ()
  | Core_models.Option.Option_Some sequence ->
      match refined_receive_key admitted sequence with
      | Core_models.Option.Option_None -> ()
      | Core_models.Option.Option_Some material ->
          match open_callback material sequence context with
          | Core_models.Option.Option_None -> ()
          | Core_models.Option.Option_Some _ ->
              refined_finish_receive_preserves_reachability
                initial_send initial_receive send_step receive_step
                admitted sequence true

/// The production-facing open wrapper preserves concrete reachability across rejection, retention, and authenticated consumption while selecting the core-fixed step internally.
let concrete_open_and_finish_preserves_reachability
    (#v_Context #v_Plaintext:Type0)
    (initial_send initial_receive:t_ConcreteRatchetChain)
    (state:t_ConcreteRatchetKernel {
       concrete_reachable initial_send initial_receive state })
    (target:u64)
    (context:v_Context)
    (open_callback:t_RatchetMaterial -> u64 -> v_Context ->
      Core_models.Option.t_Option v_Plaintext)
  : Lemma
      (let final_state, _ =
         concrete_open_and_finish state target context open_callback in
       concrete_reachable initial_send initial_receive final_state)
  =
  refined_open_and_finish_preserves_reachability
    #t_ConcreteRatchetChain #t_ConcreteRatchetChain #t_RatchetMaterial
    #v_Context #v_Plaintext initial_send initial_receive
    concrete_ratchet_step concrete_ratchet_step state.f_refined target
    context open_callback

/// The empty refined restoration builder starts valid for arbitrary counters and chain values.
let start_refined_restore_is_valid
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (send_sequence receive_sequence:u64)
    (send_chain:v_SendChain)
    (receive_chain:v_ReceiveChain)
  : Lemma
      (valid_refined_restore
        (start_refined_restore #v_SendChain #v_ReceiveChain #v_Material
          send_sequence receive_sequence send_chain receive_chain))
  = start_restore_is_valid send_sequence receive_sequence;
    empty_material_slots_are_none #v_Material

/// Starting restoration establishes the conditional reachability builder only when trusted persistence provenance supplies live chains matching the fixed initial chains and counters.
let start_refined_restore_is_reachable
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (send_sequence receive_sequence:u64)
    (send_chain:v_SendChain)
    (receive_chain:v_ReceiveChain)
  : Lemma
      (requires
        (send_chain ==
           chain_after #v_SendChain #v_Material
             initial_send send_step (v send_sequence) /\
         receive_chain ==
           chain_after #v_ReceiveChain #v_Material
             initial_receive receive_step (v receive_sequence)))
      (ensures
        (reachable_restore #v_SendChain #v_ReceiveChain #v_Material
          initial_send initial_receive send_step receive_step
          (start_refined_restore #v_SendChain #v_ReceiveChain #v_Material
            send_sequence receive_sequence send_chain receive_chain)))
  =
  start_refined_restore_is_valid #v_SendChain #v_ReceiveChain #v_Material
    send_sequence receive_sequence send_chain receive_chain;
  empty_material_slots_are_derived #v_ReceiveChain #v_Material
    initial_receive receive_step

/// Refined restoration either rejects without changing the builder or appends the supplied sequence and exact material together while preserving all invariants.
let refined_restore_receive_key_is_atomic
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (restore:t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material {
       valid_refined_restore restore })
    (sequence:u64)
    (material:v_Material)
  : Lemma
      (let restore', accepted =
         refined_restore_receive_key restore sequence material in
       if accepted then
         valid_refined_restore restore' /\
         restore'.f_send_chain == restore.f_send_chain /\
         restore'.f_receive_chain == restore.f_receive_chain /\
         cache_len restore'.f_logical.f_state.f_receive_cache ==
           cache_len restore.f_logical.f_state.f_receive_cache + 1 /\
         packed_prefix_unchanged
           restore.f_logical.f_state.f_receive_cache
           restore'.f_logical.f_state.f_receive_cache
           restore.f_receive_slots
           restore'.f_receive_slots /\
         (exists (slot:u8{v slot < 50}).
            v slot == cache_len restore.f_logical.f_state.f_receive_cache /\
            cache_slot
              restore'.f_logical.f_state.f_receive_cache sequence slot /\
            refined_slot_value restore'.f_receive_slots (v slot) ==
              Core_models.Option.Option_Some
                ({ f_sequence = sequence; f_material = material } <:
                  t_CachedReceiveKey v_Material))
       else restore' == restore)
  = restore_receive_key_with_slot_success_shape restore.f_logical sequence;
    restore_receive_key_with_slot_preserves_validity restore.f_logical sequence

/// Restoration append preserves conditional reachability only when trusted persistence provenance supplies the canonical material for the appended sequence.
let refined_restore_receive_key_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (restore:t_RefinedRatchetRestore
      v_SendChain v_ReceiveChain v_Material {
       reachable_restore #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step restore })
    (sequence:u64 { v sequence > 0 })
    (material:v_Material {
       material == material_at #v_ReceiveChain #v_Material
         initial_receive receive_step (v sequence) })
  : Lemma
      (let restore', _ =
         refined_restore_receive_key restore sequence material in
       reachable_restore #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step restore')
  =
  refined_restore_receive_key_is_atomic restore sequence material;
  let restore', accepted =
    refined_restore_receive_key restore sequence material in
  if accepted then
    let slot:(i:nat{i < 50}) =
      cache_len restore.f_logical.f_state.f_receive_cache in
    assert
      (refined_slot_value restore'.f_receive_slots slot ==
        Core_models.Option.Option_Some
          ({ f_sequence = sequence; f_material = material } <:
            t_CachedReceiveKey v_Material));
    cached_materials_after_append_are_derived
      #v_ReceiveChain #v_Material
      initial_receive receive_step
      restore.f_logical.f_state.f_receive_cache
      restore'.f_logical.f_state.f_receive_cache
      restore.f_receive_slots restore'.f_receive_slots
      sequence material slot
  else ()

/// Finishing a valid refined restoration publishes its logical state, chains, and material slots as one valid refined value.
let finish_refined_restore_is_valid
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (restore:t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material {
       valid_refined_restore restore })
  : Lemma
      (let state = finish_refined_restore restore in
       valid_refined state /\
       state.f_control == finish_restore restore.f_logical /\
       state.f_send_chain == restore.f_send_chain /\
       state.f_receive_chain == restore.f_receive_chain /\
       state.f_receive_slots == restore.f_receive_slots)
  = finish_restore_is_valid restore.f_logical

/// Finishing a conditionally reachable restoration publishes a reachable state without weakening any chain or cached-material derivation clause.
let finish_refined_restore_preserves_reachability
    (#v_SendChain #v_ReceiveChain #v_Material:Type0)
    (initial_send:v_SendChain)
    (initial_receive:v_ReceiveChain)
    (send_step:v_SendChain -> t_RatchetStep v_SendChain v_Material)
    (receive_step:v_ReceiveChain ->
      t_RatchetStep v_ReceiveChain v_Material)
    (restore:t_RefinedRatchetRestore
      v_SendChain v_ReceiveChain v_Material {
       reachable_restore #v_SendChain #v_ReceiveChain #v_Material
         initial_send initial_receive send_step receive_step restore })
  : Lemma
      (reachable #v_SendChain #v_ReceiveChain #v_Material
        initial_send initial_receive send_step receive_step
        (finish_refined_restore restore))
  = finish_refined_restore_is_valid restore

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
