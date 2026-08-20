module Beaconcrypt_core.Ratchet.Control
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Maximum number of outstanding receive keys admitted by the ratchet.
let v_RATCHET_MAX_GAP: u64 = mk_u64 50

/// Physical capacity of the logical receive-key cache.
let v_RECEIVE_CACHE_CAPACITY: usize = cast (v_RATCHET_MAX_GAP <: u64) <: usize

/// Opaque fixed-capacity cache of logical receive-key sequence numbers.
/// Its representation is public to the hax/F* proof boundary, while private
/// fields prevent Rust callers from constructing states that bypass validation.
type t_SequenceCache = {
  f_entries:t_Array u64 (mk_usize 50);
  f_len:u8
}

let impl_SequenceCache__empty (_: Prims.unit) : t_SequenceCache =
  { f_entries = Rust_primitives.Hax.repeat (mk_u64 0) (mk_usize 50); f_len = mk_u8 0 }
  <:
  t_SequenceCache

let impl_SequenceCache__append (self: t_SequenceCache) (sequence: u64)
    : Core_models.Option.t_Option (t_SequenceCache & u8) =
  if sequence =. mk_u64 0 || (cast (self.f_len <: u8) <: usize) >=. v_RECEIVE_CACHE_CAPACITY
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_SequenceCache & u8)
  else
    let slot:u8 = self.f_len in
    let entries:t_Array u64 (mk_usize 50) = self.f_entries in
    let entries:t_Array u64 (mk_usize 50) =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize entries
        (cast (slot <: u8) <: usize)
        sequence
    in
    Core_models.Option.Option_Some
    (({ f_entries = entries; f_len = slot +! mk_u8 1 } <: t_SequenceCache), slot
      <:
      (t_SequenceCache & u8))
    <:
    Core_models.Option.t_Option (t_SequenceCache & u8)

let impl_SequenceCache__entry (self: t_SequenceCache) (slot: u8) : Core_models.Option.t_Option u64 =
  let slot_index:usize = cast (slot <: u8) <: usize in
  if slot <. self.f_len && slot_index <. v_RECEIVE_CACHE_CAPACITY
  then
    Core_models.Option.Option_Some self.f_entries.[ slot_index ] <: Core_models.Option.t_Option u64
  else Core_models.Option.Option_None <: Core_models.Option.t_Option u64

/// Pure protocol state for one peer's symmetric ratchet.
/// Cryptographic chain state and concrete message-key bytes stay outside this type.
/// [`crate::ratchet::RefinedRatchet`] pairs sequences with concrete material.
type t_RatchetState = {
  f_send_sequence:u64;
  f_receive_sequence:u64;
  f_receive_cache:t_SequenceCache
}

/// Construct a state with counters but no outstanding receive keys.
let impl_RatchetState__from_counters (send_sequence receive_sequence: u64) : t_RatchetState =
  {
    f_send_sequence = send_sequence;
    f_receive_sequence = receive_sequence;
    f_receive_cache = impl_SequenceCache__empty ()
  }
  <:
  t_RatchetState

/// Construct a state with no receive history or cached receive keys.
let impl_RatchetState__new (send_sequence: u64) : t_RatchetState =
  impl_RatchetState__from_counters send_sequence (mk_u64 0)

let impl_RatchetState__send_sequence (self: t_RatchetState) : u64 = self.f_send_sequence

let impl_RatchetState__receive_sequence (self: t_RatchetState) : u64 = self.f_receive_sequence

let impl_RatchetState__receive_cache_len (self: t_RatchetState) : u8 = self.f_receive_cache.f_len

/// Return the logical receive-key sequence stored in `slot`.
let impl_RatchetState__receive_key_at (self: t_RatchetState) (slot: u8)
    : Core_models.Option.t_Option u64 = impl_SequenceCache__entry self.f_receive_cache slot

/// One-use logical capability paired with concrete send material by the refined kernel.
type t_SendKey = {
  f_sequence:u64;
  f_available:bool
}

let impl_SendKey__unavailable (_: Prims.unit) : t_SendKey =
  { f_sequence = mk_u64 0; f_available = false } <: t_SendKey

let impl_SendKey__sequence (self: t_SendKey) : Core_models.Option.t_Option u64 =
  if self.f_available
  then Core_models.Option.Option_Some self.f_sequence <: Core_models.Option.t_Option u64
  else Core_models.Option.Option_None <: Core_models.Option.t_Option u64

let impl_SendKey__is_available (self: t_SendKey) : bool = self.f_available

/// Result of attempting to allocate the next sending sequence number.
type t_SendAdvance = {
  f_state:t_RatchetState;
  f_sequence:Core_models.Option.t_Option u64;
  f_key:t_SendKey
}

/// Advance the sending sequence once, unless its `u64` counter is exhausted.
/// The returned key is a low-level logical capability. [`refined_advance_send`]
/// pairs it with the concrete material returned by the opaque step for the same
/// sequence and requires that pair to be finished after its one use.
let advance_send (state: t_RatchetState) : t_SendAdvance =
  if state.f_send_sequence =. Core_models.Num.impl_u64__MAX
  then
    {
      f_state = state;
      f_sequence = Core_models.Option.Option_None <: Core_models.Option.t_Option u64;
      f_key = impl_SendKey__unavailable ()
    }
    <:
    t_SendAdvance
  else
    let next:u64 = state.f_send_sequence +! mk_u64 1 in
    let key:t_SendKey = { f_sequence = next; f_available = true } <: t_SendKey in
    {
      f_state = { state with f_send_sequence = next } <: t_RatchetState;
      f_sequence = Core_models.Option.Option_Some next <: Core_models.Option.t_Option u64;
      f_key = key
    }
    <:
    t_SendAdvance

/// Result of consuming a logical send-key capability.
type t_SendFinish = {
  f_key:t_SendKey;
  f_consumed:bool
}

/// Consume a send key exactly once.
/// The refined kernel performs this transition after both successful and failed
/// encryption, matching beaconcrypt's existing one-use send-key policy.
let finish_send (key: t_SendKey) : t_SendFinish =
  if key.f_available
  then
    { f_key = { f_sequence = key.f_sequence; f_available = false } <: t_SendKey; f_consumed = true }
    <:
    t_SendFinish
  else { f_key = key; f_consumed = false } <: t_SendFinish

/// Admission plan for a receive sequence.
/// `sequence == None` is a state-neutral rejection. A zero derivation count
/// deliberately preserves the current low-level behavior for old, consumed,
/// and zero sequences: a later key lookup decides whether the key exists.
type t_ReceivePlan = {
  f_sequence:Core_models.Option.t_Option u64;
  f_derivations:u64
}

/// Decide whether `target` can be reached without exceeding the receive gap or
/// the total outstanding-key capacity.
let plan_receive_until (state: t_RatchetState) (target: u64) : t_ReceivePlan =
  if target <=. state.f_receive_sequence
  then
    {
      f_sequence = Core_models.Option.Option_Some target <: Core_models.Option.t_Option u64;
      f_derivations = mk_u64 0
    }
    <:
    t_ReceivePlan
  else
    let derivations:u64 = target -! state.f_receive_sequence in
    let cached:u64 = cast (state.f_receive_cache.f_len <: u8) <: u64 in
    if derivations >. v_RATCHET_MAX_GAP || cached >. (v_RATCHET_MAX_GAP -! derivations <: u64)
    then
      {
        f_sequence = Core_models.Option.Option_None <: Core_models.Option.t_Option u64;
        f_derivations = mk_u64 0
      }
      <:
      t_ReceivePlan
    else
      {
        f_sequence = Core_models.Option.Option_Some target <: Core_models.Option.t_Option u64;
        f_derivations = derivations
      }
      <:
      t_ReceivePlan

/// Result of deriving one logical receive key.
type t_ReceiveAdvance = {
  f_state:t_RatchetState;
  f_sequence:Core_models.Option.t_Option u64;
  f_slot:Core_models.Option.t_Option u8
}

/// Advance the receive chain by exactly one key.
/// The refined executor calls this exactly `ReceivePlan::derivations` times and
/// binds one opaque step output to each successful logical advance. Exhaustion
/// and a full cache are state-neutral.
let advance_receive (state: t_RatchetState) : t_ReceiveAdvance =
  if state.f_receive_sequence =. Core_models.Num.impl_u64__MAX
  then
    {
      f_state = state;
      f_sequence = Core_models.Option.Option_None <: Core_models.Option.t_Option u64;
      f_slot = Core_models.Option.Option_None <: Core_models.Option.t_Option u8
    }
    <:
    t_ReceiveAdvance
  else
    let next:u64 = state.f_receive_sequence +! mk_u64 1 in
    match
      impl_SequenceCache__append state.f_receive_cache next
      <:
      Core_models.Option.t_Option (t_SequenceCache & u8)
    with
    | Core_models.Option.Option_Some (receive_cache, slot) ->
      {
        f_state
        =
        { state with f_receive_sequence = next; f_receive_cache = receive_cache } <: t_RatchetState;
        f_sequence = Core_models.Option.Option_Some next <: Core_models.Option.t_Option u64;
        f_slot = Core_models.Option.Option_Some slot <: Core_models.Option.t_Option u8
      }
      <:
      t_ReceiveAdvance
    | _ ->
      {
        f_state = state;
        f_sequence = Core_models.Option.Option_None <: Core_models.Option.t_Option u64;
        f_slot = Core_models.Option.Option_None <: Core_models.Option.t_Option u8
      }
      <:
      t_ReceiveAdvance

/// Outcome of authenticating a cached receive key.
type t_ReceiveDisposition =
  | ReceiveDisposition_Missing : t_ReceiveDisposition
  | ReceiveDisposition_Retained : t_ReceiveDisposition
  | ReceiveDisposition_Consumed : t_ReceiveDisposition

/// Result of completing a receive attempt.
type t_ReceiveFinish = {
  f_state:t_RatchetState;
  f_disposition:t_ReceiveDisposition
}

/// Physical swap-removal indices selected by the logical receive transition.
type t_ReceiveRemoval = {
  f_target_slot:u8;
  f_last_slot:u8
}

/// Logical completion result plus the exact concrete removal operation.
type t_ReceiveFinishWithRemoval = {
  f_state:t_RatchetState;
  f_disposition:t_ReceiveDisposition;
  f_removal:Core_models.Option.t_Option t_ReceiveRemoval
}

/// Complete a receive attempt and return the physical swap-removal plan.
/// Missing or retained keys return no plan and leave `state` unchanged. A
/// consumed key returns the target slot and the old final active slot.
let finish_receive_with_removal
      (state: t_RatchetState)
      (target: u64)
      (slot: u8)
      (authenticated: bool)
    : t_ReceiveFinishWithRemoval =
  let len:u8 = state.f_receive_cache.f_len in
  let len_index:usize = cast (len <: u8) <: usize in
  let slot_index:usize = cast (slot <: u8) <: usize in
  if
    len_index >. v_RECEIVE_CACHE_CAPACITY || slot_index >=. len_index ||
    ~.((state.f_receive_cache.f_entries.[ slot_index ] <: u64) =. target <: bool)
  then
    {
      f_state = state;
      f_disposition = ReceiveDisposition_Missing <: t_ReceiveDisposition;
      f_removal = Core_models.Option.Option_None <: Core_models.Option.t_Option t_ReceiveRemoval
    }
    <:
    t_ReceiveFinishWithRemoval
  else
    if ~.authenticated
    then
      {
        f_state = state;
        f_disposition = ReceiveDisposition_Retained <: t_ReceiveDisposition;
        f_removal = Core_models.Option.Option_None <: Core_models.Option.t_Option t_ReceiveRemoval
      }
      <:
      t_ReceiveFinishWithRemoval
    else
      let last_slot:u8 = len -! mk_u8 1 in
      let entries:t_Array u64 (mk_usize 50) = state.f_receive_cache.f_entries in
      let entries:t_Array u64 (mk_usize 50) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize entries
          slot_index
          (entries.[ cast (last_slot <: u8) <: usize ] <: u64)
      in
      let entries:t_Array u64 (mk_usize 50) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize entries
          (cast (last_slot <: u8) <: usize)
          (mk_u64 0)
      in
      {
        f_state
        =
        {
          state with
          f_receive_cache = { f_entries = entries; f_len = last_slot } <: t_SequenceCache
        }
        <:
        t_RatchetState;
        f_disposition = ReceiveDisposition_Consumed <: t_ReceiveDisposition;
        f_removal
        =
        Core_models.Option.Option_Some
        ({ f_target_slot = slot; f_last_slot = last_slot } <: t_ReceiveRemoval)
        <:
        Core_models.Option.t_Option t_ReceiveRemoval
      }
      <:
      t_ReceiveFinishWithRemoval

/// Complete authentication for a receive key identified by both slot and
/// sequence.
/// Requiring both values prevents a stale slot from consuming a different key.
/// Removal uses a visible fixed-array swap, avoiding assumed collection models
/// in the prover backend.
let finish_receive (state: t_RatchetState) (target: u64) (slot: u8) (authenticated: bool)
    : t_ReceiveFinish =
  let finished:t_ReceiveFinishWithRemoval =
    finish_receive_with_removal state target slot authenticated
  in
  { f_state = finished.f_state; f_disposition = finished.f_disposition } <: t_ReceiveFinish

/// Builder for restoring a ratchet from a sorted list of cached sequences.
/// This typestate prevents callers from manufacturing an invalid `RatchetState`.
/// [`crate::ratchet::RefinedRatchetRestore`] additionally binds concrete material.
type t_RatchetRestore = {
  f_state:t_RatchetState;
  f_last_sequence:u64
}

let start_restore (send_sequence receive_sequence: u64) : t_RatchetRestore =
  {
    f_state = impl_RatchetState__from_counters send_sequence receive_sequence;
    f_last_sequence = mk_u64 0
  }
  <:
  t_RatchetRestore

/// One checked persistence-restoration append and its allocated slot.
type t_ReceiveRestoreStep = {
  f_restore:t_RatchetRestore;
  f_slot:u8
}

/// Append one sorted receive sequence during restoration and return its slot.
let restore_receive_key_with_slot (restore: t_RatchetRestore) (sequence: u64)
    : Core_models.Option.t_Option t_ReceiveRestoreStep =
  if
    sequence =. mk_u64 0 || sequence >. restore.f_state.f_receive_sequence ||
    sequence <=. restore.f_last_sequence
  then Core_models.Option.Option_None <: Core_models.Option.t_Option t_ReceiveRestoreStep
  else
    match
      impl_SequenceCache__append restore.f_state.f_receive_cache sequence
      <:
      Core_models.Option.t_Option (t_SequenceCache & u8)
    with
    | Core_models.Option.Option_Some value ->
      let (receive_cache: t_SequenceCache), (slot: u8) = value in
      Core_models.Option.Option_Some
      ({
          f_restore
          =
          {
            f_state = { restore.f_state with f_receive_cache = receive_cache } <: t_RatchetState;
            f_last_sequence = sequence
          }
          <:
          t_RatchetRestore;
          f_slot = slot
        }
        <:
        t_ReceiveRestoreStep)
      <:
      Core_models.Option.t_Option t_ReceiveRestoreStep
    | Core_models.Option.Option_None  ->
      Core_models.Option.Option_None <: Core_models.Option.t_Option t_ReceiveRestoreStep

let restore_receive_key (restore: t_RatchetRestore) (sequence: u64)
    : Core_models.Option.t_Option t_RatchetRestore =
  Core_models.Option.impl__map #t_ReceiveRestoreStep
    #t_RatchetRestore
    #(t_ReceiveRestoreStep -> t_RatchetRestore)
    (restore_receive_key_with_slot restore sequence
      <:
      Core_models.Option.t_Option t_ReceiveRestoreStep)
    (fun step ->
        let step:t_ReceiveRestoreStep = step in
        step.f_restore)

let finish_restore (restore: t_RatchetRestore) : t_RatchetState = restore.f_state

/// Ratchet state associated with one peer identifier.
type t_PeerRatchetState = {
  f_peer_id:u64;
  f_ratchet:t_RatchetState
}

/// Commit the result of any pure ratchet transition only to the selected peer.
/// Compatibility proofs use this pointwise operation to state that applying a
/// replacement over a uniquely keyed peer map leaves every other peer unchanged.
let replace_ratchet_for_peer
      (requested_peer: u64)
      (peer: t_PeerRatchetState)
      (replacement: t_RatchetState)
    : t_PeerRatchetState =
  if ~.(requested_peer =. peer.f_peer_id <: bool)
  then peer
  else { f_peer_id = peer.f_peer_id; f_ratchet = replacement } <: t_PeerRatchetState

/// Result of applying a send transition pointwise to a peer.
type t_PeerSendAdvance = {
  f_peer:t_PeerRatchetState;
  f_sequence:Core_models.Option.t_Option u64;
  f_key:t_SendKey
}

/// Advance only the peer whose identifier matches `requested_peer`.
/// Applying this function pointwise to a uniquely keyed peer map gives the
/// frame rule: every non-selected peer is returned byte-for-byte unchanged.
let advance_send_for_peer (requested_peer: u64) (peer: t_PeerRatchetState) : t_PeerSendAdvance =
  if ~.(requested_peer =. peer.f_peer_id <: bool)
  then
    {
      f_peer = peer;
      f_sequence = Core_models.Option.Option_None <: Core_models.Option.t_Option u64;
      f_key = impl_SendKey__unavailable ()
    }
    <:
    t_PeerSendAdvance
  else
    let advanced:t_SendAdvance = advance_send peer.f_ratchet in
    {
      f_peer = replace_ratchet_for_peer requested_peer peer advanced.f_state;
      f_sequence = advanced.f_sequence;
      f_key = advanced.f_key
    }
    <:
    t_PeerSendAdvance

/// Return the physical slot currently containing `sequence`.
/// The bounded scan is iterative so stack consumption is independent of
/// `RECEIVE_CACHE_CAPACITY`. The explicit remaining counter is retained as the
/// extraction-visible termination measure.
let rec lookup_receive_key_from (state: t_RatchetState) (sequence: u64) (slot remaining: u8)
    : Prims.Tot (Core_models.Option.t_Option u8)
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option u8
  else
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. v_RECEIVE_CACHE_CAPACITY || slot >=. state.f_receive_cache.f_len
    then Core_models.Option.Option_None <: Core_models.Option.t_Option u8
    else
      if (state.f_receive_cache.f_entries.[ slot_index ] <: u64) =. sequence
      then Core_models.Option.Option_Some slot <: Core_models.Option.t_Option u8
      else
        lookup_receive_key_from state sequence (slot +! mk_u8 1 <: u8) (remaining -! mk_u8 1 <: u8)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let lookup_receive_key_from_stops_at_capacity
      (state: t_RatchetState)
      (sequence: u64)
      (slot remaining: u8)
    : Prims.Pure Prims.unit
      (requires remaining >. mk_u8 0 && (cast (slot <: u8) <: usize) >=. v_RECEIVE_CACHE_CAPACITY)
      (ensures
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          (lookup_receive_key_from state sequence slot remaining <: Core_models.Option.t_Option u8) =.
          (Core_models.Option.Option_None <: Core_models.Option.t_Option u8)) = ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let lookup_receive_key_from_stops_at_len
      (state: t_RatchetState)
      (sequence: u64)
      (slot remaining: u8)
    : Prims.Pure Prims.unit
      (requires
        remaining >. mk_u8 0 && (cast (slot <: u8) <: usize) <. v_RECEIVE_CACHE_CAPACITY &&
        slot >=. state.f_receive_cache.f_len)
      (ensures
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          (lookup_receive_key_from state sequence slot remaining <: Core_models.Option.t_Option u8) =.
          (Core_models.Option.Option_None <: Core_models.Option.t_Option u8)) = ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let lookup_receive_key_from_matches (state: t_RatchetState) (sequence: u64) (slot remaining: u8)
    : Prims.Pure Prims.unit
      (requires
        remaining >. mk_u8 0 && (cast (slot <: u8) <: usize) <. v_RECEIVE_CACHE_CAPACITY &&
        slot <. state.f_receive_cache.f_len &&
        (state.f_receive_cache.f_entries.[ cast (slot <: u8) <: usize ] <: u64) =. sequence)
      (ensures
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          (lookup_receive_key_from state sequence slot remaining <: Core_models.Option.t_Option u8) =.
          (Core_models.Option.Option_Some slot <: Core_models.Option.t_Option u8)) = ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let lookup_receive_key_from_advances (state: t_RatchetState) (sequence: u64) (slot remaining: u8)
    : Prims.Pure Prims.unit
      (requires
        remaining >. mk_u8 0 && (cast (slot <: u8) <: usize) <. v_RECEIVE_CACHE_CAPACITY &&
        slot <. state.f_receive_cache.f_len &&
        (state.f_receive_cache.f_entries.[ cast (slot <: u8) <: usize ] <: u64) <>. sequence)
      (ensures
        fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          (lookup_receive_key_from state sequence slot remaining <: Core_models.Option.t_Option u8) =.
          (lookup_receive_key_from state
              sequence
              (slot +! mk_u8 1 <: u8)
              (remaining -! mk_u8 1 <: u8)
            <:
            Core_models.Option.t_Option u8)) = ()

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let lookup_receive_key (state: t_RatchetState) (sequence: u64)
    : Prims.Pure (Core_models.Option.t_Option u8)
      Prims.l_True
      (ensures
        fun result ->
          let result:Core_models.Option.t_Option u8 = result in
          result =.
          (lookup_receive_key_from state
              sequence
              (mk_u8 0)
              (cast (v_RECEIVE_CACHE_CAPACITY <: usize) <: u8)
            <:
            Core_models.Option.t_Option u8)) =
  let slot:u8 = mk_u8 0 in
  let remaining:u8 = cast (v_RECEIVE_CACHE_CAPACITY <: usize) <: u8 in
  let found:Core_models.Option.t_Option u8 =
    Core_models.Option.Option_None <: Core_models.Option.t_Option u8
  in
  let (found: Core_models.Option.t_Option u8), (remaining: u8), (slot: u8) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (found: Core_models.Option.t_Option u8), (remaining: u8), (slot: u8) = temp_0_ in
          b2t
          (match found <: Core_models.Option.t_Option u8 with
            | Core_models.Option.Option_Some found_slot ->
              (remaining =. mk_u8 0 <: bool) &&
              ((Core_models.Option.Option_Some found_slot <: Core_models.Option.t_Option u8) =.
                (lookup_receive_key_from state
                    sequence
                    (mk_u8 0)
                    (cast (v_RECEIVE_CACHE_CAPACITY <: usize) <: u8)
                  <:
                  Core_models.Option.t_Option u8)
                <:
                bool)
            | Core_models.Option.Option_None  ->
              (lookup_receive_key_from state sequence slot remaining
                <:
                Core_models.Option.t_Option u8) =.
              (lookup_receive_key_from state
                  sequence
                  (mk_u8 0)
                  (cast (v_RECEIVE_CACHE_CAPACITY <: usize) <: u8)
                <:
                Core_models.Option.t_Option u8)
              <:
              bool))
      (fun temp_0_ ->
          let (found: Core_models.Option.t_Option u8), (remaining: u8), (slot: u8) = temp_0_ in
          remaining >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let (found: Core_models.Option.t_Option u8), (remaining: u8), (slot: u8) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (cast (remaining <: u8) <: usize)
          <:
          Hax_lib.Int.t_Int)
      (found, remaining, slot <: (Core_models.Option.t_Option u8 & u8 & u8))
      (fun temp_0_ ->
          let (found: Core_models.Option.t_Option u8), (remaining: u8), (slot: u8) = temp_0_ in
          let slot_index:usize = cast (slot <: u8) <: usize in
          if slot_index >=. v_RECEIVE_CACHE_CAPACITY
          then
            let _:Prims.unit =
              lookup_receive_key_from_stops_at_capacity state sequence slot remaining
            in
            let remaining:u8 = mk_u8 0 in
            found, remaining, slot <: (Core_models.Option.t_Option u8 & u8 & u8)
          else
            if slot >=. state.f_receive_cache.f_len
            then
              let _:Prims.unit =
                lookup_receive_key_from_stops_at_len state sequence slot remaining
              in
              let remaining:u8 = mk_u8 0 in
              found, remaining, slot <: (Core_models.Option.t_Option u8 & u8 & u8)
            else
              if (state.f_receive_cache.f_entries.[ slot_index ] <: u64) =. sequence
              then
                let _:Prims.unit = lookup_receive_key_from_matches state sequence slot remaining in
                let found:Core_models.Option.t_Option u8 =
                  Core_models.Option.Option_Some slot <: Core_models.Option.t_Option u8
                in
                let remaining:u8 = mk_u8 0 in
                found, remaining, slot <: (Core_models.Option.t_Option u8 & u8 & u8)
              else
                let _:Prims.unit = lookup_receive_key_from_advances state sequence slot remaining in
                let slot:u8 = slot +! mk_u8 1 in
                let remaining:u8 = remaining -! mk_u8 1 in
                found, remaining, slot <: (Core_models.Option.t_Option u8 & u8 & u8))
  in
  found

#pop-options
