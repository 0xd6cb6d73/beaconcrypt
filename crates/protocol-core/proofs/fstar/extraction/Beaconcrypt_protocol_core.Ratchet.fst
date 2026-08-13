module Beaconcrypt_protocol_core.Ratchet
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Maximum number of outstanding receive keys admitted by the ratchet.
let v_RATCHET_MAX_GAP: u64 = mk_u64 50

/// Physical capacity of the logical receive-key cache.
let v_RECEIVE_CACHE_CAPACITY: usize = cast (v_RATCHET_MAX_GAP <: u64) <: usize

/// Fixed width of every symmetric-ratchet root and chain value.
let v_RATCHET_CHAIN_SIZE: usize = mk_usize 32

let v_SYM_RATCHET_INFO: t_Array u8 (mk_usize 41) =
  let list =
    [
      mk_u8 83; mk_u8 121; mk_u8 109; mk_u8 82; mk_u8 97; mk_u8 116; mk_u8 99; mk_u8 104; mk_u8 101;
      mk_u8 116; mk_u8 95; mk_u8 72; mk_u8 75; mk_u8 68; mk_u8 70; mk_u8 95; mk_u8 83; mk_u8 72;
      mk_u8 65; mk_u8 45; mk_u8 53; mk_u8 49; mk_u8 50; mk_u8 95; mk_u8 67; mk_u8 72; mk_u8 65;
      mk_u8 67; mk_u8 72; mk_u8 65; mk_u8 50; mk_u8 48; mk_u8 95; mk_u8 80; mk_u8 79; mk_u8 76;
      mk_u8 89; mk_u8 49; mk_u8 51; mk_u8 48; mk_u8 53
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 41);
  Rust_primitives.Hax.array_of_list 41 list

/// Fixed-width symmetric-ratchet chain bytes owned by the extracted boundary.
type t_RatchetChain = { f_bytes:t_Array u8 (mk_usize 32) }

let impl_RatchetChain__from_bytes (bytes: t_Array u8 (mk_usize 32)) : t_RatchetChain =
  { f_bytes = bytes } <: t_RatchetChain

let impl_RatchetChain__as_bytes (self: t_RatchetChain) : t_Array u8 (mk_usize 32) = self.f_bytes

let impl_RatchetChain__into_bytes (self: t_RatchetChain) : t_Array u8 (mk_usize 32) = self.f_bytes

/// Fixed-width symmetric-ratchet message-key bytes owned by the extracted boundary.
type t_RatchetKey = { f_bytes:t_Array u8 (mk_usize 32) }

let impl_RatchetKey__as_bytes (self: t_RatchetKey) : t_Array u8 (mk_usize 32) = self.f_bytes

let impl_RatchetKey__into_bytes (self: t_RatchetKey) : t_Array u8 (mk_usize 32) = self.f_bytes

/// Fixed-width symmetric-ratchet AEAD nonce bytes owned by the extracted boundary.
type t_RatchetNonce = { f_bytes:t_Array u8 (mk_usize 12) }

let impl_RatchetNonce__as_bytes (self: t_RatchetNonce) : t_Array u8 (mk_usize 12) = self.f_bytes

let impl_RatchetNonce__into_bytes (self: t_RatchetNonce) : t_Array u8 (mk_usize 12) = self.f_bytes

/// Fixed-width key and nonce produced by one symmetric-ratchet step.
type t_RatchetMaterial = {
  f_key:t_RatchetKey;
  f_nonce:t_RatchetNonce
}

let impl_RatchetMaterial__key (self: t_RatchetMaterial) : t_RatchetKey = self.f_key

let impl_RatchetMaterial__nonce (self: t_RatchetMaterial) : t_RatchetNonce = self.f_nonce

/// Core-owned invocation of the symmetric-ratchet KDF domain.
/// Both fields are private so an executor can read but cannot alter the exact
/// input or protocol label selected by the core transition that created it.
type t_SymmetricRatchetKdfRequest = {
  f_input:t_Array u8 (mk_usize 32);
  f_info:t_Array u8 (mk_usize 41)
}

let impl_SymmetricRatchetKdfRequest__new (input: t_Array u8 (mk_usize 32))
    : t_SymmetricRatchetKdfRequest =
  { f_input = input; f_info = v_SYM_RATCHET_INFO } <: t_SymmetricRatchetKdfRequest

/// Proof-visible owned partition of one symmetric-ratchet HKDF expansion.
type t_RatchetKdfOutput = {
  f_key:t_RatchetKey;
  f_next_chain:t_RatchetChain;
  f_nonce:t_RatchetNonce
}

let impl_RatchetKdfOutput__key (self: t_RatchetKdfOutput) : t_RatchetKey = self.f_key

let impl_RatchetKdfOutput__next_chain (self: t_RatchetKdfOutput) : t_RatchetChain =
  self.f_next_chain

let impl_RatchetKdfOutput__nonce (self: t_RatchetKdfOutput) : t_RatchetNonce = self.f_nonce

/// Split `key || next_chain || nonce` into fixed-width values at the protocol's exact offsets.
let split_ratchet_kdf_output (output: t_Array u8 (mk_usize 76)) : t_RatchetKdfOutput =
  let key:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let key:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      key
      (output.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = mk_usize 32
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let next_chain:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let next_chain:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      next_chain
      (output.[ {
            Core_models.Ops.Range.f_start = mk_usize 32;
            Core_models.Ops.Range.f_end = mk_usize 64
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let nonce:t_Array u8 (mk_usize 12) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 12) in
  let nonce:t_Array u8 (mk_usize 12) =
    Core_models.Slice.impl__copy_from_slice #u8
      nonce
      (output.[ {
            Core_models.Ops.Range.f_start = mk_usize 64;
            Core_models.Ops.Range.f_end = mk_usize 76
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  {
    f_key = { f_bytes = key } <: t_RatchetKey;
    f_next_chain = { f_bytes = next_chain } <: t_RatchetChain;
    f_nonce = { f_bytes = nonce } <: t_RatchetNonce
  }
  <:
  t_RatchetKdfOutput

noeq

/// A concrete chain binds its fixed-width bytes to the sole KDF executor that
/// is carried through every later step. The fields stay private so callers
/// cannot replace the executor while retaining the same logical kernel.
type t_ConcreteRatchetChain = {
  f_chain:t_RatchetChain;
  f_kdf:t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)
}

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
/// Cryptographic chain state and concrete message-key bytes deliberately stay
/// outside this low-level type. [`RefinedRatchet`] binds each cached sequence to
/// exactly one concrete material value in the shared kernel.
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
    (state.f_receive_cache.f_entries.[ slot_index ] <: u64) <>. target
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
/// Keeping restoration as a typestate prevents callers from manufacturing an
/// invalid `RatchetState`. [`RefinedRatchetRestore`] extends it so persistence
/// can append each sorted logical sequence and its concrete material atomically.
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
    | Core_models.Option.Option_Some (receive_cache, slot) ->
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

/// One opaque ratchet-step result.
/// The shared kernel treats both fields parametrically.
/// The concrete extracted adapter [`derive_ratchet_step`] constructs them from one fixed-output opaque KDF call.
/// Logical tests may construct arbitrary values through this type.
type t_RatchetStep (v_Chain: Type0) (v_Material: Type0) = {
  f_chain:v_Chain;
  f_material:v_Material
}

let impl_RatchetKdfOutput__into_step (self: t_RatchetKdfOutput)
    : t_RatchetStep t_RatchetChain t_RatchetMaterial =
  {
    f_chain = self.f_next_chain;
    f_material = { f_key = self.f_key; f_nonce = self.f_nonce } <: t_RatchetMaterial
  }
  <:
  t_RatchetStep t_RatchetChain t_RatchetMaterial

/// Apply the sole opaque ratchet primitive to the exact old chain and interpret its fixed output.
/// The primitive's complete production-facing type is `old 32-byte chain -> 76-byte output`.
/// Label selection and HKDF details are private to that domain-specific primitive.
/// Input selection, output size, partitioning, and fixed-width construction are owned here.
let derive_ratchet_step
      (old_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_RatchetStep t_RatchetChain t_RatchetMaterial =
  let request:t_SymmetricRatchetKdfRequest =
    impl_SymmetricRatchetKdfRequest__new (impl_RatchetChain__as_bytes old_chain
        <:
        t_Array u8 (mk_usize 32))
  in
  let output:t_Array u8 (mk_usize 76) = kdf request in
  impl_RatchetKdfOutput__into_step (split_ratchet_kdf_output output <: t_RatchetKdfOutput)

/// Apply the executor bound into `old_chain` to a core-constructed request and
/// carry that same executor into the returned next chain.
let concrete_ratchet_step (old_chain: t_ConcreteRatchetChain)
    : t_RatchetStep t_ConcreteRatchetChain t_RatchetMaterial =
  let stepped:t_RatchetStep t_RatchetChain t_RatchetMaterial =
    derive_ratchet_step old_chain.f_chain old_chain.f_kdf
  in
  {
    f_chain = { f_chain = stepped.f_chain; f_kdf = old_chain.f_kdf } <: t_ConcreteRatchetChain;
    f_material = stepped.f_material
  }
  <:
  t_RatchetStep t_ConcreteRatchetChain t_RatchetMaterial

/// Concrete receive material sealed together with the logical sequence that
/// caused the kernel to store it.
/// Private fields prevent adapters from manufacturing or retagging cached
/// material independently of the checked receive and restoration transitions.
type t_CachedReceiveKey (v_Material: Type0) = {
  f_sequence:u64;
  f_material:v_Material
}

let empty_material_slots (#v_Material: Type0) (_: Prims.unit)
    : t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) =
  let list =
    [
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material);
      Core_models.Option.Option_None <: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 50);
  Rust_primitives.Hax.array_of_list 50 list

/// Ratchet control state refined by the concrete chain states and receive-key
/// material governed by that control state.
/// The concrete types remain generic so hax/F* can prove the bookkeeping for
/// arbitrary opaque HKDF inputs and outputs. Each concrete receive value is
/// sealed with its sequence, and private fields ensure Rust callers can only
/// construct and mutate that correspondence through this kernel.
type t_RefinedRatchet (v_SendChain: Type0) (v_ReceiveChain: Type0) (v_Material: Type0) = {
  f_control:t_RatchetState;
  f_send_chain:v_SendChain;
  f_receive_chain:v_ReceiveChain;
  f_receive_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    (mk_usize 50)
}

/// Construct a refined ratchet with arbitrary counters and no cached receive
/// material. This is also useful for checked exhaustion fixtures.
let impl_10__from_counters
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (send_sequence receive_sequence: u64)
      (send_chain: v_SendChain)
      (receive_chain: v_ReceiveChain)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  {
    f_control = impl_RatchetState__from_counters send_sequence receive_sequence;
    f_send_chain = send_chain;
    f_receive_chain = receive_chain;
    f_receive_slots = empty_material_slots #v_Material ()
  }
  <:
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

/// Construct a fresh refined ratchet with empty counters and receive slots.
let impl_10__new
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (send_chain: v_SendChain)
      (receive_chain: v_ReceiveChain)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  impl_10__from_counters #v_SendChain
    #v_ReceiveChain
    #v_Material
    (mk_u64 0)
    (mk_u64 0)
    send_chain
    receive_chain

let impl_10__send_sequence
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u64 = impl_RatchetState__send_sequence self.f_control

let impl_10__receive_sequence
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u64 = impl_RatchetState__receive_sequence self.f_control

let impl_10__receive_cache_len
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u8 = impl_RatchetState__receive_cache_len self.f_control

let impl_10__send_chain
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : v_SendChain = self.f_send_chain

let impl_10__receive_chain
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : v_ReceiveChain = self.f_receive_chain

/// Return the logical sequence and concrete material paired in one active
/// physical slot.
let impl_10__receive_entry_at
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (slot: u8)
    : Core_models.Option.t_Option (u64 & v_Material) =
  match
    impl_RatchetState__receive_key_at self.f_control slot <: Core_models.Option.t_Option u64
  with
  | Core_models.Option.Option_Some sequence ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. v_RECEIVE_CACHE_CAPACITY
    then Core_models.Option.Option_None <: Core_models.Option.t_Option (u64 & v_Material)
    else
      (match
          Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
            (self.f_receive_slots.[ slot_index ]
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
        with
        | Core_models.Option.Option_Some cached ->
          if cached.f_sequence <>. sequence
          then Core_models.Option.Option_None <: Core_models.Option.t_Option (u64 & v_Material)
          else
            Core_models.Option.Option_Some
            (cached.f_sequence, cached.f_material <: (u64 & v_Material))
            <:
            Core_models.Option.t_Option (u64 & v_Material)
        | Core_models.Option.Option_None  ->
          Core_models.Option.Option_None <: Core_models.Option.t_Option (u64 & v_Material))
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (u64 & v_Material)

/// A kernel-private concrete send key paired with its logical one-use capability.
/// This token is deliberately neither `Copy` nor `Clone`, and it never crosses
/// the public kernel boundary. [`refined_seal_next`] lends its material to the
/// opaque sealing callback and consumes the complete token before returning.
type t_RefinedSendKey (v_Material: Type0) = {
  f_logical:t_SendKey;
  f_material:v_Material
}

let impl_11__sequence (#v_Material: Type0) (self: t_RefinedSendKey v_Material)
    : Core_models.Option.t_Option u64 = impl_SendKey__sequence self.f_logical

let impl_11__material (#v_Material: Type0) (self: t_RefinedSendKey v_Material) : v_Material =
  self.f_material

/// Advance the send control state and concrete chain with the same opaque step.
/// Exhaustion is neutral and does not invoke `step`. Success publishes the new
/// chain and counter together and returns the exact step material beside the
/// logical capability for the allocated sequence.
let refined_advance_send
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (step: (v_SendChain -> t_RatchetStep v_SendChain v_Material))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option (t_RefinedSendKey v_Material)) =
  let advanced:t_SendAdvance = advance_send state.f_control in
  match advanced.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    if
      (impl_SendKey__sequence advanced.f_key <: Core_models.Option.t_Option u64) <>.
      (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64) ||
      (impl_RatchetState__send_sequence advanced.f_state <: u64) <>. sequence
    then
      state,
      (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_RefinedSendKey v_Material))
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        Core_models.Option.t_Option (t_RefinedSendKey v_Material))
    else
      let stepped:t_RatchetStep v_SendChain v_Material = step state.f_send_chain in
      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
        { state with f_send_chain = stepped.f_chain }
        <:
        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
      in
      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
        { state with f_control = advanced.f_state }
        <:
        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
      in
      let hax_temp_output:Core_models.Option.t_Option (t_RefinedSendKey v_Material) =
        Core_models.Option.Option_Some
        ({ f_logical = advanced.f_key; f_material = stepped.f_material }
          <:
          t_RefinedSendKey v_Material)
        <:
        Core_models.Option.t_Option (t_RefinedSendKey v_Material)
      in
      state, hax_temp_output
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        Core_models.Option.t_Option (t_RefinedSendKey v_Material))
  | Core_models.Option.Option_None  ->
    state,
    (Core_models.Option.Option_None <: Core_models.Option.t_Option (t_RefinedSendKey v_Material))
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option (t_RefinedSendKey v_Material))

/// Consume a concrete/logical send token after its single permitted use.
let refined_finish_send (#v_Material: Type0) (key: t_RefinedSendKey v_Material) : bool =
  let finished:t_SendFinish = finish_send key.f_logical in
  finished.f_consumed && ~.(impl_SendKey__is_available finished.f_key <: bool)

/// Advance the send ratchet and seal with the exact material allocated for the
/// resulting sequence.
/// The opaque callback is the only code outside the kernel that can observe
/// the sequence/material pair. The pair is borrowed only for that call and is
/// consumed before this operation returns, regardless of whether sealing
/// succeeds.
let refined_seal_next
      (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Output: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (step: (v_SendChain -> t_RatchetStep v_SendChain v_Material))
      (context: v_Context)
      (seal: (v_Material -> u64 -> v_Context -> Core_models.Option.t_Option v_Output))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option v_Output
    ) =
  let
  (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
  (out: Core_models.Option.t_Option (t_RefinedSendKey v_Material)) =
    refined_advance_send #v_SendChain #v_ReceiveChain #v_Material state step
  in
  let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
  match out <: Core_models.Option.t_Option (t_RefinedSendKey v_Material) with
  | Core_models.Option.Option_Some key ->
    (match impl_11__sequence #v_Material key <: Core_models.Option.t_Option u64 with
      | Core_models.Option.Option_Some sequence ->
        let output:Core_models.Option.t_Option v_Output =
          seal (impl_11__material #v_Material key) sequence context
        in
        if ~.(refined_finish_send #v_Material key <: bool)
        then
          state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Output)
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
            Core_models.Option.t_Option v_Output)
        else
          let hax_temp_output:Core_models.Option.t_Option v_Output = output in
          state, hax_temp_output
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
            Core_models.Option.t_Option v_Output)
      | _ ->
        let _:bool = refined_finish_send #v_Material key in
        state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Output)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
          Core_models.Option.t_Option v_Output))
  | Core_models.Option.Option_None  ->
    state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Output)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option v_Output)

/// Derive and cache exactly one receive key through the shared refined kernel.
/// Logical admission and slot validation happen before the sole opaque step.
/// Rejection therefore leaves the concrete chain and slots untouched.
let refined_advance_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64) =
  let advanced:t_ReceiveAdvance = advance_receive state.f_control in
  match advanced.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    (match advanced.f_slot <: Core_models.Option.t_Option u8 with
      | Core_models.Option.Option_Some slot ->
        let slot_index:usize = cast (slot <: u8) <: usize in
        if
          (impl_RatchetState__receive_key_at advanced.f_state slot
            <:
            Core_models.Option.t_Option u64) <>.
          (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64) ||
          slot_index >=. v_RECEIVE_CACHE_CAPACITY ||
          Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
            (state.f_receive_slots.[ slot_index ]
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
        then
          state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
        else
          let stepped:t_RatchetStep v_ReceiveChain v_Material = step state.f_receive_chain in
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
            { state with f_receive_chain = stepped.f_chain }
            <:
            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
          in
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
            {
              state with
              f_receive_slots
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
                slot_index
                (Core_models.Option.Option_Some
                  ({ f_sequence = sequence; f_material = stepped.f_material }
                    <:
                    t_CachedReceiveKey v_Material)
                  <:
                  Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
            }
            <:
            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
          in
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
            { state with f_control = advanced.f_state }
            <:
            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
          in
          let hax_temp_output:Core_models.Option.t_Option u64 =
            Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64
          in
          state, hax_temp_output
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
      | Core_models.Option.Option_None  ->
        state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64))
  | Core_models.Option.Option_None  ->
    state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)

noeq

/// Production-specialized ratchet kernel.
/// Both directional chains carry the same private KDF executor, and every
/// public transition below selects [`concrete_ratchet_step`] internally. This
/// removes the generic step callback from the production-facing lifecycle.
type t_ConcreteRatchetKernel = {
  f_refined:t_RefinedRatchet t_ConcreteRatchetChain t_ConcreteRatchetChain t_RatchetMaterial
}

/// Construct a concrete kernel at checked persistence counters.
let impl_ConcreteRatchetKernel__from_counters
      (send_sequence receive_sequence: u64)
      (send_chain receive_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetKernel =
  {
    f_refined
    =
    impl_10__from_counters #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      send_sequence
      receive_sequence
      ({ f_chain = send_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
      ({ f_chain = receive_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
  }
  <:
  t_ConcreteRatchetKernel

/// Construct a fresh concrete kernel and bind one KDF executor for its lifetime.
let impl_ConcreteRatchetKernel__new
      (send_chain receive_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetKernel =
  impl_ConcreteRatchetKernel__from_counters (mk_u64 0) (mk_u64 0) send_chain receive_chain kdf

let impl_ConcreteRatchetKernel__send_sequence (self: t_ConcreteRatchetKernel) : u64 =
  impl_10__send_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_sequence (self: t_ConcreteRatchetKernel) : u64 =
  impl_10__receive_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_cache_len (self: t_ConcreteRatchetKernel) : u8 =
  impl_10__receive_cache_len #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__send_chain (self: t_ConcreteRatchetKernel) : t_RatchetChain =
  self.f_refined.f_send_chain.f_chain

let impl_ConcreteRatchetKernel__receive_chain (self: t_ConcreteRatchetKernel) : t_RatchetChain =
  self.f_refined.f_receive_chain.f_chain

let impl_ConcreteRatchetKernel__receive_entry_at (self: t_ConcreteRatchetKernel) (slot: u8)
    : Core_models.Option.t_Option (u64 & t_RatchetMaterial) =
  impl_10__receive_entry_at #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined
    slot

/// Advance and seal with the core-fixed concrete step and KDF request.
let concrete_seal_next
      (#v_Context #v_Output: Type0)
      (state: t_ConcreteRatchetKernel)
      (context: v_Context)
      (seal: (t_RatchetMaterial -> u64 -> v_Context -> Core_models.Option.t_Option v_Output))
    : (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Output) =
  let
  (tmp0: t_RefinedRatchet t_ConcreteRatchetChain t_ConcreteRatchetChain t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Output) =
    refined_seal_next #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      #v_Context
      #v_Output
      state.f_refined
      concrete_ratchet_step
      context
      seal
  in
  let state:t_ConcreteRatchetKernel = { state with f_refined = tmp0 } <: t_ConcreteRatchetKernel in
  let hax_temp_output:Core_models.Option.t_Option v_Output = out in
  state, hax_temp_output <: (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Output)

/// Checked restoration builder for a complete refined ratchet.
type t_RefinedRatchetRestore (v_SendChain: Type0) (v_ReceiveChain: Type0) (v_Material: Type0) = {
  f_logical:t_RatchetRestore;
  f_send_chain:v_SendChain;
  f_receive_chain:v_ReceiveChain;
  f_receive_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    (mk_usize 50)
}

let start_refined_restore
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (send_sequence receive_sequence: u64)
      (send_chain: v_SendChain)
      (receive_chain: v_ReceiveChain)
    : t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material =
  {
    f_logical = start_restore send_sequence receive_sequence;
    f_send_chain = send_chain;
    f_receive_chain = receive_chain;
    f_receive_slots = empty_material_slots #v_Material ()
  }
  <:
  t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material

/// Restore one sorted logical sequence and its concrete material atomically.
let refined_restore_receive_key
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (restore: t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material)
      (sequence: u64)
      (material: v_Material)
    : (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material & bool) =
  match
    restore_receive_key_with_slot restore.f_logical sequence
    <:
    Core_models.Option.t_Option t_ReceiveRestoreStep
  with
  | Core_models.Option.Option_Some step ->
    let slot_index:usize = cast (step.f_slot <: u8) <: usize in
    if
      slot_index >=. v_RECEIVE_CACHE_CAPACITY ||
      Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
        (restore.f_receive_slots.[ slot_index ]
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    then restore, false <: (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material & bool)
    else
      let restore:t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material =
        {
          restore with
          f_receive_slots
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize restore.f_receive_slots
            slot_index
            (Core_models.Option.Option_Some
              ({ f_sequence = sequence; f_material = material } <: t_CachedReceiveKey v_Material)
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
        }
        <:
        t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material
      in
      let restore:t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material =
        { restore with f_logical = step.f_restore }
        <:
        t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material
      in
      restore, true <: (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material & bool)
  | _ -> restore, false <: (t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material & bool)

let finish_refined_restore
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (restore: t_RefinedRatchetRestore v_SendChain v_ReceiveChain v_Material)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  {
    f_control = finish_restore restore.f_logical;
    f_send_chain = restore.f_send_chain;
    f_receive_chain = restore.f_receive_chain;
    f_receive_slots = restore.f_receive_slots
  }
  <:
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

noeq

/// Checked restoration builder that binds one concrete KDF executor to both
/// directional chains before any restored material can be published.
type t_ConcreteRatchetRestore = {
  f_refined:t_RefinedRatchetRestore t_ConcreteRatchetChain t_ConcreteRatchetChain t_RatchetMaterial
}

let start_concrete_restore
      (send_sequence receive_sequence: u64)
      (send_chain receive_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetRestore =
  {
    f_refined
    =
    start_refined_restore #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      send_sequence
      receive_sequence
      ({ f_chain = send_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
      ({ f_chain = receive_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
  }
  <:
  t_ConcreteRatchetRestore

let concrete_restore_receive_key
      (restore: t_ConcreteRatchetRestore)
      (sequence: u64)
      (material: t_RatchetMaterial)
    : (t_ConcreteRatchetRestore & bool) =
  let
  (tmp0: t_RefinedRatchetRestore t_ConcreteRatchetChain t_ConcreteRatchetChain t_RatchetMaterial),
  (out: bool) =
    refined_restore_receive_key #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      restore.f_refined
      sequence
      material
  in
  let restore:t_ConcreteRatchetRestore =
    { restore with f_refined = tmp0 } <: t_ConcreteRatchetRestore
  in
  let hax_temp_output:bool = out in
  restore, hax_temp_output <: (t_ConcreteRatchetRestore & bool)

let finish_concrete_restore (restore: t_ConcreteRatchetRestore) : t_ConcreteRatchetKernel =
  {
    f_refined
    =
    finish_refined_restore #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      restore.f_refined
  }
  <:
  t_ConcreteRatchetKernel

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
  if requested_peer <>. peer.f_peer_id
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
  if requested_peer <>. peer.f_peer_id
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

let rec lookup_receive_key_from (state: t_RatchetState) (sequence: u64) (slot remaining: u8)
    : Prims.Tot (Core_models.Option.t_Option u8)
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option u8
  else
    if (cast (slot <: u8) <: usize) >=. v_RECEIVE_CACHE_CAPACITY
    then Core_models.Option.Option_None <: Core_models.Option.t_Option u8
    else
      if slot >=. state.f_receive_cache.f_len
      then Core_models.Option.Option_None <: Core_models.Option.t_Option u8
      else
        if (state.f_receive_cache.f_entries.[ cast (slot <: u8) <: usize ] <: u64) =. sequence
        then Core_models.Option.Option_Some slot <: Core_models.Option.t_Option u8
        else
          lookup_receive_key_from state
            sequence
            (slot +! mk_u8 1 <: u8)
            (remaining -! mk_u8 1 <: u8)

let rec refined_receive_slots_are_empty
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (first_slot remaining: u8)
    : Prims.Tot bool
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then true
  else
    let slot_index:usize = cast (first_slot <: u8) <: usize in
    if
      slot_index >=. v_RECEIVE_CACHE_CAPACITY ||
      Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
        (state.f_receive_slots.[ slot_index ]
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    then false
    else
      refined_receive_slots_are_empty #v_SendChain
        #v_ReceiveChain
        #v_Material
        state
        (first_slot +! mk_u8 1 <: u8)
        (remaining -! mk_u8 1 <: u8)

/// Commit an already-preflighted suffix of receive steps.
/// Admission bounds the counter and cache.
/// Preflight proves every append destination vacant.
/// Each internal one-step result is successful.
/// This helper exposes no fallible intermediate result.
let rec refined_execute_receive_steps
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
      (remaining: u8)
    : Prims.Tot (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then state
  else
    let
    (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
    (out: Core_models.Option.t_Option u64) =
      refined_advance_receive #v_SendChain #v_ReceiveChain #v_Material state step
    in
    let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
    let _:Core_models.Option.t_Option u64 = out in
    refined_execute_receive_steps #v_SendChain
      #v_ReceiveChain
      #v_Material
      state
      step
      (remaining -! mk_u8 1 <: u8)

/// Return the physical slot currently containing `sequence`.
let lookup_receive_key (state: t_RatchetState) (sequence: u64) : Core_models.Option.t_Option u8 =
  lookup_receive_key_from state sequence (mk_u8 0) (cast (v_RECEIVE_CACHE_CAPACITY <: usize) <: u8)

/// Plan and execute every receive step needed for `target` inside the kernel.
/// Every destination slot is checked before the first callback.
/// Rejection is therefore neutral.
/// An accepted transaction has no intermediate failure branch.
/// It cannot publish only a prefix of the planned refinement.
let refined_advance_receive_until
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (target: u64)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64) =
  let plan:t_ReceivePlan = plan_receive_until state.f_control target in
  match plan.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some target ->
    if plan.f_derivations >. v_RATCHET_MAX_GAP
    then
      state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
    else
      let remaining:u8 = cast (plan.f_derivations <: u64) <: u8 in
      let first_slot:u8 = impl_RatchetState__receive_cache_len state.f_control in
      if
        ~.(refined_receive_slots_are_empty #v_SendChain
            #v_ReceiveChain
            #v_Material
            state
            first_slot
            remaining
          <:
          bool)
      then
        state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
      else
        let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
          refined_execute_receive_steps #v_SendChain
            #v_ReceiveChain
            #v_Material
            state
            step
            remaining
        in
        let hax_temp_output:Core_models.Option.t_Option u64 =
          Core_models.Option.Option_Some target <: Core_models.Option.t_Option u64
        in
        state, hax_temp_output
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
  | Core_models.Option.Option_None  ->
    state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)

/// Look up concrete receive material only through the verified logical cache.
let refined_receive_key
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (sequence: u64)
    : Core_models.Option.t_Option v_Material =
  match lookup_receive_key state.f_control sequence <: Core_models.Option.t_Option u8 with
  | Core_models.Option.Option_Some slot ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. v_RECEIVE_CACHE_CAPACITY
    then Core_models.Option.Option_None <: Core_models.Option.t_Option v_Material
    else
      (match
          Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
            (state.f_receive_slots.[ slot_index ]
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
        with
        | Core_models.Option.Option_Some cached ->
          if cached.f_sequence <>. sequence
          then Core_models.Option.Option_None <: Core_models.Option.t_Option v_Material
          else
            Core_models.Option.Option_Some cached.f_material
            <:
            Core_models.Option.t_Option v_Material
        | Core_models.Option.Option_None  ->
          Core_models.Option.Option_None <: Core_models.Option.t_Option v_Material)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option v_Material

/// Complete a receive attempt and mutate logical and concrete slots together.
/// Missing and retained outcomes are neutral. Successful authentication applies
/// the core-selected target/last swap-removal internally before publishing the
/// returned control state.
let refined_finish_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (sequence: u64)
      (authenticated: bool)
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition) =
  match lookup_receive_key state.f_control sequence <: Core_models.Option.t_Option u8 with
  | Core_models.Option.Option_Some slot ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. v_RECEIVE_CACHE_CAPACITY
    then
      state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)
    else
      let target_matches:bool =
        match
          Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
            (state.f_receive_slots.[ slot_index ]
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
        with
        | Core_models.Option.Option_Some cached -> cached.f_sequence =. sequence
        | Core_models.Option.Option_None  -> false
      in
      if ~.target_matches
      then
        state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)
      else
        let finished:t_ReceiveFinishWithRemoval =
          finish_receive_with_removal state.f_control sequence slot authenticated
        in
        (match finished.f_disposition <: t_ReceiveDisposition with
          | ReceiveDisposition_Missing  ->
            state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
            <:
            (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)
          | ReceiveDisposition_Retained  ->
            state, (ReceiveDisposition_Retained <: t_ReceiveDisposition)
            <:
            (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)
          | ReceiveDisposition_Consumed  ->
            match finished.f_removal <: Core_models.Option.t_Option t_ReceiveRemoval with
            | Core_models.Option.Option_Some removal ->
              let target_index:usize = cast (removal.f_target_slot <: u8) <: usize in
              let last_index:usize = cast (removal.f_last_slot <: u8) <: usize in
              if
                removal.f_target_slot <>. slot || target_index >=. v_RECEIVE_CACHE_CAPACITY ||
                last_index >=. v_RECEIVE_CACHE_CAPACITY
              then
                state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
                <:
                (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)
              else
                (match
                    impl_RatchetState__receive_key_at state.f_control removal.f_last_slot
                    <:
                    Core_models.Option.t_Option u64
                  with
                  | Core_models.Option.Option_Some last_sequence ->
                    let target_matches:bool =
                      match
                        Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
                          (state.f_receive_slots.[ target_index ]
                            <:
                            Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        <:
                        Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
                      with
                      | Core_models.Option.Option_Some cached -> cached.f_sequence =. sequence
                      | Core_models.Option.Option_None  -> false
                    in
                    let last_matches:bool =
                      match
                        Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
                          (state.f_receive_slots.[ last_index ]
                            <:
                            Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        <:
                        Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
                      with
                      | Core_models.Option.Option_Some cached -> cached.f_sequence =. last_sequence
                      | Core_models.Option.Option_None  -> false
                    in
                    if ~.target_matches || ~.last_matches
                    then
                      state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
                      <:
                      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition
                      )
                    else
                      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                        if target_index =. last_index
                        then
                          let
                          (tmp0: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)),
                          (out: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) =
                            Core_models.Option.impl__take #(t_CachedReceiveKey v_Material)
                              (state.f_receive_slots.[ last_index ]
                                <:
                                Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                          in
                          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                            {
                              state with
                              f_receive_slots
                              =
                              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                                  .f_receive_slots
                                last_index
                                tmp0
                            }
                            <:
                            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
                          in
                          let _:Core_models.Option.t_Option (t_CachedReceiveKey v_Material) = out in
                          state
                        else
                          let
                          (tmp0: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)),
                          (out: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) =
                            Core_models.Option.impl__take #(t_CachedReceiveKey v_Material)
                              (state.f_receive_slots.[ last_index ]
                                <:
                                Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                          in
                          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                            {
                              state with
                              f_receive_slots
                              =
                              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                                  .f_receive_slots
                                last_index
                                tmp0
                            }
                            <:
                            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
                          in
                          let moved:Core_models.Option.t_Option (t_CachedReceiveKey v_Material) =
                            out
                          in
                          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                            {
                              state with
                              f_receive_slots
                              =
                              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
                                  .f_receive_slots
                                target_index
                                moved
                            }
                            <:
                            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
                          in
                          state
                      in
                      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                        { state with f_control = finished.f_state }
                        <:
                        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
                      in
                      state, (ReceiveDisposition_Consumed <: t_ReceiveDisposition)
                      <:
                      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition
                      )
                  | _ ->
                    state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
                    <:
                    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition))
            | _ ->
              state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
              <:
              (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition))
  | _ ->
    state, (ReceiveDisposition_Missing <: t_ReceiveDisposition)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & t_ReceiveDisposition)

/// Select the exact sequence-tagged receive material, try to authenticate and
/// open the supplied frame context, and finish that same attempt atomically.
/// Returning `Some` from the opaque callback consumes the selected material.
/// Returning `None` retains it for retry. Neither raw material nor an
/// independently supplied authentication Boolean crosses this public API.
let refined_open_and_finish
      (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (target: u64)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
      (context: v_Context)
      (v_open: (v_Material -> u64 -> v_Context -> Core_models.Option.t_Option v_Plaintext))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Plaintext) =
  let
  (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
  (out: Core_models.Option.t_Option u64) =
    refined_advance_receive_until #v_SendChain #v_ReceiveChain #v_Material state target step
  in
  let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
  match out <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    (match
        refined_receive_key #v_SendChain #v_ReceiveChain #v_Material state sequence
        <:
        Core_models.Option.t_Option v_Material
      with
      | Core_models.Option.Option_Some material ->
        let opened:Core_models.Option.t_Option v_Plaintext = v_open material sequence context in
        let
        (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
        (hax_temp_output: Core_models.Option.t_Option v_Plaintext) =
          match opened <: Core_models.Option.t_Option v_Plaintext with
          | Core_models.Option.Option_None  ->
            state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
            <:
            (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
              Core_models.Option.t_Option v_Plaintext)
          | Core_models.Option.Option_Some plaintext ->
            let
            (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
            (out: t_ReceiveDisposition) =
              refined_finish_receive #v_SendChain #v_ReceiveChain #v_Material state sequence true
            in
            let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
            match out <: t_ReceiveDisposition with
            | ReceiveDisposition_Consumed  ->
              state,
              (Core_models.Option.Option_Some plaintext <: Core_models.Option.t_Option v_Plaintext)
              <:
              (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                Core_models.Option.t_Option v_Plaintext)
            | ReceiveDisposition_Missing
            | ReceiveDisposition_Retained  ->
              state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
              <:
              (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                Core_models.Option.t_Option v_Plaintext)
        in
        state, hax_temp_output
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
          Core_models.Option.t_Option v_Plaintext)
      | Core_models.Option.Option_None  ->
        state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
          Core_models.Option.t_Option v_Plaintext))
  | Core_models.Option.Option_None  ->
    state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Plaintext)

/// Admit, select, open, and finish with the core-fixed concrete step and KDF request.
let concrete_open_and_finish
      (#v_Context #v_Plaintext: Type0)
      (state: t_ConcreteRatchetKernel)
      (target: u64)
      (context: v_Context)
      (v_open: (t_RatchetMaterial -> u64 -> v_Context -> Core_models.Option.t_Option v_Plaintext))
    : (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext) =
  let
  (tmp0: t_RefinedRatchet t_ConcreteRatchetChain t_ConcreteRatchetChain t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Plaintext) =
    refined_open_and_finish #t_ConcreteRatchetChain #t_ConcreteRatchetChain #t_RatchetMaterial
      #v_Context #v_Plaintext state.f_refined target concrete_ratchet_step context v_open
  in
  let state:t_ConcreteRatchetKernel = { state with f_refined = tmp0 } <: t_ConcreteRatchetKernel in
  let hax_temp_output:Core_models.Option.t_Option v_Plaintext = out in
  state, hax_temp_output <: (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext)
