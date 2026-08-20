module Beaconcrypt_core.Ratchet.Refined
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

friend Beaconcrypt_core.Ratchet.Control

/// One opaque ratchet-step result.
/// The shared kernel treats both fields parametrically.
/// [`crate::ratchet::derive_ratchet_step`] applies the concrete fixed-output KDF.
/// Logical tests may construct arbitrary values through this type.
type t_RatchetStep (v_Chain: Type0) (v_Material: Type0) = {
  f_chain:v_Chain;
  f_material:v_Material
}

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
  f_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState;
  f_send_chain:v_SendChain;
  f_receive_chain:v_ReceiveChain;
  f_receive_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    (mk_usize 50)
}

/// Prevalidated metadata for consuming an already cached receive key.
type t_PreparedCachedReceive = {
  f_sequence:u64;
  f_target_slot:u8;
  f_last_slot:u8;
  f_committed_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState
}

/// Final metadata produced while deriving a future receive into a caller-owned
/// staging buffer.
/// Keeping the fixed-capacity buffer out of this recursive result ensures the
/// Rust implementation has exactly one live staging array regardless of gap.
type t_PreparedFutureTarget (v_ReceiveChain: Type0) (v_Material: Type0) = {
  f_committed_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState;
  f_final_receive_chain:v_ReceiveChain;
  f_target_sequence:u64;
  f_target_material:v_Material;
  f_first_slot:u8;
  f_skipped:u8
}

/// Privately derived future receive delta.
/// The target material is deliberately separate from `staged_slots`, so a
/// successful publication can retain only skipped material while dropping the
/// authenticated target.
type t_PendingReceive (v_ReceiveChain: Type0) (v_Material: Type0) = {
  f_committed_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState;
  f_final_receive_chain:v_ReceiveChain;
  f_staged_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50);
  f_target_sequence:u64;
  f_target_material:v_Material;
  f_first_slot:u8;
  f_skipped:u8
}

/// Kernel-private receive preparation that owns only the delta needed for a
/// successful publication. Neither variant is a live or serializable ratchet.
type t_PreparedReceive (v_ReceiveChain: Type0) (v_Material: Type0) =
  | PreparedReceive_Cached : t_PreparedCachedReceive -> t_PreparedReceive v_ReceiveChain v_Material
  | PreparedReceive_Future : t_PendingReceive v_ReceiveChain v_Material
    -> t_PreparedReceive v_ReceiveChain v_Material

/// Construct a refined ratchet with arbitrary counters and no cached receive
/// material. This is also useful for checked exhaustion fixtures.
let impl__from_counters
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (send_sequence receive_sequence: u64)
      (send_chain: v_SendChain)
      (receive_chain: v_ReceiveChain)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  {
    f_control
    =
    Beaconcrypt_core.Ratchet.Control.impl_RatchetState__from_counters send_sequence receive_sequence;
    f_send_chain = send_chain;
    f_receive_chain = receive_chain;
    f_receive_slots = empty_material_slots #v_Material ()
  }
  <:
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

/// Construct a fresh refined ratchet with empty counters and receive slots.
let impl__new
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (send_chain: v_SendChain)
      (receive_chain: v_ReceiveChain)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  impl__from_counters #v_SendChain
    #v_ReceiveChain
    #v_Material
    (mk_u64 0)
    (mk_u64 0)
    send_chain
    receive_chain

let impl__send_sequence
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u64 = Beaconcrypt_core.Ratchet.Control.impl_RatchetState__send_sequence self.f_control

let impl__receive_sequence
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u64 = Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_sequence self.f_control

let impl__receive_cache_len
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : u8 = Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len self.f_control

let impl__send_chain
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : v_SendChain = self.f_send_chain

let impl__receive_chain
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
    : v_ReceiveChain = self.f_receive_chain

/// Return the logical sequence and concrete material paired in one active
/// physical slot.
let impl__receive_entry_at
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (self: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (slot: u8)
    : Core_models.Option.t_Option (u64 & v_Material) =
  match
    Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at self.f_control slot
    <:
    Core_models.Option.t_Option u64
  with
  | Core_models.Option.Option_Some sequence ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
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
  f_logical:Beaconcrypt_core.Ratchet.Control.t_SendKey;
  f_material:v_Material
}

let impl_1__sequence (#v_Material: Type0) (self: t_RefinedSendKey v_Material)
    : Core_models.Option.t_Option u64 =
  Beaconcrypt_core.Ratchet.Control.impl_SendKey__sequence self.f_logical

let impl_1__material (#v_Material: Type0) (self: t_RefinedSendKey v_Material) : v_Material =
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
  let advanced:Beaconcrypt_core.Ratchet.Control.t_SendAdvance =
    Beaconcrypt_core.Ratchet.Control.advance_send state.f_control
  in
  match advanced.Beaconcrypt_core.Ratchet.Control.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    if
      (Beaconcrypt_core.Ratchet.Control.impl_SendKey__sequence advanced
            .Beaconcrypt_core.Ratchet.Control.f_key
        <:
        Core_models.Option.t_Option u64) <>.
      (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64) ||
      (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__send_sequence advanced
            .Beaconcrypt_core.Ratchet.Control.f_state
        <:
        u64) <>.
      sequence
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
        { state with f_control = advanced.Beaconcrypt_core.Ratchet.Control.f_state }
        <:
        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
      in
      let hax_temp_output:Core_models.Option.t_Option (t_RefinedSendKey v_Material) =
        Core_models.Option.Option_Some
        ({
            f_logical = advanced.Beaconcrypt_core.Ratchet.Control.f_key;
            f_material = stepped.f_material
          }
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
  let finished:Beaconcrypt_core.Ratchet.Control.t_SendFinish =
    Beaconcrypt_core.Ratchet.Control.finish_send key.f_logical
  in
  finished.Beaconcrypt_core.Ratchet.Control.f_consumed &&
  ~.(Beaconcrypt_core.Ratchet.Control.impl_SendKey__is_available finished
        .Beaconcrypt_core.Ratchet.Control.f_key
    <:
    bool)

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
    (match impl_1__sequence #v_Material key <: Core_models.Option.t_Option u64 with
      | Core_models.Option.Option_Some sequence ->
        let output:Core_models.Option.t_Option v_Output =
          seal (impl_1__material #v_Material key) sequence context
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
  let advanced:Beaconcrypt_core.Ratchet.Control.t_ReceiveAdvance =
    Beaconcrypt_core.Ratchet.Control.advance_receive state.f_control
  in
  match advanced.Beaconcrypt_core.Ratchet.Control.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    (match advanced.Beaconcrypt_core.Ratchet.Control.f_slot <: Core_models.Option.t_Option u8 with
      | Core_models.Option.Option_Some slot ->
        let slot_index:usize = cast (slot <: u8) <: usize in
        if
          (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at advanced
                .Beaconcrypt_core.Ratchet.Control.f_state
              slot
            <:
            Core_models.Option.t_Option u64) <>.
          (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64) ||
          slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
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
            { state with f_control = advanced.Beaconcrypt_core.Ratchet.Control.f_state }
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

/// Preflight an existing cached target and compute its successful logical
/// removal without changing the live refined ratchet.
let prepare_cached_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (sequence: u64)
    : Core_models.Option.t_Option t_PreparedCachedReceive =
  match
    Beaconcrypt_core.Ratchet.Control.lookup_receive_key state.f_control sequence
    <:
    Core_models.Option.t_Option u8
  with
  | Core_models.Option.Option_Some target_slot ->
    let target_index:usize = cast (target_slot <: u8) <: usize in
    if target_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then Core_models.Option.Option_None <: Core_models.Option.t_Option t_PreparedCachedReceive
    else
      if
        (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at state.f_control
            target_slot
          <:
          Core_models.Option.t_Option u64) <>.
        (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64)
      then Core_models.Option.Option_None <: Core_models.Option.t_Option t_PreparedCachedReceive
      else
        (match
            Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
              (state.f_receive_slots.[ target_index ]
                <:
                Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
            <:
            Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
          with
          | Core_models.Option.Option_Some target ->
            if target.f_sequence <>. sequence
            then
              Core_models.Option.Option_None <: Core_models.Option.t_Option t_PreparedCachedReceive
            else
              let len:u8 =
                Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len state
                    .f_control
              in
              if len =. mk_u8 0
              then
                Core_models.Option.Option_None
                <:
                Core_models.Option.t_Option t_PreparedCachedReceive
              else
                let last_slot:u8 = len -! mk_u8 1 in
                let last_index:usize = cast (last_slot <: u8) <: usize in
                if last_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
                then
                  Core_models.Option.Option_None
                  <:
                  Core_models.Option.t_Option t_PreparedCachedReceive
                else
                  (match
                      Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at state
                          .f_control
                        last_slot
                      <:
                      Core_models.Option.t_Option u64
                    with
                    | Core_models.Option.Option_Some last_sequence ->
                      (match
                          Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
                            (state.f_receive_slots.[ last_index ]
                              <:
                              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                          <:
                          Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
                        with
                        | Core_models.Option.Option_Some last ->
                          if last.f_sequence <>. last_sequence
                          then
                            Core_models.Option.Option_None
                            <:
                            Core_models.Option.t_Option t_PreparedCachedReceive
                          else
                            let finished:Beaconcrypt_core.Ratchet.Control.t_ReceiveFinishWithRemoval
                            =
                              Beaconcrypt_core.Ratchet.Control.finish_receive_with_removal state
                                  .f_control
                                sequence
                                target_slot
                                true
                            in
                            (match
                                finished.Beaconcrypt_core.Ratchet.Control.f_removal
                                <:
                                Core_models.Option.t_Option
                                Beaconcrypt_core.Ratchet.Control.t_ReceiveRemoval
                              with
                              | Core_models.Option.Option_Some removal ->
                                if
                                  ~.(match
                                      finished.Beaconcrypt_core.Ratchet.Control.f_disposition
                                      <:
                                      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition
                                    with
                                    | Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Consumed  ->
                                      true
                                    | _ -> false)
                                then
                                  Core_models.Option.Option_None
                                  <:
                                  Core_models.Option.t_Option t_PreparedCachedReceive
                                else
                                  if
                                    removal.Beaconcrypt_core.Ratchet.Control.f_target_slot <>.
                                    target_slot
                                  then
                                    Core_models.Option.Option_None
                                    <:
                                    Core_models.Option.t_Option t_PreparedCachedReceive
                                  else
                                    if
                                      removal.Beaconcrypt_core.Ratchet.Control.f_last_slot <>.
                                      last_slot
                                    then
                                      Core_models.Option.Option_None
                                      <:
                                      Core_models.Option.t_Option t_PreparedCachedReceive
                                    else
                                      Core_models.Option.Option_Some
                                      ({
                                          f_sequence = sequence;
                                          f_target_slot = target_slot;
                                          f_last_slot = last_slot;
                                          f_committed_control
                                          =
                                          finished.Beaconcrypt_core.Ratchet.Control.f_state
                                        }
                                        <:
                                        t_PreparedCachedReceive)
                                      <:
                                      Core_models.Option.t_Option t_PreparedCachedReceive
                              | Core_models.Option.Option_None  ->
                                Core_models.Option.Option_None
                                <:
                                Core_models.Option.t_Option t_PreparedCachedReceive)
                        | Core_models.Option.Option_None  ->
                          Core_models.Option.Option_None
                          <:
                          Core_models.Option.t_Option t_PreparedCachedReceive)
                    | Core_models.Option.Option_None  ->
                      Core_models.Option.Option_None
                      <:
                      Core_models.Option.t_Option t_PreparedCachedReceive)
          | Core_models.Option.Option_None  ->
            Core_models.Option.Option_None <: Core_models.Option.t_Option t_PreparedCachedReceive)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option t_PreparedCachedReceive

/// Derive a future target into a private delta without assigning any live
/// chain, slot, or logical control field.
/// The traversal is iterative so its call-stack consumption is independent of
/// the admitted receive gap. Exactly one derived chain and one material value
/// are live for the current iteration, in addition to the caller-owned staging
/// array.
let prepare_future_receive_steps
      (#v_ReceiveChain #v_Material: Type0)
      (entry_chain: v_ReceiveChain)
      (control: Beaconcrypt_core.Ratchet.Control.t_RatchetState)
      (target: u64)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
      (remaining first_slot skipped: u8)
      (staged_slots:
          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
    : Prims.Tot
      (t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
        Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material))
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then
    staged_slots,
    (Core_models.Option.Option_None
      <:
      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material))
    <:
    (t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material))
  else
    let result:Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) =
      Core_models.Option.Option_None
      <:
      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)
    in
    let (current_chain: Core_models.Option.t_Option v_ReceiveChain):Core_models.Option.t_Option
    v_ReceiveChain =
      Core_models.Option.Option_None <: Core_models.Option.t_Option v_ReceiveChain
    in
    let current_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState = control in
    let left:u8 = remaining in
    let skipped_count:u8 = skipped in
    let
    (current_chain: Core_models.Option.t_Option v_ReceiveChain),
    (current_control: Beaconcrypt_core.Ratchet.Control.t_RatchetState),
    (left: u8),
    (result: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)),
    (skipped_count: u8),
    (staged_slots:
      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
      Rust_primitives.Hax.while_loop (fun temp_0_ ->
            let
            (current_chain: Core_models.Option.t_Option v_ReceiveChain),
            (current_control: Beaconcrypt_core.Ratchet.Control.t_RatchetState),
            (left: u8),
            (result: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)),
            (skipped_count: u8),
            (staged_slots:
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
              temp_0_
            in
            true)
        (fun temp_0_ ->
            let
            (current_chain: Core_models.Option.t_Option v_ReceiveChain),
            (current_control: Beaconcrypt_core.Ratchet.Control.t_RatchetState),
            (left: u8),
            (result: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)),
            (skipped_count: u8),
            (staged_slots:
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
              temp_0_
            in
            left >. mk_u8 0 <: bool)
        (fun temp_0_ ->
            let
            (current_chain: Core_models.Option.t_Option v_ReceiveChain),
            (current_control: Beaconcrypt_core.Ratchet.Control.t_RatchetState),
            (left: u8),
            (result: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)),
            (skipped_count: u8),
            (staged_slots:
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
              temp_0_
            in
            Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
        (current_chain, current_control, left, result, skipped_count, staged_slots
          <:
          (Core_models.Option.t_Option v_ReceiveChain &
            Beaconcrypt_core.Ratchet.Control.t_RatchetState &
            u8 &
            Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
            u8 &
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)))
        (fun temp_0_ ->
            let
            (current_chain: Core_models.Option.t_Option v_ReceiveChain),
            (current_control: Beaconcrypt_core.Ratchet.Control.t_RatchetState),
            (left: u8),
            (result: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)),
            (skipped_count: u8),
            (staged_slots:
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
              temp_0_
            in
            let advanced:Beaconcrypt_core.Ratchet.Control.t_ReceiveAdvance =
              Beaconcrypt_core.Ratchet.Control.advance_receive current_control
            in
            match
              advanced.Beaconcrypt_core.Ratchet.Control.f_sequence,
              advanced.Beaconcrypt_core.Ratchet.Control.f_slot
              <:
              (Core_models.Option.t_Option u64 & Core_models.Option.t_Option u8)
            with
            | Core_models.Option.Option_Some sequence, Core_models.Option.Option_Some slot ->
              let slot_index:usize = cast (slot <: u8) <: usize in
              if
                (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at advanced
                      .Beaconcrypt_core.Ratchet.Control.f_state
                    slot
                  <:
                  Core_models.Option.t_Option u64) <>.
                (Core_models.Option.Option_Some sequence <: Core_models.Option.t_Option u64) ||
                slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
                slot_index <>.
                ((cast (first_slot <: u8) <: usize) +! (cast (skipped_count <: u8) <: usize)
                  <:
                  usize) ||
                Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
                  (staged_slots.[ slot_index ]
                    <:
                    Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
              then
                let left:u8 = mk_u8 0 in
                current_chain, current_control, left, result, skipped_count, staged_slots
                <:
                (Core_models.Option.t_Option v_ReceiveChain &
                  Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                  u8 &
                  Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                  u8 &
                  t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                    (mk_usize 50))
              else
                let stepped:t_RatchetStep v_ReceiveChain v_Material =
                  match
                    Core_models.Option.impl__as_ref #v_ReceiveChain current_chain
                    <:
                    Core_models.Option.t_Option v_ReceiveChain
                  with
                  | Core_models.Option.Option_Some chain -> step chain
                  | Core_models.Option.Option_None  -> step entry_chain
                in
                let { f_chain = chain ; f_material = material }:t_RatchetStep v_ReceiveChain
                  v_Material =
                  stepped
                in
                if left =. mk_u8 1
                then
                  if sequence <>. target
                  then
                    let left:u8 = mk_u8 0 in
                    current_chain, current_control, left, result, skipped_count, staged_slots
                    <:
                    (Core_models.Option.t_Option v_ReceiveChain &
                      Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                      u8 &
                      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                      u8 &
                      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        (mk_usize 50))
                  else
                    let finished:Beaconcrypt_core.Ratchet.Control.t_ReceiveFinishWithRemoval =
                      Beaconcrypt_core.Ratchet.Control.finish_receive_with_removal advanced
                          .Beaconcrypt_core.Ratchet.Control.f_state
                        target
                        slot
                        true
                    in
                    match
                      finished.Beaconcrypt_core.Ratchet.Control.f_removal
                      <:
                      Core_models.Option.t_Option Beaconcrypt_core.Ratchet.Control.t_ReceiveRemoval
                    with
                    | Core_models.Option.Option_Some removal ->
                      if
                        ~.(match
                            finished.Beaconcrypt_core.Ratchet.Control.f_disposition
                            <:
                            Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition
                          with
                          | Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Consumed  -> true
                          | _ -> false) ||
                        removal.Beaconcrypt_core.Ratchet.Control.f_target_slot <>. slot ||
                        removal.Beaconcrypt_core.Ratchet.Control.f_last_slot <>. slot
                      then
                        let left:u8 = mk_u8 0 in
                        current_chain, current_control, left, result, skipped_count, staged_slots
                        <:
                        (Core_models.Option.t_Option v_ReceiveChain &
                          Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                          u8 &
                          Core_models.Option.t_Option
                          (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                          u8 &
                          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                            (mk_usize 50))
                      else
                        let result:Core_models.Option.t_Option
                        (t_PreparedFutureTarget v_ReceiveChain v_Material) =
                          Core_models.Option.Option_Some
                          ({
                              f_committed_control
                              =
                              finished.Beaconcrypt_core.Ratchet.Control.f_state;
                              f_final_receive_chain = chain;
                              f_target_sequence = sequence;
                              f_target_material = material;
                              f_first_slot = first_slot;
                              f_skipped = skipped_count
                            }
                            <:
                            t_PreparedFutureTarget v_ReceiveChain v_Material)
                          <:
                          Core_models.Option.t_Option
                          (t_PreparedFutureTarget v_ReceiveChain v_Material)
                        in
                        let left:u8 = mk_u8 0 in
                        current_chain, current_control, left, result, skipped_count, staged_slots
                        <:
                        (Core_models.Option.t_Option v_ReceiveChain &
                          Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                          u8 &
                          Core_models.Option.t_Option
                          (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                          u8 &
                          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                            (mk_usize 50))
                    | Core_models.Option.Option_None  ->
                      current_chain, current_control, mk_u8 0, result, skipped_count, staged_slots
                      <:
                      (Core_models.Option.t_Option v_ReceiveChain &
                        Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                        u8 &
                        Core_models.Option.t_Option
                        (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                        u8 &
                        t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                          (mk_usize 50))
                else
                  if sequence >=. target
                  then
                    let left:u8 = mk_u8 0 in
                    current_chain, current_control, left, result, skipped_count, staged_slots
                    <:
                    (Core_models.Option.t_Option v_ReceiveChain &
                      Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                      u8 &
                      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                      u8 &
                      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        (mk_usize 50))
                  else
                    let staged_slots:t_Array
                      (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) =
                      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize staged_slots
                        slot_index
                        (Core_models.Option.Option_Some
                          ({ f_sequence = sequence; f_material = material }
                            <:
                            t_CachedReceiveKey v_Material)
                          <:
                          Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                    in
                    let current_chain:Core_models.Option.t_Option v_ReceiveChain =
                      Core_models.Option.Option_Some chain
                      <:
                      Core_models.Option.t_Option v_ReceiveChain
                    in
                    let current_control:Beaconcrypt_core.Ratchet.Control.t_RatchetState =
                      advanced.Beaconcrypt_core.Ratchet.Control.f_state
                    in
                    let skipped_count:u8 = skipped_count +! mk_u8 1 in
                    let left:u8 = left -! mk_u8 1 in
                    current_chain, current_control, left, result, skipped_count, staged_slots
                    <:
                    (Core_models.Option.t_Option v_ReceiveChain &
                      Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                      u8 &
                      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                      u8 &
                      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        (mk_usize 50))
            | _ ->
              current_chain, current_control, mk_u8 0, result, skipped_count, staged_slots
              <:
              (Core_models.Option.t_Option v_ReceiveChain &
                Beaconcrypt_core.Ratchet.Control.t_RatchetState &
                u8 &
                Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material) &
                u8 &
                t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
        )
    in
    let hax_temp_output:Core_models.Option.t_Option
    (t_PreparedFutureTarget v_ReceiveChain v_Material) =
      result
    in
    staged_slots, hax_temp_output
    <:
    (t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
      Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material))

/// Publish a prevalidated cached removal with no remaining failure branch.
let publish_cached_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (prepared: t_PreparedCachedReceive)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  let target_index:usize = cast (prepared.f_target_slot <: u8) <: usize in
  let last_index:usize = cast (prepared.f_last_slot <: u8) <: usize in
  if target_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
  then state
  else
    if last_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then state
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
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
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
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
                last_index
                tmp0
            }
            <:
            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
          in
          let moved:Core_models.Option.t_Option (t_CachedReceiveKey v_Material) = out in
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
            {
              state with
              f_receive_slots
              =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
                target_index
                moved
            }
            <:
            t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
          in
          state
      in
      { state with f_control = prepared.f_committed_control }
      <:
      t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

/// Commit an already-preflighted suffix of receive steps.
/// Admission bounds the counter and cache.
/// Preflight proves every append destination vacant.
/// Each internal one-step result is successful.
/// This helper exposes no fallible intermediate result.
let refined_execute_receive_steps
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
      (remaining: u8)
    : Prims.Tot (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  let left:u8 = remaining in
  let (left: u8), (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (left: u8), (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          true)
      (fun temp_0_ ->
          let (left: u8), (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          left >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let (left: u8), (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
      (left, state <: (u8 & t_RefinedRatchet v_SendChain v_ReceiveChain v_Material))
      (fun temp_0_ ->
          let (left: u8), (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          let
          (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
          (out: Core_models.Option.t_Option u64) =
            refined_advance_receive #v_SendChain #v_ReceiveChain #v_Material state step
          in
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
          let _:Core_models.Option.t_Option u64 = out in
          let left:u8 = left -! mk_u8 1 in
          left, state <: (u8 & t_RefinedRatchet v_SendChain v_ReceiveChain v_Material))
  in
  state

/// Look up concrete receive material only through the verified logical cache.
let refined_receive_key
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (sequence: u64)
    : Core_models.Option.t_Option v_Material =
  match
    Beaconcrypt_core.Ratchet.Control.lookup_receive_key state.f_control sequence
    <:
    Core_models.Option.t_Option u8
  with
  | Core_models.Option.Option_Some slot ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
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
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition) =
  match
    Beaconcrypt_core.Ratchet.Control.lookup_receive_key state.f_control sequence
    <:
    Core_models.Option.t_Option u8
  with
  | Core_models.Option.Option_Some slot ->
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then
      state,
      (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
        <:
        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
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
        state,
        (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
          <:
          Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
        <:
        (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
          Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
      else
        let finished:Beaconcrypt_core.Ratchet.Control.t_ReceiveFinishWithRemoval =
          Beaconcrypt_core.Ratchet.Control.finish_receive_with_removal state.f_control
            sequence
            slot
            authenticated
        in
        (match
            finished.Beaconcrypt_core.Ratchet.Control.f_disposition
            <:
            Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition
          with
          | Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing  ->
            state,
            (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
              <:
              Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
            <:
            (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
              Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
          | Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Retained  ->
            state,
            (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Retained
              <:
              Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
            <:
            (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
              Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
          | Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Consumed  ->
            match
              finished.Beaconcrypt_core.Ratchet.Control.f_removal
              <:
              Core_models.Option.t_Option Beaconcrypt_core.Ratchet.Control.t_ReceiveRemoval
            with
            | Core_models.Option.Option_Some removal ->
              let target_index:usize =
                cast (removal.Beaconcrypt_core.Ratchet.Control.f_target_slot <: u8) <: usize
              in
              let last_index:usize =
                cast (removal.Beaconcrypt_core.Ratchet.Control.f_last_slot <: u8) <: usize
              in
              if
                removal.Beaconcrypt_core.Ratchet.Control.f_target_slot <>. slot ||
                target_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
                last_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
              then
                state,
                (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
                  <:
                  Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
                <:
                (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                  Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
              else
                (match
                    Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at state
                        .f_control
                      removal.Beaconcrypt_core.Ratchet.Control.f_last_slot
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
                      state,
                      (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
                        <:
                        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
                      <:
                      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
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
                        { state with f_control = finished.Beaconcrypt_core.Ratchet.Control.f_state }
                        <:
                        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
                      in
                      state,
                      (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Consumed
                        <:
                        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
                      <:
                      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                        Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
                  | _ ->
                    state,
                    (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
                      <:
                      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
                    <:
                    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition))
            | _ ->
              state,
              (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
                <:
                Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
              <:
              (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition))
  | _ ->
    state,
    (Beaconcrypt_core.Ratchet.Control.ReceiveDisposition_Missing
      <:
      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Beaconcrypt_core.Ratchet.Control.t_ReceiveDisposition)

/// Checked restoration builder for a complete refined ratchet.
type t_RefinedRatchetRestore (v_SendChain: Type0) (v_ReceiveChain: Type0) (v_Material: Type0) = {
  f_logical:Beaconcrypt_core.Ratchet.Control.t_RatchetRestore;
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
    f_logical = Beaconcrypt_core.Ratchet.Control.start_restore send_sequence receive_sequence;
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
    Beaconcrypt_core.Ratchet.Control.restore_receive_key_with_slot restore.f_logical sequence
    <:
    Core_models.Option.t_Option Beaconcrypt_core.Ratchet.Control.t_ReceiveRestoreStep
  with
  | Core_models.Option.Option_Some step ->
    let slot_index:usize = cast (step.Beaconcrypt_core.Ratchet.Control.f_slot <: u8) <: usize in
    if
      slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
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
        { restore with f_logical = step.Beaconcrypt_core.Ratchet.Control.f_restore }
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
    f_control = Beaconcrypt_core.Ratchet.Control.finish_restore restore.f_logical;
    f_send_chain = restore.f_send_chain;
    f_receive_chain = restore.f_receive_chain;
    f_receive_slots = restore.f_receive_slots
  }
  <:
  t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

let rec refined_receive_slots_are_empty_from
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
      slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
      Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
        (state.f_receive_slots.[ slot_index ]
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
    then false
    else
      refined_receive_slots_are_empty_from #v_SendChain
        #v_ReceiveChain
        #v_Material
        state
        (first_slot +! mk_u8 1 <: u8)
        (remaining -! mk_u8 1 <: u8)

let rec receive_control_prefix_matches_from
      (entry committed: Beaconcrypt_core.Ratchet.Control.t_RatchetState)
      (slot remaining: u8)
    : Prims.Tot bool
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then true
  else
    if (cast (slot <: u8) <: usize) >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then false
    else
      if
        (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at entry slot
          <:
          Core_models.Option.t_Option u64) <>.
        (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at committed slot
          <:
          Core_models.Option.t_Option u64)
      then false
      else
        receive_control_prefix_matches_from entry
          committed
          (slot +! mk_u8 1 <: u8)
          (remaining -! mk_u8 1 <: u8)

let rec pending_receive_slots_are_valid_from
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (pending: t_PendingReceive v_ReceiveChain v_Material)
      (slot: u8)
      (expected_sequence: u64)
      (remaining: u8)
    : Prims.Tot bool
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then true
  else
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then false
    else
      if
        Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
          (state.f_receive_slots.[ slot_index ]
            <:
            Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      then false
      else
        match
          Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
            (pending.f_staged_slots.[ slot_index ]
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          <:
          Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
        with
        | Core_models.Option.Option_Some staged ->
          let staged:t_CachedReceiveKey v_Material = staged in
          if staged.f_sequence <>. expected_sequence
          then false
          else
            if
              (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at pending
                    .f_committed_control
                  slot
                <:
                Core_models.Option.t_Option u64) <>.
              (Core_models.Option.Option_Some expected_sequence <: Core_models.Option.t_Option u64)
            then false
            else
              if remaining =. mk_u8 1
              then true
              else
                if expected_sequence =. Core_models.Num.impl_u64__MAX
                then false
                else
                  pending_receive_slots_are_valid_from #v_SendChain
                    #v_ReceiveChain
                    #v_Material
                    state
                    pending
                    (slot +! mk_u8 1 <: u8)
                    (expected_sequence +! mk_u64 1 <: u64)
                    (remaining -! mk_u8 1 <: u8)
        | Core_models.Option.Option_None  -> false

let rec publish_future_receive_slots_from
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (staged_slots:
          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
      (slot remaining: u8)
    : Prims.Tot
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  if remaining =. mk_u8 0
  then
    state, staged_slots
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
  else
    let slot_index:usize = cast (slot <: u8) <: usize in
    if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
    then
      state, staged_slots
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
    else
      let
      (tmp0: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)),
      (out: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) =
        Core_models.Option.impl__take #(t_CachedReceiveKey v_Material)
          (staged_slots.[ slot_index ]
            <:
            Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
      in
      let staged_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
        (mk_usize 50) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_usize staged_slots slot_index tmp0
      in
      let moved:Core_models.Option.t_Option (t_CachedReceiveKey v_Material) = out in
      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
        {
          state with
          f_receive_slots
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
            slot_index
            moved
        }
        <:
        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
      in
      publish_future_receive_slots_from #v_SendChain
        #v_ReceiveChain
        #v_Material
        state
        staged_slots
        (slot +! mk_u8 1 <: u8)
        (remaining -! mk_u8 1 <: u8)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let refined_receive_slots_are_empty
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (first_slot remaining: u8)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          result =.
          (refined_receive_slots_are_empty_from #v_SendChain
              #v_ReceiveChain
              #v_Material
              state
              first_slot
              remaining
            <:
            bool)) =
  let slot:u8 = first_slot in
  let left:u8 = remaining in
  let empty:bool = true in
  let (empty: bool), (left: u8), (slot: u8) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (empty: bool), (left: u8), (slot: u8) = temp_0_ in
          b2t
          (match empty <: bool with
            | true ->
              (refined_receive_slots_are_empty_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  slot
                  left
                <:
                bool) =.
              (refined_receive_slots_are_empty_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  first_slot
                  remaining
                <:
                bool)
              <:
              bool
            | false ->
              ~.(refined_receive_slots_are_empty_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  first_slot
                  remaining
                <:
                bool)
              <:
              bool))
      (fun temp_0_ ->
          let (empty: bool), (left: u8), (slot: u8) = temp_0_ in
          left >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let (empty: bool), (left: u8), (slot: u8) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
      (empty, left, slot <: (bool & u8 & u8))
      (fun temp_0_ ->
          let (empty: bool), (left: u8), (slot: u8) = temp_0_ in
          let slot_index:usize = cast (slot <: u8) <: usize in
          if
            slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
            Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
              (state.f_receive_slots.[ slot_index ]
                <:
                Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          then
            let _:Prims.unit =
              Hax_lib.v_assert (~.(refined_receive_slots_are_empty_from #v_SendChain
                      #v_ReceiveChain
                      #v_Material
                      state
                      slot
                      left
                    <:
                    bool)
                  <:
                  bool)
            in
            let empty:bool = false in
            let left:u8 = mk_u8 0 in
            empty, left, slot <: (bool & u8 & u8)
          else
            let _:Prims.unit =
              Hax_lib.v_assert ((refined_receive_slots_are_empty_from #v_SendChain
                      #v_ReceiveChain
                      #v_Material
                      state
                      slot
                      left
                    <:
                    bool) =.
                  (refined_receive_slots_are_empty_from #v_SendChain
                      #v_ReceiveChain
                      #v_Material
                      state
                      (slot +! mk_u8 1 <: u8)
                      (left -! mk_u8 1 <: u8)
                    <:
                    bool)
                  <:
                  bool)
            in
            let slot:u8 = slot +! mk_u8 1 in
            let left:u8 = left -! mk_u8 1 in
            empty, left, slot <: (bool & u8 & u8))
  in
  empty

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let receive_control_prefix_matches
      (entry committed: Beaconcrypt_core.Ratchet.Control.t_RatchetState)
      (slot remaining: u8)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          result =. (receive_control_prefix_matches_from entry committed slot remaining <: bool)) =
  let current_slot:u8 = slot in
  let left:u8 = remaining in
  let matches:bool = true in
  let (current_slot: u8), (left: u8), (matches: bool) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (current_slot: u8), (left: u8), (matches: bool) = temp_0_ in
          b2t
          (match matches <: bool with
            | true ->
              (receive_control_prefix_matches_from entry committed current_slot left <: bool) =.
              (receive_control_prefix_matches_from entry committed slot remaining <: bool)
              <:
              bool
            | false ->
              ~.(receive_control_prefix_matches_from entry committed slot remaining <: bool) <: bool
          ))
      (fun temp_0_ ->
          let (current_slot: u8), (left: u8), (matches: bool) = temp_0_ in
          left >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let (current_slot: u8), (left: u8), (matches: bool) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
      (current_slot, left, matches <: (u8 & u8 & bool))
      (fun temp_0_ ->
          let (current_slot: u8), (left: u8), (matches: bool) = temp_0_ in
          if
            ((cast (current_slot <: u8) <: usize) >=.
              Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
              <:
              bool) ||
            (~.((Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at entry
                    current_slot
                  <:
                  Core_models.Option.t_Option u64) =.
                (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at committed
                    current_slot
                  <:
                  Core_models.Option.t_Option u64)
                <:
                bool)
              <:
              bool)
          then
            let _:Prims.unit =
              Hax_lib.v_assert (~.(receive_control_prefix_matches_from entry
                      committed
                      current_slot
                      left
                    <:
                    bool)
                  <:
                  bool)
            in
            let matches:bool = false in
            let left:u8 = mk_u8 0 in
            current_slot, left, matches <: (u8 & u8 & bool)
          else
            let _:Prims.unit =
              Hax_lib.v_assert ((receive_control_prefix_matches_from entry
                      committed
                      current_slot
                      left
                    <:
                    bool) =.
                  (receive_control_prefix_matches_from entry
                      committed
                      (current_slot +! mk_u8 1 <: u8)
                      (left -! mk_u8 1 <: u8)
                    <:
                    bool)
                  <:
                  bool)
            in
            let current_slot:u8 = current_slot +! mk_u8 1 in
            let left:u8 = left -! mk_u8 1 in
            current_slot, left, matches <: (u8 & u8 & bool))
  in
  matches

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let pending_receive_slots_are_valid
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (pending: t_PendingReceive v_ReceiveChain v_Material)
      (slot: u8)
      (expected_sequence: u64)
      (remaining: u8)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun result ->
          let result:bool = result in
          result =.
          (pending_receive_slots_are_valid_from #v_SendChain
              #v_ReceiveChain
              #v_Material
              state
              pending
              slot
              expected_sequence
              remaining
            <:
            bool)) =
  let current_slot:u8 = slot in
  let expected:u64 = expected_sequence in
  let left:u8 = remaining in
  let valid:bool = true in
  let (current_slot: u8), (expected: u64), (left: u8), (valid: bool) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let (current_slot: u8), (expected: u64), (left: u8), (valid: bool) = temp_0_ in
          b2t
          (match valid <: bool with
            | true ->
              (pending_receive_slots_are_valid_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  pending
                  current_slot
                  expected
                  left
                <:
                bool) =.
              (pending_receive_slots_are_valid_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  pending
                  slot
                  expected_sequence
                  remaining
                <:
                bool)
              <:
              bool
            | false ->
              ~.(pending_receive_slots_are_valid_from #v_SendChain
                  #v_ReceiveChain
                  #v_Material
                  state
                  pending
                  slot
                  expected_sequence
                  remaining
                <:
                bool)
              <:
              bool))
      (fun temp_0_ ->
          let (current_slot: u8), (expected: u64), (left: u8), (valid: bool) = temp_0_ in
          left >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let (current_slot: u8), (expected: u64), (left: u8), (valid: bool) = temp_0_ in
          Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
      (current_slot, expected, left, valid <: (u8 & u64 & u8 & bool))
      (fun temp_0_ ->
          let (current_slot: u8), (expected: u64), (left: u8), (valid: bool) = temp_0_ in
          let slot_index:usize = cast (current_slot <: u8) <: usize in
          if
            slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY ||
            Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
              (state.f_receive_slots.[ slot_index ]
                <:
                Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
          then
            let _:Prims.unit =
              Hax_lib.v_assert (~.(pending_receive_slots_are_valid_from #v_SendChain
                      #v_ReceiveChain
                      #v_Material
                      state
                      pending
                      current_slot
                      expected
                      left
                    <:
                    bool)
                  <:
                  bool)
            in
            let valid:bool = false in
            let left:u8 = mk_u8 0 in
            current_slot, expected, left, valid <: (u8 & u64 & u8 & bool)
          else
            match
              Core_models.Option.impl__as_ref #(t_CachedReceiveKey v_Material)
                (pending.f_staged_slots.[ slot_index ]
                  <:
                  Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
              <:
              Core_models.Option.t_Option (t_CachedReceiveKey v_Material)
            with
            | Core_models.Option.Option_Some staged ->
              if
                ~.(staged.f_sequence =. expected <: bool) ||
                ~.((Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_key_at pending
                        .f_committed_control
                      current_slot
                    <:
                    Core_models.Option.t_Option u64) =.
                  (Core_models.Option.Option_Some expected <: Core_models.Option.t_Option u64)
                  <:
                  bool)
              then
                let _:Prims.unit =
                  Hax_lib.v_assert (~.(pending_receive_slots_are_valid_from #v_SendChain
                          #v_ReceiveChain
                          #v_Material
                          state
                          pending
                          current_slot
                          expected
                          left
                        <:
                        bool)
                      <:
                      bool)
                in
                let valid:bool = false in
                let left:u8 = mk_u8 0 in
                current_slot, expected, left, valid <: (u8 & u64 & u8 & bool)
              else
                if left =. mk_u8 1
                then
                  let _:Prims.unit =
                    Hax_lib.v_assert (pending_receive_slots_are_valid_from #v_SendChain
                          #v_ReceiveChain
                          #v_Material
                          state
                          pending
                          current_slot
                          expected
                          left
                        <:
                        bool)
                  in
                  let left:u8 = mk_u8 0 in
                  current_slot, expected, left, valid <: (u8 & u64 & u8 & bool)
                else
                  if expected =. Core_models.Num.impl_u64__MAX
                  then
                    let _:Prims.unit =
                      Hax_lib.v_assert (~.(pending_receive_slots_are_valid_from #v_SendChain
                              #v_ReceiveChain
                              #v_Material
                              state
                              pending
                              current_slot
                              expected
                              left
                            <:
                            bool)
                          <:
                          bool)
                    in
                    let valid:bool = false in
                    let left:u8 = mk_u8 0 in
                    current_slot, expected, left, valid <: (u8 & u64 & u8 & bool)
                  else
                    let _:Prims.unit =
                      Hax_lib.v_assert ((pending_receive_slots_are_valid_from #v_SendChain
                              #v_ReceiveChain
                              #v_Material
                              state
                              pending
                              current_slot
                              expected
                              left
                            <:
                            bool) =.
                          (pending_receive_slots_are_valid_from #v_SendChain
                              #v_ReceiveChain
                              #v_Material
                              state
                              pending
                              (current_slot +! mk_u8 1 <: u8)
                              (expected +! mk_u64 1 <: u64)
                              (left -! mk_u8 1 <: u8)
                            <:
                            bool)
                          <:
                          bool)
                    in
                    let current_slot:u8 = current_slot +! mk_u8 1 in
                    let expected:u64 = expected +! mk_u64 1 in
                    let left:u8 = left -! mk_u8 1 in
                    current_slot, expected, left, valid <: (u8 & u64 & u8 & bool)
            | Core_models.Option.Option_None  ->
              let _:Prims.unit =
                Hax_lib.v_assert (~.(pending_receive_slots_are_valid_from #v_SendChain
                        #v_ReceiveChain
                        #v_Material
                        state
                        pending
                        current_slot
                        expected
                        left
                      <:
                      bool)
                    <:
                    bool)
              in
              let valid:bool = false in
              let left:u8 = mk_u8 0 in
              current_slot, expected, left, valid <: (u8 & u64 & u8 & bool))
  in
  valid

#pop-options

/// Validate the complete private publication invariant before it can escape
/// preparation. Publication itself can therefore be a total movement phase.
let pending_receive_is_valid
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (pending: t_PendingReceive v_ReceiveChain v_Material)
      (requested: u64)
    : bool =
  let entry_receive_sequence:u64 =
    Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_sequence state.f_control
  in
  if pending.f_target_sequence <>. requested
  then false
  else
    if requested <=. entry_receive_sequence
    then false
    else
      if
        pending.f_first_slot <>.
        (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len state.f_control <: u8
        )
      then false
      else
        if
          (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__send_sequence pending
                .f_committed_control
            <:
            u64) <>.
          (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__send_sequence state.f_control <: u64)
        then false
        else
          if
            (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_sequence pending
                  .f_committed_control
              <:
              u64) <>.
            requested
          then false
          else
            if
              (requested -! entry_receive_sequence <: u64) <>.
              ((cast (pending.f_skipped <: u8) <: u64) +! mk_u64 1 <: u64)
            then false
            else
              if
                Core_models.Option.impl__is_some #u8
                  (Beaconcrypt_core.Ratchet.Control.lookup_receive_key pending.f_committed_control
                      requested
                    <:
                    Core_models.Option.t_Option u8)
              then false
              else
                let committed_len:usize =
                  (cast (pending.f_first_slot <: u8) <: usize) +!
                  (cast (pending.f_skipped <: u8) <: usize)
                in
                if committed_len >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
                then false
                else
                  if
                    (cast (Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len pending
                              .f_committed_control
                          <:
                          u8)
                      <:
                      usize) <>.
                    committed_len
                  then false
                  else
                    if
                      ~.(receive_control_prefix_matches state.f_control
                          pending.f_committed_control
                          (mk_u8 0)
                          pending.f_first_slot
                        <:
                        bool)
                    then false
                    else
                      let target_index:usize = committed_len in
                      if
                        Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
                          (state.f_receive_slots.[ target_index ]
                            <:
                            Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                      then false
                      else
                        if
                          Core_models.Option.impl__is_some #(t_CachedReceiveKey v_Material)
                            (pending.f_staged_slots.[ target_index ]
                              <:
                              Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
                        then false
                        else
                          let expected_first:u64 = entry_receive_sequence +! mk_u64 1 in
                          pending_receive_slots_are_valid #v_SendChain
                            #v_ReceiveChain
                            #v_Material
                            state
                            pending
                            pending.f_first_slot
                            expected_first
                            pending.f_skipped

/// Plan and privately prepare the complete target transaction while leaving
/// the live refined ratchet unchanged.
let prepare_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (target: u64)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
    : Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material) =
  let plan:Beaconcrypt_core.Ratchet.Control.t_ReceivePlan =
    Beaconcrypt_core.Ratchet.Control.plan_receive_until state.f_control target
  in
  match plan.Beaconcrypt_core.Ratchet.Control.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some sequence ->
    if plan.Beaconcrypt_core.Ratchet.Control.f_derivations =. mk_u64 0
    then
      Core_models.Option.impl__map #t_PreparedCachedReceive
        #(t_PreparedReceive v_ReceiveChain v_Material)
        #(t_PreparedCachedReceive -> t_PreparedReceive v_ReceiveChain v_Material)
        (prepare_cached_receive #v_SendChain #v_ReceiveChain #v_Material state sequence
          <:
          Core_models.Option.t_Option t_PreparedCachedReceive)
        PreparedReceive_Cached
    else
      if
        plan.Beaconcrypt_core.Ratchet.Control.f_derivations >.
        Beaconcrypt_core.Ratchet.Control.v_RATCHET_MAX_GAP
      then
        Core_models.Option.Option_None
        <:
        Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)
      else
        let remaining:u8 =
          cast (plan.Beaconcrypt_core.Ratchet.Control.f_derivations <: u64) <: u8
        in
        let first_slot:u8 =
          Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len state.f_control
        in
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
          Core_models.Option.Option_None
          <:
          Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)
        else
          let staged_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
            (mk_usize 50) =
            empty_material_slots #v_Material ()
          in
          let
          (tmp0:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
          (out: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)) =
            prepare_future_receive_steps #v_ReceiveChain #v_Material state.f_receive_chain
              state.f_control sequence step remaining first_slot (mk_u8 0) staged_slots
          in
          let staged_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
            (mk_usize 50) =
            tmp0
          in
          (match
              out <: Core_models.Option.t_Option (t_PreparedFutureTarget v_ReceiveChain v_Material)
            with
            | Core_models.Option.Option_Some
              { f_committed_control = committed_control ;
                f_final_receive_chain = final_receive_chain ;
                f_target_sequence = target_sequence ;
                f_target_material = target_material ;
                f_first_slot = first_slot ;
                f_skipped = skipped } ->
              let pending:t_PendingReceive v_ReceiveChain v_Material =
                {
                  f_committed_control = committed_control;
                  f_final_receive_chain = final_receive_chain;
                  f_staged_slots = staged_slots;
                  f_target_sequence = target_sequence;
                  f_target_material = target_material;
                  f_first_slot = first_slot;
                  f_skipped = skipped
                }
                <:
                t_PendingReceive v_ReceiveChain v_Material
              in
              if
                ~.(pending_receive_is_valid #v_SendChain
                    #v_ReceiveChain
                    #v_Material
                    state
                    pending
                    target
                  <:
                  bool)
              then
                Core_models.Option.Option_None
                <:
                Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)
              else
                Core_models.Option.Option_Some
                (PreparedReceive_Future pending <: t_PreparedReceive v_ReceiveChain v_Material)
                <:
                Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)
            | Core_models.Option.Option_None  ->
              Core_models.Option.Option_None
              <:
              Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material))
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let publish_future_receive_slots
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (staged_slots:
          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
      (slot remaining: u8)
    : Prims.Pure
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let
          (state_future: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
          (staged_slots_future:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
            temp_0_
          in
          let final_state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = state_future in
          let final_staged_slots:t_Array
            (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) =
            staged_slots_future
          in
          publish_future_receive_slots_from state staged_slots slot remaining ==
          (final_state, final_staged_slots))
      (decreases (Rust_primitives.Hax.Int.from_machine remaining <: Hax_lib.Int.t_Int)) =
  let e_reference:
      t_RefinedRatchet v_SendChain v_ReceiveChain v_Material ->
      t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) ->
      u8 ->
      u8
    -> (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
        t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
    publish_future_receive_slots_from
  in
  let (initial_state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material):t_RefinedRatchet
    v_SendChain v_ReceiveChain v_Material =
    state
  in
  let
  (initial_staged_slots:
    t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)):t_Array
    (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) =
    staged_slots
  in
  let current_slot:u8 = slot in
  let left:u8 = remaining in
  let
  (current_slot: u8),
  (left: u8),
  (staged_slots:
    t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
  (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
    Rust_primitives.Hax.while_loop (fun temp_0_ ->
          let
          (current_slot: u8),
          (left: u8),
          (staged_slots:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
          (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          publish_future_receive_slots_from initial_state initial_staged_slots slot remaining ==
          publish_future_receive_slots_from state staged_slots current_slot left)
      (fun temp_0_ ->
          let
          (current_slot: u8),
          (left: u8),
          (staged_slots:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
          (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          left >. mk_u8 0 <: bool)
      (fun temp_0_ ->
          let
          (current_slot: u8),
          (left: u8),
          (staged_slots:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
          (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          Rust_primitives.Hax.Int.from_machine (cast (left <: u8) <: usize) <: Hax_lib.Int.t_Int)
      (current_slot, left, staged_slots, state
        <:
        (u8 & u8 &
          t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
          t_RefinedRatchet v_SendChain v_ReceiveChain v_Material))
      (fun temp_0_ ->
          let
          (current_slot: u8),
          (left: u8),
          (staged_slots:
            t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)),
          (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material) =
            temp_0_
          in
          let slot_index:usize = cast (current_slot <: u8) <: usize in
          if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
          then
            let left:u8 = mk_u8 0 in
            current_slot, left, staged_slots, state
            <:
            (u8 & u8 &
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
              t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
          else
            let
            (tmp0: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)),
            (out: Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) =
              Core_models.Option.impl__take #(t_CachedReceiveKey v_Material)
                (staged_slots.[ slot_index ]
                  <:
                  Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
            in
            let staged_slots:t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material))
              (mk_usize 50) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize staged_slots
                slot_index
                tmp0
            in
            let moved:Core_models.Option.t_Option (t_CachedReceiveKey v_Material) = out in
            let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
              {
                state with
                f_receive_slots
                =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state.f_receive_slots
                  slot_index
                  moved
              }
              <:
              t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
            in
            let current_slot:u8 = current_slot +! mk_u8 1 in
            let left:u8 = left -! mk_u8 1 in
            current_slot, left, staged_slots, state
            <:
            (u8 & u8 &
              t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50) &
              t_RefinedRatchet v_SendChain v_ReceiveChain v_Material))
  in
  state, staged_slots
  <:
  (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
    t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50))

#pop-options

/// Publish a validated future delta. The target material remains in `pending`
/// and is dropped instead of ever entering the live cache.
let publish_future_receive
      (#v_SendChain #v_ReceiveChain #v_Material: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (pending: t_PendingReceive v_ReceiveChain v_Material)
    : t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
  let first_index:usize = cast (pending.f_first_slot <: u8) <: usize in
  let skipped:usize = cast (pending.f_skipped <: u8) <: usize in
  if first_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
  then state
  else
    if
      skipped >=.
      (Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY -! first_index <: usize)
    then state
    else
      let
      (tmp0: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material),
      (tmp1: t_Array (Core_models.Option.t_Option (t_CachedReceiveKey v_Material)) (mk_usize 50)) =
        publish_future_receive_slots #v_SendChain
          #v_ReceiveChain
          #v_Material
          state
          pending.f_staged_slots
          pending.f_first_slot
          pending.f_skipped
      in
      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material = tmp0 in
      let pending:t_PendingReceive v_ReceiveChain v_Material =
        { pending with f_staged_slots = tmp1 } <: t_PendingReceive v_ReceiveChain v_Material
      in
      let _:Prims.unit = () in
      let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
        { state with f_receive_chain = pending.f_final_receive_chain }
        <:
        t_RefinedRatchet v_SendChain v_ReceiveChain v_Material
      in
      { state with f_control = pending.f_committed_control }
      <:
      t_RefinedRatchet v_SendChain v_ReceiveChain v_Material

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
  let plan:Beaconcrypt_core.Ratchet.Control.t_ReceivePlan =
    Beaconcrypt_core.Ratchet.Control.plan_receive_until state.f_control target
  in
  match plan.Beaconcrypt_core.Ratchet.Control.f_sequence <: Core_models.Option.t_Option u64 with
  | Core_models.Option.Option_Some target ->
    if
      plan.Beaconcrypt_core.Ratchet.Control.f_derivations >.
      Beaconcrypt_core.Ratchet.Control.v_RATCHET_MAX_GAP
    then
      state, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
      <:
      (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material & Core_models.Option.t_Option u64)
    else
      let remaining:u8 = cast (plan.Beaconcrypt_core.Ratchet.Control.f_derivations <: u64) <: u8 in
      let first_slot:u8 =
        Beaconcrypt_core.Ratchet.Control.impl_RatchetState__receive_cache_len state.f_control
      in
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

/// Select the exact sequence-tagged receive material, try to authenticate and
/// open the supplied frame context, and finish that same attempt atomically.
/// Returning `Some` from the opaque callback consumes the selected material.
/// Returning `None` preserves the complete entry state. Future derivations are
/// owned by a private pending delta and are published only after the callback
/// succeeds. Neither raw material nor an independently supplied authentication
/// Boolean crosses this public API.
let refined_open_and_finish
      (#v_SendChain #v_ReceiveChain #v_Material #v_Context #v_Plaintext: Type0)
      (state: t_RefinedRatchet v_SendChain v_ReceiveChain v_Material)
      (target: u64)
      (step: (v_ReceiveChain -> t_RatchetStep v_ReceiveChain v_Material))
      (context: v_Context)
      (v_open: (v_Material -> u64 -> v_Context -> Core_models.Option.t_Option v_Plaintext))
    : (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Plaintext) =
  match
    prepare_receive #v_SendChain #v_ReceiveChain #v_Material state target step
    <:
    Core_models.Option.t_Option (t_PreparedReceive v_ReceiveChain v_Material)
  with
  | Core_models.Option.Option_Some prepared ->
    (match prepared <: t_PreparedReceive v_ReceiveChain v_Material with
      | PreparedReceive_Cached prepared ->
        let slot_index:usize = cast (prepared.f_target_slot <: u8) <: usize in
        if slot_index >=. Beaconcrypt_core.Ratchet.Control.v_RECEIVE_CACHE_CAPACITY
        then
          state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
            Core_models.Option.t_Option v_Plaintext)
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
              if cached.f_sequence <>. prepared.f_sequence
              then
                state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
                <:
                (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                  Core_models.Option.t_Option v_Plaintext)
              else
                let opened:Core_models.Option.t_Option v_Plaintext =
                  v_open cached.f_material prepared.f_sequence context
                in
                (match opened <: Core_models.Option.t_Option v_Plaintext with
                  | Core_models.Option.Option_None  ->
                    state,
                    (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
                    <:
                    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                      Core_models.Option.t_Option v_Plaintext)
                  | Core_models.Option.Option_Some plaintext ->
                    let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
                      publish_cached_receive #v_SendChain #v_ReceiveChain #v_Material state prepared
                    in
                    state,
                    (Core_models.Option.Option_Some plaintext
                      <:
                      Core_models.Option.t_Option v_Plaintext)
                    <:
                    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                      Core_models.Option.t_Option v_Plaintext))
            | Core_models.Option.Option_None  ->
              state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
              <:
              (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
                Core_models.Option.t_Option v_Plaintext))
      | PreparedReceive_Future pending ->
        let opened:Core_models.Option.t_Option v_Plaintext =
          v_open pending.f_target_material pending.f_target_sequence context
        in
        match opened <: Core_models.Option.t_Option v_Plaintext with
        | Core_models.Option.Option_None  ->
          state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
            Core_models.Option.t_Option v_Plaintext)
        | Core_models.Option.Option_Some plaintext ->
          let state:t_RefinedRatchet v_SendChain v_ReceiveChain v_Material =
            publish_future_receive #v_SendChain #v_ReceiveChain #v_Material state pending
          in
          state,
          (Core_models.Option.Option_Some plaintext <: Core_models.Option.t_Option v_Plaintext)
          <:
          (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
            Core_models.Option.t_Option v_Plaintext))
  | Core_models.Option.Option_None  ->
    state, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_Plaintext)
    <:
    (t_RefinedRatchet v_SendChain v_ReceiveChain v_Material &
      Core_models.Option.t_Option v_Plaintext)
