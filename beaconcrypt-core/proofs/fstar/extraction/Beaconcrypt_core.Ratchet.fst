module Beaconcrypt_core.Ratchet
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

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

friend Beaconcrypt_core.Ratchet.Refined

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

let impl_RatchetKdfOutput__into_step (self: t_RatchetKdfOutput)
    : Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_RatchetChain t_RatchetMaterial =
  {
    Beaconcrypt_core.Ratchet.Refined.f_chain = self.f_next_chain;
    Beaconcrypt_core.Ratchet.Refined.f_material
    =
    { f_key = self.f_key; f_nonce = self.f_nonce } <: t_RatchetMaterial
  }
  <:
  Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_RatchetChain t_RatchetMaterial

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

/// Apply the sole opaque ratchet primitive to the exact old chain and interpret its fixed output.
/// The primitive's complete production-facing type is `old 32-byte chain -> 76-byte output`.
/// Label selection and HKDF details are private to that domain-specific primitive.
/// Input selection, output size, partitioning, and fixed-width construction are owned here.
let derive_ratchet_step
      (old_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_RatchetChain t_RatchetMaterial =
  let request:t_SymmetricRatchetKdfRequest =
    impl_SymmetricRatchetKdfRequest__new (impl_RatchetChain__as_bytes old_chain
        <:
        t_Array u8 (mk_usize 32))
  in
  let output:t_Array u8 (mk_usize 76) = kdf request in
  impl_RatchetKdfOutput__into_step (split_ratchet_kdf_output output <: t_RatchetKdfOutput)

noeq

/// A concrete chain binds its fixed-width bytes to the sole KDF executor that
/// is carried through every later step. The fields stay private so callers
/// cannot replace the executor while retaining the same logical kernel.
type t_ConcreteRatchetChain = {
  f_chain:t_RatchetChain;
  f_kdf:t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)
}

/// Apply the executor bound into `old_chain` to a core-constructed request and
/// carry that same executor into the returned next chain.
let concrete_ratchet_step (old_chain: t_ConcreteRatchetChain)
    : Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_ConcreteRatchetChain t_RatchetMaterial =
  let stepped:Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_RatchetChain t_RatchetMaterial =
    derive_ratchet_step old_chain.f_chain old_chain.f_kdf
  in
  {
    Beaconcrypt_core.Ratchet.Refined.f_chain
    =
    { f_chain = stepped.Beaconcrypt_core.Ratchet.Refined.f_chain; f_kdf = old_chain.f_kdf }
    <:
    t_ConcreteRatchetChain;
    Beaconcrypt_core.Ratchet.Refined.f_material
    =
    stepped.Beaconcrypt_core.Ratchet.Refined.f_material
  }
  <:
  Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_ConcreteRatchetChain t_RatchetMaterial

noeq

/// Production-specialized ratchet kernel.
/// Both directional chains carry the same private KDF executor, and every
/// public transition below selects `concrete_ratchet_step` internally. This
/// removes the generic step callback from the production-facing lifecycle.
type t_ConcreteRatchetKernel = {
  f_refined:Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
    t_ConcreteRatchetChain
    t_RatchetMaterial
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
    Beaconcrypt_core.Ratchet.Refined.impl__from_counters #t_ConcreteRatchetChain
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
  Beaconcrypt_core.Ratchet.Refined.impl__send_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_sequence (self: t_ConcreteRatchetKernel) : u64 =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_cache_len (self: t_ConcreteRatchetKernel) : u8 =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_cache_len #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__send_chain (self: t_ConcreteRatchetKernel) : t_RatchetChain =
  self.f_refined.Beaconcrypt_core.Ratchet.Refined.f_send_chain.f_chain

let impl_ConcreteRatchetKernel__receive_chain (self: t_ConcreteRatchetKernel) : t_RatchetChain =
  self.f_refined.Beaconcrypt_core.Ratchet.Refined.f_receive_chain.f_chain

let impl_ConcreteRatchetKernel__receive_entry_at (self: t_ConcreteRatchetKernel) (slot: u8)
    : Core_models.Option.t_Option (u64 & t_RatchetMaterial) =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_entry_at #t_ConcreteRatchetChain
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
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Output) =
    Beaconcrypt_core.Ratchet.Refined.refined_seal_next #t_ConcreteRatchetChain
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

/// Admit, select, open, and finish with the core-fixed concrete step and KDF request.
let concrete_open_and_finish
      (#v_Context #v_Plaintext: Type0)
      (state: t_ConcreteRatchetKernel)
      (target: u64)
      (context: v_Context)
      (v_open: (t_RatchetMaterial -> u64 -> v_Context -> Core_models.Option.t_Option v_Plaintext))
    : (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext) =
  let
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Plaintext) =
    Beaconcrypt_core.Ratchet.Refined.refined_open_and_finish #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain #t_RatchetMaterial #v_Context #v_Plaintext state.f_refined target
      concrete_ratchet_step context v_open
  in
  let state:t_ConcreteRatchetKernel = { state with f_refined = tmp0 } <: t_ConcreteRatchetKernel in
  let hax_temp_output:Core_models.Option.t_Option v_Plaintext = out in
  state, hax_temp_output <: (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext)

noeq

/// Checked restoration builder that binds one concrete KDF executor to both
/// directional chains before any restored material can be published.
type t_ConcreteRatchetRestore = {
  f_refined:Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchetRestore t_ConcreteRatchetChain
    t_ConcreteRatchetChain
    t_RatchetMaterial
}

let start_concrete_restore
      (send_sequence receive_sequence: u64)
      (send_chain receive_chain: t_RatchetChain)
      (kdf: (t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetRestore =
  {
    f_refined
    =
    Beaconcrypt_core.Ratchet.Refined.start_refined_restore #t_ConcreteRatchetChain
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
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchetRestore t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      t_RatchetMaterial),
  (out: bool) =
    Beaconcrypt_core.Ratchet.Refined.refined_restore_receive_key #t_ConcreteRatchetChain
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
    Beaconcrypt_core.Ratchet.Refined.finish_refined_restore #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #t_RatchetMaterial
      restore.f_refined
  }
  <:
  t_ConcreteRatchetKernel
