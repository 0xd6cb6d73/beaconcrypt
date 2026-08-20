module Beaconcrypt_core.Ratchet.Concrete
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

friend Beaconcrypt_core.Ratchet
friend Beaconcrypt_core.Ratchet.Refined
noeq

/// A concrete chain binds its fixed-width bytes to the sole KDF executor that
/// is carried through every later step. The fields stay private so callers
/// cannot replace the executor while retaining the same logical kernel.
type t_ConcreteRatchetChain = {
  f_chain:Beaconcrypt_core.Ratchet.t_RatchetChain;
  f_kdf:Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)
}

noeq

/// Production-specialized ratchet kernel.
/// Both directional chains carry the same private KDF executor, and every
/// public transition below selects `concrete_ratchet_step` internally. This
/// removes the generic step callback from the production-facing lifecycle.
type t_ConcreteRatchetKernel = {
  f_refined:Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
    t_ConcreteRatchetChain
    Beaconcrypt_core.Ratchet.t_RatchetMaterial
}

/// Construct a concrete kernel at checked persistence counters.
let impl_ConcreteRatchetKernel__from_counters
      (send_sequence receive_sequence: u64)
      (send_chain receive_chain: Beaconcrypt_core.Ratchet.t_RatchetChain)
      (kdf: (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetKernel =
  {
    f_refined
    =
    Beaconcrypt_core.Ratchet.Refined.impl__from_counters #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #Beaconcrypt_core.Ratchet.t_RatchetMaterial
      send_sequence
      receive_sequence
      ({ f_chain = send_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
      ({ f_chain = receive_chain; f_kdf = kdf } <: t_ConcreteRatchetChain)
  }
  <:
  t_ConcreteRatchetKernel

/// Construct a fresh concrete kernel and bind one KDF executor for its lifetime.
let impl_ConcreteRatchetKernel__new
      (send_chain receive_chain: Beaconcrypt_core.Ratchet.t_RatchetChain)
      (kdf: (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetKernel =
  impl_ConcreteRatchetKernel__from_counters (mk_u64 0) (mk_u64 0) send_chain receive_chain kdf

let impl_ConcreteRatchetKernel__send_sequence (self: t_ConcreteRatchetKernel) : u64 =
  Beaconcrypt_core.Ratchet.Refined.impl__send_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #Beaconcrypt_core.Ratchet.t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_sequence (self: t_ConcreteRatchetKernel) : u64 =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_sequence #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #Beaconcrypt_core.Ratchet.t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__receive_cache_len (self: t_ConcreteRatchetKernel) : u8 =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_cache_len #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #Beaconcrypt_core.Ratchet.t_RatchetMaterial
    self.f_refined

let impl_ConcreteRatchetKernel__send_chain (self: t_ConcreteRatchetKernel)
    : Beaconcrypt_core.Ratchet.t_RatchetChain =
  self.f_refined.Beaconcrypt_core.Ratchet.Refined.f_send_chain.f_chain

let impl_ConcreteRatchetKernel__receive_chain (self: t_ConcreteRatchetKernel)
    : Beaconcrypt_core.Ratchet.t_RatchetChain =
  self.f_refined.Beaconcrypt_core.Ratchet.Refined.f_receive_chain.f_chain

let impl_ConcreteRatchetKernel__receive_entry_at (self: t_ConcreteRatchetKernel) (slot: u8)
    : Core_models.Option.t_Option (u64 & Beaconcrypt_core.Ratchet.t_RatchetMaterial) =
  Beaconcrypt_core.Ratchet.Refined.impl__receive_entry_at #t_ConcreteRatchetChain
    #t_ConcreteRatchetChain
    #Beaconcrypt_core.Ratchet.t_RatchetMaterial
    self.f_refined
    slot

noeq

/// Checked restoration builder that binds one concrete KDF executor to both
/// directional chains before any restored material can be published.
type t_ConcreteRatchetRestore = {
  f_refined:Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchetRestore t_ConcreteRatchetChain
    t_ConcreteRatchetChain
    Beaconcrypt_core.Ratchet.t_RatchetMaterial
}

let start_concrete_restore
      (send_sequence receive_sequence: u64)
      (send_chain receive_chain: Beaconcrypt_core.Ratchet.t_RatchetChain)
      (kdf: (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : t_ConcreteRatchetRestore =
  {
    f_refined
    =
    Beaconcrypt_core.Ratchet.Refined.start_refined_restore #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #Beaconcrypt_core.Ratchet.t_RatchetMaterial
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
      (material: Beaconcrypt_core.Ratchet.t_RatchetMaterial)
    : (t_ConcreteRatchetRestore & bool) =
  let
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchetRestore t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      Beaconcrypt_core.Ratchet.t_RatchetMaterial),
  (out: bool) =
    Beaconcrypt_core.Ratchet.Refined.refined_restore_receive_key #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #Beaconcrypt_core.Ratchet.t_RatchetMaterial
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
      #Beaconcrypt_core.Ratchet.t_RatchetMaterial
      restore.f_refined
  }
  <:
  t_ConcreteRatchetKernel

/// Apply the sole opaque ratchet primitive to the exact old chain and interpret its fixed output.
/// The primitive's complete production-facing type is `old 32-byte chain -> 76-byte output`.
/// Label selection and HKDF details are private to that domain-specific primitive.
/// Input selection, output size, partitioning, and fixed-width construction are owned here.
let derive_ratchet_step
      (old_chain: Beaconcrypt_core.Ratchet.t_RatchetChain)
      (kdf: (Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest -> t_Array u8 (mk_usize 76)))
    : Beaconcrypt_core.Ratchet.Refined.t_RatchetStep Beaconcrypt_core.Ratchet.t_RatchetChain
      Beaconcrypt_core.Ratchet.t_RatchetMaterial =
  let request:Beaconcrypt_core.Ratchet.t_SymmetricRatchetKdfRequest =
    Beaconcrypt_core.Ratchet.impl_SymmetricRatchetKdfRequest__new (Beaconcrypt_core.Ratchet.impl_RatchetChain__as_bytes
          old_chain
        <:
        t_Array u8 (mk_usize 32))
  in
  let output:t_Array u8 (mk_usize 76) = kdf request in
  let output:Beaconcrypt_core.Ratchet.t_RatchetKdfOutput =
    Beaconcrypt_core.Ratchet.split_ratchet_kdf_output output
  in
  {
    Beaconcrypt_core.Ratchet.Refined.f_chain = output.Beaconcrypt_core.Ratchet.f_next_chain;
    Beaconcrypt_core.Ratchet.Refined.f_material
    =
    {
      Beaconcrypt_core.Ratchet.f_key = output.Beaconcrypt_core.Ratchet.f_key;
      Beaconcrypt_core.Ratchet.f_nonce = output.Beaconcrypt_core.Ratchet.f_nonce
    }
    <:
    Beaconcrypt_core.Ratchet.t_RatchetMaterial
  }
  <:
  Beaconcrypt_core.Ratchet.Refined.t_RatchetStep Beaconcrypt_core.Ratchet.t_RatchetChain
    Beaconcrypt_core.Ratchet.t_RatchetMaterial

/// Apply the executor bound into `old_chain` to a core-constructed request and
/// carry that same executor into the returned next chain.
let concrete_ratchet_step (old_chain: t_ConcreteRatchetChain)
    : Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_ConcreteRatchetChain
      Beaconcrypt_core.Ratchet.t_RatchetMaterial =
  let stepped:Beaconcrypt_core.Ratchet.Refined.t_RatchetStep Beaconcrypt_core.Ratchet.t_RatchetChain
    Beaconcrypt_core.Ratchet.t_RatchetMaterial =
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
  Beaconcrypt_core.Ratchet.Refined.t_RatchetStep t_ConcreteRatchetChain
    Beaconcrypt_core.Ratchet.t_RatchetMaterial

/// Advance and seal with the core-fixed concrete step and KDF request.
let concrete_seal_next
      (#v_Context #v_Output: Type0)
      (state: t_ConcreteRatchetKernel)
      (context: v_Context)
      (seal:
          (Beaconcrypt_core.Ratchet.t_RatchetMaterial -> u64 -> v_Context
              -> Core_models.Option.t_Option v_Output))
    : (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Output) =
  let
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      Beaconcrypt_core.Ratchet.t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Output) =
    Beaconcrypt_core.Ratchet.Refined.refined_seal_next #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain
      #Beaconcrypt_core.Ratchet.t_RatchetMaterial
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
      (v_open:
          (Beaconcrypt_core.Ratchet.t_RatchetMaterial -> u64 -> v_Context
              -> Core_models.Option.t_Option v_Plaintext))
    : (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext) =
  let
  (tmp0:
    Beaconcrypt_core.Ratchet.Refined.t_RefinedRatchet t_ConcreteRatchetChain
      t_ConcreteRatchetChain
      Beaconcrypt_core.Ratchet.t_RatchetMaterial),
  (out: Core_models.Option.t_Option v_Plaintext) =
    Beaconcrypt_core.Ratchet.Refined.refined_open_and_finish #t_ConcreteRatchetChain
      #t_ConcreteRatchetChain #Beaconcrypt_core.Ratchet.t_RatchetMaterial #v_Context #v_Plaintext
      state.f_refined target concrete_ratchet_step context v_open
  in
  let state:t_ConcreteRatchetKernel = { state with f_refined = tmp0 } <: t_ConcreteRatchetKernel in
  let hax_temp_output:Core_models.Option.t_Option v_Plaintext = out in
  state, hax_temp_output <: (t_ConcreteRatchetKernel & Core_models.Option.t_Option v_Plaintext)
