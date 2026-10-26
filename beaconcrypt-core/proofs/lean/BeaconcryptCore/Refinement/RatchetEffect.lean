import BeaconcryptCore.Refinement.RatchetRefinement

/-!
# First-order cryptographic effect phases

This file proves basic laws about the production effect machine extracted from Rust.
The effect machine replaces stored function pointers with affine request/response
phases.  These lemmas establish that requests are core-owned, cancellation and failed
open restore the exact entry kernel, KDF replies are partitioned by the core, and
seal/open results are returned without an independent authentication flag.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core

/-! ## Initial PQXDH ratchet effect -/

theorem pqxdh.concrete.start_initial_ratchet_kdf_exact
    (root : Array Std.U8 32#usize) (initialization : pqxdh.RatchetInitialization) :
    pqxdh.concrete.start_initial_ratchet_kdf root initialization =
      ok {
        request := { input := root, info := ratchet.SYM_RATCHET_INFO },
        initialization := initialization
      } := by
  rfl

theorem pqxdh.concrete.initial_request_accessor_exact
    (pending : pqxdh.concrete.InitialRatchetKdfPending) :
    pqxdh.concrete.InitialRatchetKdfPending.impl.request pending = ok pending.request := by
  rfl

theorem pqxdh.concrete.start_beacon_ratchet_kdf_exact
    (root : Array Std.U8 32#usize) :
    pqxdh.concrete.start_beacon_ratchet_kdf root =
      ok {
        request := { input := root, info := ratchet.SYM_RATCHET_INFO },
        initialization := { send_offset := 32#u8, receive_offset := 0#u8 }
      } := by
  have hcast : UScalar.cast UScalarTy.U8 32#usize = 32#u8 := by
    apply UScalar.eq_of_val_eq
    simp_scalar
  simp [pqxdh.concrete.start_beacon_ratchet_kdf, pqxdh.BEACON_RATCHETS,
    pqxdh.concrete.start_initial_ratchet_kdf, ratchet.SymmetricRatchetKdfRequest.new,
    pqxdh.RATCHET_CHAIN_SIZE, ratchet.RATCHET_CHAIN_SIZE, lift, hcast]

theorem pqxdh.concrete.start_server_ratchet_kdf_exact
    (root : Array Std.U8 32#usize) :
    pqxdh.concrete.start_server_ratchet_kdf root =
      ok {
        request := { input := root, info := ratchet.SYM_RATCHET_INFO },
        initialization := { send_offset := 0#u8, receive_offset := 32#u8 }
      } := by
  have hcast : UScalar.cast UScalarTy.U8 32#usize = 32#u8 := by
    apply UScalar.eq_of_val_eq
    simp_scalar
  simp [pqxdh.concrete.start_server_ratchet_kdf, pqxdh.SERVER_RATCHETS,
    pqxdh.concrete.start_initial_ratchet_kdf, ratchet.SymmetricRatchetKdfRequest.new,
    pqxdh.RATCHET_CHAIN_SIZE, ratchet.RATCHET_CHAIN_SIZE, lift, hcast]

theorem pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition
    (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    pqxdh.concrete.resume_initial_ratchet_kdf pending response = (do
      let chains ←
        pqxdh.split_initial_ratchet_kdf_output response.bytes pending.initialization
      ratchet.concrete.ConcreteRatchetKernel.new chains.send_chain chains.receive_chain) := by
  rfl

/-! ## Ratchet KDF response interpretation -/

theorem ratchet.concrete.ratchet_step_from_response_exact
    (response : ratchet.RatchetKdfResponse) :
    ratchet.concrete.ratchet_step_from_response response = (do
      let output ← ratchet.split_ratchet_kdf_output response.bytes
      ok {
        chain := output.next_chain,
        material := { key := output.key, nonce := output.nonce }
      }) := by
  rfl

/-! ## Affine cancellation and completion laws -/

theorem ratchet.concrete.SendKdf.cancel_exact {Context : Type}
    (pending : ratchet.concrete.SendKdf Context) :
    pending.cancel = ok (pending.entry, pending.context) := by
  rfl

theorem ratchet.concrete.SendKdf.request_exact {Context : Type}
    (pending : ratchet.concrete.SendKdf Context) :
    ratchet.concrete.SendKdf.impl.request pending = ok pending.request := by
  rfl

/-- A non-exhausted production send emits the exact old chain and fixed domain label.
The continuation also owns the unchanged entry kernel and caller context. -/
theorem ratchet.concrete.begin_send_nonexhausted_exact {Context : Type}
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (hmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX) :
    ∃ pending : ratchet.concrete.SendKdf Context,
      ratchet.concrete.begin_send kernel context =
        ok (ratchet.concrete.SendStart.SendKdfRequested pending) ∧
      pending.entry = kernel ∧
      pending.context = context ∧
      pending.request.input = kernel.refined.send_chain.bytes ∧
      pending.request.info = ratchet.SYM_RATCHET_INFO ∧
      pending.sequence.val = kernel.refined.control.send_sequence.val + 1 := by
  obtain ⟨advanced, hadv, hsend, -, -, hsequence, hkey⟩ :=
    ratchet.control.advance_send_ok kernel.refined.control hmax
  let pending : ratchet.concrete.SendKdf Context := {
    entry := kernel,
    context,
    committed_control := advanced.state,
    logical := advanced.key,
    sequence := advanced.state.send_sequence,
    request := {
      input := kernel.refined.send_chain.bytes,
      info := ratchet.SYM_RATCHET_INFO
    }
  }
  refine ⟨pending, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp [ratchet.concrete.begin_send, hadv, hsequence, hkey,
      ratchet.control.SendKey.impl.sequence,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64,
      ratchet.control.RatchetState.impl.send_sequence, ratchet.RatchetChain.as_bytes,
      ratchet.SymmetricRatchetKdfRequest.new, pending]
  · exact hsend

theorem ratchet.concrete.begin_send_exhausted_restores_entry {Context : Type}
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (hmax : kernel.refined.control.send_sequence = core.num.U64.MAX) :
    ratchet.concrete.begin_send kernel context =
      ok (ratchet.concrete.SendStart.SendExhausted kernel context) := by
  have hadv := ratchet.control.advance_send_max kernel.refined.control hmax
  simp [ratchet.concrete.begin_send, hadv]

theorem ratchet.concrete.SendKdf.resume_exact {Context : Type}
    (pending : ratchet.concrete.SendKdf Context) (response : ratchet.RatchetKdfResponse)
    (stepped : ratchet.refined.RatchetStep ratchet.RatchetChain ratchet.RatchetMaterial)
    (hstep : ratchet.concrete.ratchet_step_from_response response = ok stepped) :
    pending.resume response =
      ok {
        advanced := {
          refined := {
            pending.entry.refined with
            control := pending.committed_control,
            send_chain := stepped.chain
          }
        },
        context := pending.context,
        logical := pending.logical,
        sequence := pending.sequence,
        material := stepped.material
      } := by
  simp [ratchet.concrete.SendKdf.resume, hstep]

theorem ratchet.concrete.ReceiveKdf.cancel_exact {Context : Type}
    (pending : ratchet.concrete.ReceiveKdf Context) :
    pending.cancel = ok (pending.entry, pending.context) := by
  rfl

theorem ratchet.concrete.ReceiveKdf.request_exact {Context : Type}
    (pending : ratchet.concrete.ReceiveKdf Context) :
    ratchet.concrete.ReceiveKdf.impl.request pending = ok pending.request := by
  rfl

theorem ratchet.concrete.begin_receive_rejected_plan_restores_entry {Context : Type}
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (target : Std.U64)
    (context : Context) (derivations : Std.U64)
    (hplan : ratchet.control.plan_receive_until kernel.refined.control target =
      ok {
        sequence := core.option.Option.None,
        derivations := derivations
      }) :
    ratchet.concrete.begin_receive kernel target context =
      ok (ratchet.concrete.ReceiveEffect.ReceiveRejected kernel context) := by
  simp [ratchet.concrete.begin_receive, hplan, ratchet.concrete.receive_rejected]

theorem ratchet.concrete.begin_receive_cached_exact {Context : Type}
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (target sequence : Std.U64)
    (context : Context) (prepared : ratchet.refined.PreparedCachedReceive)
    (hplan : ratchet.control.plan_receive_until kernel.refined.control target =
      ok {
        sequence := core.option.Option.Some sequence,
        derivations := 0#u64
      })
    (hprepared : ratchet.refined.prepare_cached_receive kernel.refined sequence =
      ok (core.option.Option.Some prepared)) :
    ratchet.concrete.begin_receive kernel target context =
      ok (ratchet.concrete.ReceiveEffect.ReceiveOpenRequested {
        entry := kernel,
        context,
        prepared := ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared
      }) := by
  simp [ratchet.concrete.begin_receive, hplan, hprepared]

/-- An admitted future receive emits the exact live receive chain and fixed domain
label. Its working state and staging array remain private in the continuation. -/
theorem ratchet.concrete.begin_receive_future_request_exact {Context : Type}
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (target sequence derivations skipped : Std.U64)
    (context : Context)
    (hnonzero : derivations ≠ 0#u64)
    (hskipped : derivations - 1#u64 = ok skipped)
    (hbound : ¬skipped > ratchet.control.RATCHET_MAX_GAP)
    (hplan : ratchet.control.plan_receive_until kernel.refined.control target =
      ok {
        sequence := core.option.Option.Some sequence,
        derivations := derivations
      })
    (hempty : ratchet.refined.refined_receive_slots_are_empty kernel.refined
      kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped) = ok true) :
    ∃ pending : ratchet.concrete.ReceiveKdf Context,
      ratchet.concrete.begin_receive kernel target context =
        ok (ratchet.concrete.ReceiveEffect.ReceiveKdfRequested pending) ∧
      pending.entry = kernel ∧
      pending.context = context ∧
      pending.target = sequence ∧
      pending.working_control = kernel.refined.control ∧
      pending.request.input = kernel.refined.receive_chain.bytes ∧
      pending.request.info = ratchet.SYM_RATCHET_INFO := by
  have hboundval : ¬50 < skipped.val := by
    simp [ratchet.control.RATCHET_MAX_GAP] at hbound
    scalar_tac
  obtain ⟨slots, hslots⟩ : ∃ slots,
      ratchet.refined.empty_material_slots ratchet.RatchetMaterial = ok slots := by
    simp [ratchet.refined.empty_material_slots]
  let pending : ratchet.concrete.ReceiveKdf Context := {
    entry := kernel,
    context,
    target := sequence,
    working_control := kernel.refined.control,
    staged_slots := slots,
    first_slot := kernel.refined.control.receive_cache.len,
    skipped := 0#u8,
    remaining := UScalar.cast UScalarTy.U8 derivations,
    request := {
      input := kernel.refined.receive_chain.bytes,
      info := ratchet.SYM_RATCHET_INFO
    }
  }
  refine ⟨pending, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [ratchet.concrete.begin_receive, hplan, hnonzero, hskipped, hboundval, lift,
    ratchet.control.RatchetState.receive_cache_len, hempty, ratchet.RatchetChain.as_bytes,
    ratchet.SymmetricRatchetKdfRequest.new, hslots, pending]

theorem ratchet.concrete.ReceiveOpen.reject_exact {Context : Type}
    (pending : ratchet.concrete.ReceiveOpen Context) :
    pending.reject = ok (pending.entry, pending.context) := by
  rfl

theorem ratchet.concrete.ReceiveOpen.context_exact {Context : Type}
    (pending : ratchet.concrete.ReceiveOpen Context) :
    ratchet.concrete.ReceiveOpen.impl.context pending = ok pending.context := by
  rfl

theorem ratchet.concrete.ReceiveOpen.future_sequence_exact {Context : Type}
    (entry : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (future : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial) :
    ratchet.concrete.ReceiveOpen.sequence {
      entry,
      context,
      prepared := ratchet.refined.PreparedReceive.PreparedReceiveFutureCase future
    } = ok future.target_sequence := by
  rfl

theorem ratchet.concrete.ReceiveOpen.future_material_exact {Context : Type}
    (entry : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (future : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial) :
    ratchet.concrete.ReceiveOpen.material {
      entry,
      context,
      prepared := ratchet.refined.PreparedReceive.PreparedReceiveFutureCase future
    } = ok (core.option.Option.Some future.target_material) := by
  rfl

theorem ratchet.concrete.SendSeal.finish_returns_interpreter_result
    {Context Output : Type} (pending : ratchet.concrete.SendSeal Context)
    (sealed : core.option.Option Output) :
    pending.finish sealed = ok (pending.advanced, sealed) := by
  cases h : pending.logical.available <;>
    simp [ratchet.concrete.SendSeal.finish, ratchet.control.finish_send, h]

theorem ratchet.concrete.ReceiveOpen.finish_failure_restores_entry
    {Context Plaintext : Type} (pending : ratchet.concrete.ReceiveOpen Context) :
    pending.finish (core.option.Option.None : core.option.Option Plaintext) =
      ok (pending.entry, core.option.Option.None) := by
  rfl

theorem ratchet.concrete.ReceiveOpen.finish_future_success_publishes_same_plaintext
    {Context Plaintext : Type} (entry : ratchet.concrete.ConcreteRatchetKernel)
    (context : Context)
    (future : ratchet.refined.PendingReceive ratchet.RatchetChain ratchet.RatchetMaterial)
    (plaintext : Plaintext) (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain
      ratchet.RatchetChain ratchet.RatchetMaterial)
    (hpublish : ratchet.refined.publish_future_receive entry.refined future = ok published) :
    ratchet.concrete.ReceiveOpen.finish {
      entry,
      context,
      prepared := ratchet.refined.PreparedReceive.PreparedReceiveFutureCase future
    } (core.option.Option.Some plaintext) =
      ok ({ refined := published }, core.option.Option.Some plaintext) := by
  simp [ratchet.concrete.ReceiveOpen.finish, hpublish]

theorem ratchet.concrete.ReceiveOpen.finish_cached_success_publishes_same_plaintext
    {Context Plaintext : Type} (entry : ratchet.concrete.ConcreteRatchetKernel)
    (context : Context) (cached : ratchet.refined.PreparedCachedReceive)
    (plaintext : Plaintext) (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain
      ratchet.RatchetChain ratchet.RatchetMaterial)
    (hpublish : ratchet.refined.publish_cached_receive entry.refined cached = ok published) :
    ratchet.concrete.ReceiveOpen.finish {
      entry,
      context,
      prepared := ratchet.refined.PreparedReceive.PreparedReceiveCachedCase cached
    } (core.option.Option.Some plaintext) =
      ok ({ refined := published }, core.option.Option.Some plaintext) := by
  simp [ratchet.concrete.ReceiveOpen.finish, hpublish]

end beaconcrypt_core
