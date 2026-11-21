-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationSeedKernel

/-! After the actual two successful KDF replies, the retained Server AEAD capability contains the advanced chain, unchanged opposite chain, selected material, public record context and sequence-one control. It contains no old left chain or root. These functional equations justify replacing that unused initializer coordinate inside the actual post-root service. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationSeedErasure

def selected (initial : registration.ServerInitialKdf)
    (initialResponse : pqxdh.concrete.InitialRatchetKdfResponse) (response : RatchetKdfResponse) :
    RustM (core.result.Result registration.ServerRecordAead pqxdh.ServerState) := do
  let result ← initial.resume (.Some initialResponse)
  match result with
  | .Err control => .ok (.Err control)
  | .Ok next => next.resume (.Some response)

theorem initial_kernel (initial : registration.ServerInitialKdf) (root : Std.Array Std.U8 32#usize)
    (actual : initial.pending = PqxdhInitialRatchetComplementarity.serverPending root)
    (left right : PqxdhSecretInputKdf.RootOutput) :
    pqxdh.concrete.resume_initial_ratchet_kdf initial.pending
      (RawCtxSelectedInitialConstructor.response64 (left ++ right)) =
      ConcreteRatchetKernel.from_counters 0#u64 0#u64
        (RawCtxFreshChainCut.concreteChain left) (RawCtxFreshChainCut.concreteChain right) := by
  rw [actual]
  exact PqxdhRecordLiftSeed.initial_kernel false left right

theorem left_unused (initial : registration.ServerInitialKdf) (root : Std.Array Std.U8 32#usize)
    (actual : initial.pending = PqxdhInitialRatchetComplementarity.serverPending root)
    (left₁ left₂ right : PqxdhSecretInputKdf.RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    selected initial (RawCtxSelectedInitialConstructor.response64 (left₁ ++ right))
        (RawCtxKdfRequestTable.fullResponse output) =
      selected initial (RawCtxSelectedInitialConstructor.response64 (left₂ ++ right))
        (RawCtxKdfRequestTable.fullResponse output) := by
  obtain ⟨bound, boundRun, _boundBytes⟩ := registration_key_id_binding_abs initial.candidate.key_id
  have contextRun : record_effects.SealFrameContext.registration initial.application
      initial.candidate.key_id initial.candidate.server_identity_key_id initial.binding.associated_data =
      .ok (serverRecordContext initial bound) := by
    simp [record_effects.SealFrameContext.registration, boundRun,
      pqxdh.RegistrationKeyIdBinding.as_bytes, serverRecordContext]
  simp only [selected, registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate,
    initial_kernel initial root actual, pqxdh.ServerRegistrationCandidate.impl.key_id,
    pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id,
    session.CompletedRegistrationBinding.impl.associated_data, contextRun, bind_tc_ok]
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty initial.application = .ok result := ⟨_, rfl⟩
  simp only [ConcreteRatchetKernel.from_counters, ratchet.refined.RefinedRatchet.from_counters,
    ratchet.control.RatchetState.from_counters, ratchet.control.SequenceCache.empty,
    ratchet.refined.empty_material_slots, bind_tc_ok, record_effects.begin_record_send,
    serverRecordContext, emptyRun]
  cases empty
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, core.option.Option.is_none,
    core.option.Option.is_some, bind_tc_ok, begin_send, ratchet.control.advance_send]
  all_goals simp only [ite_eq_right (by decide : 0#u64 ≠ core.num.U64.MAX),
    show (0#u64 + 1#u64 : RustM _) = .ok 1#u64 from rfl,
    bind_tc_ok, ratchet.control.SendKey.impl.sequence,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
    beq_self_eq_true, ratchet.control.RatchetState.impl.send_sequence, ite_true,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
    registration.ServerInitialSeal.resume, record_effects.RecordSendKdf.resume, SendKdf.resume,
    PqxdhRecordLiftSeed.response_step]
  all_goals simp only [Bool.true_eq_false, decide_false, Bool.false_eq_true, ite_false, bind_tc_ok]

theorem server_left_unused (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial)
    (left₁ left₂ right : PqxdhSecretInputKdf.RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput) :
    selected initial (RawCtxSelectedInitialConstructor.response64 (left₁ ++ right))
        (RawCtxKdfRequestTable.fullResponse output) =
      selected initial (RawCtxSelectedInitialConstructor.response64 (left₂ ++ right))
        (RawCtxKdfRequestTable.fullResponse output) :=
  left_unused initial agreement.root.bytes
    (RegistrationSeedKernel.server_pending control current availability agreement application initial actual)
      left₁ left₂ right output

end BeaconcryptCore.Computational.RegistrationSeedErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationSeedErasure.initial_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedErasure.initial_kernel
/-- info: 'BeaconcryptCore.Computational.RegistrationSeedErasure.left_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedErasure.left_unused
/-- info: 'BeaconcryptCore.Computational.RegistrationSeedErasure.server_left_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationSeedErasure.server_left_unused
