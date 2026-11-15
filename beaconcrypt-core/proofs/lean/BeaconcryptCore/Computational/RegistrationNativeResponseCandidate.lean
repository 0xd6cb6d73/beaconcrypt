-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseIdentity
import BeaconcryptCore.Computational.RegistrationBoundKeySchedule
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Refinement.RegistrationAd

/-! The actual admitted Server initializer chooses the current Ed25519 identity. Arbitrary primitive callbacks in the native record and publication trees cannot change that encoded identity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseCandidate

/-- Actual successful native admission selects the current pin's Ed25519 public identity. -/
theorem initial_identity (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial) :
    initial.candidate.server_identity_public_key = current.binding.identity_public_key := by
  obtain ⟨_, _, _, _, _, prepared⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding
      control current availability agreement application initial actual
  exact (BeaconcryptCore.Refinement.RegistrationAd.server_prepare_fields
    control agreement.pending current.binding availability initial.candidate prepared).2.1

/-- The complete native record tree retains its admitted candidate's public Server identity. -/
theorem record_identity (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromInitial initial)) :
    completed.candidate.server_identity_public_key = initial.candidate.server_identity_public_key :=
  congrArg (fun candidate => candidate.server_identity_public_key)
    (RegistrationServerRecordExecutor.path_retains initial completed
      (RegistrationServerRecordExecutor.fromInitial_path initial completed supported)).2.1

/-- Supplying the two source KDF replies preserves the admitted candidate identity before every raw-record callback. -/
theorem factored_identity (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (RegistrationBoundKeySchedule.factored initial output)) :
    completed.candidate.server_identity_public_key = initial.candidate.server_identity_public_key := by
  let pending := RegistrationBoundKeySchedule.restore initial
  let initialReply := RawCtxSelectedInitialConstructor.response64 (RegistrationBoundKeySchedule.zero ++ output.2)
  let ratchetReply := RawCtxKdfRequestTable.fullResponse output.1
  obtain ⟨kernel, next, selected, context, _kernelRun, firstResume, secondResume, _sent⟩ :=
    RegistrationSeedKernel.source_send pending initialReply ratchetReply
  have selectedRun : RegistrationSeedErasure.selected pending initialReply ratchetReply = .ok (.Ok selected) := by
    simp only [RegistrationSeedErasure.selected, firstResume, bind_tc_ok, secondResume]
  change .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.continueResult
    (RegistrationSeedErasure.selected pending initialReply ratchetReply) RegistrationServerRecordExecutor.fromAead) at supported
  rw [selectedRun] at supported
  obtain ⟨initialRequest, initialRun⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialKdf_request_total pending
  obtain ⟨ratchetRequest, ratchetRun⟩ := BeaconcryptCore.PanicFreedom.RegistrationTrivial.ServerInitialSeal_request_total next
  have full : .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromInitial pending) := by
    simp only [RegistrationServerRecordExecutor.fromInitial, initialRun,
      RegistrationServerRecordExecutor.continueWith, mem_support_bind_iff]
    refine ⟨.Some initialReply, mem_support_query _ _, ?_⟩
    rw [firstResume]
    simp only [RegistrationServerRecordExecutor.continueResult, RegistrationServerRecordExecutor.fromRatchet,
      ratchetRun, RegistrationServerRecordExecutor.continueWith, mem_support_bind_iff]
    exact ⟨.Some ratchetReply, mem_support_query _ _, by simpa only [secondResume, RegistrationServerRecordExecutor.continueResult] using supported⟩
  exact record_identity pending completed full

end BeaconcryptCore.Computational.RegistrationNativeResponseCandidate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.initial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.initial_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.record_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.record_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.factored_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCandidate.factored_identity
