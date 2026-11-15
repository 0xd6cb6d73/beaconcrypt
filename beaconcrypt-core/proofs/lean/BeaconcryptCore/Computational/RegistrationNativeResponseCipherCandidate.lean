-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext
import BeaconcryptCore.Computational.RegistrationBoundKeySchedule
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor
import BeaconcryptCore.Refinement.RegistrationAd

/-! The actual admitted Server initializer retains its pending registration ciphertext. Arbitrary primitive callbacks in the native record and publication trees cannot change that encoded ciphertext. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate

/-- Actual successful native admission retains the original pending registration ciphertext. -/
theorem initial_ciphertext (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (agreement : agreement.ServerAgreement) (application : Slice Std.U8)
    (initial : registration.ServerInitialKdf)
    (actual : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission control current availability agreement application initial) :
    initial.candidate.kem_ciphertext = agreement.pending.kem_ciphertext := by
  obtain ⟨_, _, _, _, _, prepared⟩ :=
    BeaconcryptCore.Refinement.RegistrationAd.server_admission_binding
      control current availability agreement application initial actual
  exact (BeaconcryptCore.Refinement.RegistrationAd.server_prepare_fields
    control agreement.pending current.binding availability initial.candidate prepared).2.2.2.2

/-- The complete native record tree retains its admitted candidate's public KEM ciphertext. -/
theorem record_ciphertext (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (RegistrationServerRecordExecutor.fromInitial initial)) :
    completed.candidate.kem_ciphertext = initial.candidate.kem_ciphertext :=
  congrArg (fun candidate => candidate.kem_ciphertext)
    (RegistrationServerRecordExecutor.path_retains initial completed
      (RegistrationServerRecordExecutor.fromInitial_path initial completed supported)).2.1

/-- Supplying the two source KDF replies preserves the admitted candidate KEM ciphertext before every raw-record callback. -/
theorem factored_ciphertext (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (RegistrationBoundKeySchedule.factored initial output)) :
    completed.candidate.kem_ciphertext = initial.candidate.kem_ciphertext := by
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
  exact record_ciphertext pending completed full


end BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.initial_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.initial_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.record_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.record_ciphertext

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.factored_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseCipherCandidate.factored_ciphertext
