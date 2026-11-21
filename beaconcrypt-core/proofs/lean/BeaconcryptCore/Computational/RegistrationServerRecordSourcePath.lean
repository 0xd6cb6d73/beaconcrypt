-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordRollback
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Every successful actual source first-record run follows the original extracted Core continuation path, including the full enclosing seal/write failures and mutable hash result. Thus binding, candidate and sequence-one advanced kernel retention need no codec or primitive-success premise. -/
namespace BeaconcryptCore.Computational.RegistrationServerRecordSourcePath
open RegistrationServerRecordRollback (Spec implementation)
open RegistrationNativePlatformServerRecord (continueWith continueResult fromWrite)
open RegistrationNativePlatformSourceRecord (fromInitialWithHash fromRatchetWithHash fromAeadWithHash)

private theorem continueWith_support {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM RegistrationServerRecordExecutor.Result)) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (continueWith result next)) :
    ∃ value, result = .ok value ∧ .ok (.Ok completed) ∈ support (next value) := by
  cases result <;> simp_all [continueWith]

private theorem continueResult_support {Input : Type} (result : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM RegistrationServerRecordExecutor.Result)) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support (continueResult result next)) :
    ∃ value, result = .ok (.Ok value) ∧ .ok (.Ok completed) ∈ support (next value) := by
  cases result with
  | ok value => cases value <;> simp_all [continueResult]
  | fail error | div => simp_all [continueResult]

theorem path (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (supported : .ok (.Ok completed) ∈ support
      (fromInitialWithHash (m := OracleComp Spec) (fun request => Spec.query (.record request))
        (fun request => Spec.query (.sealing request)) (fun transcript => Spec.query (.commitment transcript))
        (fun request => Spec.query (.writing request)) initial)) : RegistrationServerRecordExecutor.Path initial completed := by
  obtain ⟨_request, _requested, called⟩ := continueWith_support initial.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨initialReply, _called, continued⟩ := called
  obtain ⟨ratchet, initialResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨_request, _requested, called⟩ := continueWith_support ratchet.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨ratchetReply, _called, continued⟩ := called
  obtain ⟨aead, ratchetResume, supported⟩ := continueResult_support _ _ completed continued
  obtain ⟨_request, _requested, called⟩ := continueWith_support aead.request _ completed supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨sealingReply, _called, continued⟩ := called
  obtain ⟨commitmentPhase, aeadResume, supported⟩ := continueResult_support _ _ completed continued
  cases sealingReply with
  | fail error | div => simp only [bind_tc_fail, bind_tc_div, reduceCtorEq] at aeadResume
  | ok aeadReply =>
    simp only [bind_tc_ok] at aeadResume
    rw [RegistrationNativePlatformCommitment.normalize] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨hashResult, _hashed, continued⟩ := supported
    obtain ⟨writePhase, commitmentResume, supported⟩ := continueResult_support _ _ completed continued
    cases hashResult with
    | fail error | div => simp only [bind_tc_fail, bind_tc_div, reduceCtorEq] at commitmentResume
    | ok pair =>
      rcases pair with ⟨hashReply, _updated⟩
      simp only [bind_tc_ok] at commitmentResume
      obtain ⟨_request, _requested, called⟩ := continueWith_support writePhase.request _ completed supported
      simp only [mem_support_bind_iff] at called
      obtain ⟨writingReply, _written, returned⟩ := called
      simp only [support_pure, Set.mem_singleton_iff] at returned
      cases writingReply with
      | fail error | div => simp only [bind_tc_fail, bind_tc_div, reduceCtorEq] at returned
      | ok writeReply =>
        simp only [bind_tc_ok] at returned
        exact ⟨initialReply, ratchet, initialResume, ratchetReply, aead, ratchetResume, aeadReply,
          commitmentPhase, aeadResume, hashReply, writePhase, commitmentResume, writeReply, returned.symm⟩

theorem stateful_path {State : Type}
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : State)
    (supported : (.ok (.Ok completed), after) ∈ support ((fromInitialWithHash record sealing hash write initial).run before)) :
    RegistrationServerRecordExecutor.Path initial completed := by
  rw [← RegistrationServerRecordRollback.interpret record sealing hash write initial] at supported
  apply path initial completed
  apply OracleComp.support_simulateQ_run'_subset (implementation record sealing hash write) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

theorem stateful_retains {State : Type}
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : State)
    (supported : (.ok (.Ok completed), after) ∈ support ((fromInitialWithHash record sealing hash write initial).run before)) :
    completed.binding = initial.binding ∧ completed.candidate = initial.candidate ∧
      ∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        completed.kernel = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = initial.binding.associated_data :=
  RegistrationServerRecordExecutor.path_retains initial completed (stateful_path record sealing hash write initial completed before after supported)
end BeaconcryptCore.Computational.RegistrationServerRecordSourcePath

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.path

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.stateful_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.stateful_path

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.stateful_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRecordSourcePath.stateful_retains
