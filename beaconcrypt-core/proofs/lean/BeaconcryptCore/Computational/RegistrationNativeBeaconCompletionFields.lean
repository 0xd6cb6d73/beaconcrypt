-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields

/-! The same actual Beacon hash/open trace retains its original agreement through commitment admission and publishes exactly the admitted plaintext suffix with the source-populated completed binding. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields
open BeaconcryptCore.Refinement.RegistrationRecords
open RegistrationNativeBeaconRecordTrace (Trace)
variable {S : Type}

/-- Commitment verification preserves the exact agreement of this actual source trace. -/
theorem agreement (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (expected : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (before after : S)
    (trace : Trace implementation phase completed before after) (metadata : BeaconPhaseMetadata expected phase) :
    trace.aead.agreement = expected := by
  have kept := RegistrationNativeBeaconRecordFields.along_prefix implementation expected trace.leading metadata
  obtain ⟨result, executed, retained⟩ := beacon_commitment_metadata expected trace.commitmentState
    (RegistrationBeaconRecordExecutor.commitmentMatches trace.hashReply trace.supplied) kept
  have resultEq : result = .Ok (.AeadRequested trace.aead) := RustM.ok.inj (executed.symm.trans trace.hashResumed)
  cases resultEq
  exact retained.1

/-- Actual successful completion supplies its actual nonempty plaintext, exact checked ID prefix, full binding, and application suffix. -/
theorem completed (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (expected : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (result : registration.CompletedBeacon) (before after : S)
    (trace : Trace implementation phase result before after) (metadata : BeaconPhaseMetadata expected phase) :
    ∃ plaintext : Slice U8, trace.openReply = .Some plaintext ∧ 8 < plaintext.val.length ∧
      (plaintext.val.take 8).map absByte = Pqxdh.LE64 expected.candidate.assigned_key_id.val ∧
      result.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding expected.binding expected.candidate.assigned_key_id ∧
      result.application = plaintext.drop 8#usize := by
  have sameAgreement := agreement implementation expected phase result before after trace metadata
  obtain ⟨kernel, _sequence, _sequenceRun, _source, finished⟩ := beacon_completion_refines trace.aead trace.openReply
  have actual := RustM.ok.inj (trace.aeadResumed.symm.trans finished)
  cases replyEq : trace.openReply with
  | none => simp only [replyEq] at actual; cases actual
  | some plaintext =>
    simp only [replyEq] at actual
    split at actual
    · rename_i accepted
      have resultEq : result = completedBeacon trace.aead kernel plaintext := by simpa only [core.result.Result.Ok.injEq] using actual
      refine ⟨plaintext, rfl, accepted.1, ?_, ?_, ?_⟩
      · exact sameAgreement ▸ accepted.2.2
      · rw [resultEq]
        simp only [completedBeacon, sameAgreement]
      · rw [resultEq]; rfl
    · cases actual

end BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields.completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconCompletionFields.completed
