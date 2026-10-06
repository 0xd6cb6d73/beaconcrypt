-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointFinalReportEvent
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding

/-! The chosen candidate's complete-tuple origin event is stated on the actual source signing and reveal transcript at the actual addressed owner. Its implication to the ordinary public detector is derived from the initialized source invariant. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhRegistrationJointFinalCandidate
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}

/-- A fresh generated source owner is addressed by the adversary's original result. Its accepted original candidate has no complete chronological signing-attempt origin. Imported candidates, rejection and compromised targets stay in the experiment, outside this protected event. -/
def Failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : Nat}
    (result : ReportResult KemSK A Choice count) : Prop :=
  ∃ (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Choice)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count)
    (candidate : Phase1Candidate) (publicKey : PublicIdentity) (decoded : Phase1KeyTuple),
    (sourceResult result).1 = some encoded ∧
    encoded.2.2.owners[encoded.2.1.1]? = some owner ∧
    selected codec result.1 = some candidate ∧
    result.1.2.refs[owner.1]? = some (.generated target.val) ∧
    sourceKeys setup.joint (sourceResult result).2.1.1.seeds owner.1 = some publicKey ∧
    acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded) ∧
    PqxdhRegistrationJointRoutedReveals.revealedAt owner.1 (sourceResult result).2.1.1.transcript = false ∧
    ¬PqxdhRegistrationJointAttemptDecoding.Occurred decoded
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult result).2.1.1.transcript)

/-- The actual initialized owner invariant supplies the complete real attempt history, so a protected native tuple-origin failure is an original-field report failure with no extra premise about history, key ownership or honest target selection. -/
theorem public_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (result : ReportResult KemSK A Choice count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)))
    (failed : Failure setup codec result) :
    PqxdhRegistrationJointFinalReportEvent.Failure setup.joint codec result := by
  obtain ⟨encoded, owner, target, candidate, publicKey, decoded,
    finished, found, chosen, generated, key, accepted, fresh, absent⟩ := failed
  obtain ⟨receipt, _, exactHistory, _, origin⟩ :=
    PqxdhRegistrationJointAttemptReports.owner_origin setup codec checks ensureInit supplied count program runtime
      result supported encoded finished encoded.2.1.1 owner found target generated publicKey candidate decoded key accepted fresh
  rcases origin with issued | forged
  · exact False.elim (absent ⟨receipt.attempts, exactHistory, issued⟩)
  · exact ⟨target.val, candidate, chosen, forged⟩

/-- The protected complete-tuple origin failure in the literal native stopping execution is bounded by the ordinary final-report detector without a selection loss. -/
theorem transport (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A) :
    letI := Classical.propDecidable
    𝒟[(fun result => decide (Failure setup codec result)) <$>
      PqxdhJointPhase1Reports.run setup.joint count
        (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)] {true} ≤
    𝒟[(fun result => result.2.1.occurred) <$>
      PqxdhJointPhase1Reports.run setup.joint count (client setup codec checks ensureInit supplied count program runtime)] {true} := by
  classical
  apply le_trans _ (PqxdhRegistrationJointFinalReportEvent.transport setup codec checks ensureInit supplied count program runtime)
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map,
    evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result supported failed
  simpa only [Function.comp_apply, decide_eq_true_eq] using public_failure setup codec checks ensureInit supplied count program runtime result supported
    (of_decide_eq_true failed)

end BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent.public_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent.public_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent.transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent.transport
