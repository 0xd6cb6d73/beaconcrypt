-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointNativeOriginEvent

/-! The actual chronological attempt invariant connects a selected original candidate to the same native owner's immutable KEM key. Failure is the previously charged native tuple-origin event, not a new authenticity premise. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin
open PqxdhJointIdentity PqxdhDynamicIdentityReports PqxdhEd25519EufCma PqxdhServerAuthExperiment
open PqxdhRegistrationJointFinalCandidate (Choice selected)
open PqxdhRegistrationJointInitializedReports (ReportResult sourceResult)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}

/-- Reattaching private source pools does not change the selected original raw bytes. -/
theorem selected_source (codec : Codec Reader Response) {count : Nat}
    (result : ReportResult KemSK A Choice count)
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Choice)
    (finished : (sourceResult result).1 = some encoded) :
    selected codec result.1 = PqxdhRegistrationJointRawSignatures.candidate codec encoded.2.1.2 := by
  change Option.map _ result.1.1.1 = some encoded at finished
  obtain ⟨original, found, rfl⟩ := Option.map_eq_some_iff.mp finished
  simp only [selected, found, Option.bind_some, PqxdhRegistrationJointOpenInitialization.attach]

/-- Every protected addressed generated owner has either the exact issued tuple and native KEM public key, or the already defined native tuple-origin failure, which `NativeOriginEvent.transport` bounds by the final-report detector with coefficient one. No premise selects an honest incoming tuple. Acceptance is the detached `acceptPhase1Candidate setup.joint.verify` interface under the owner's source identity key, not the attached source verification. -/
theorem key_or_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Choice) (runtime : A)
    (result : ReportResult KemSK A Choice count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)))
    (encoded : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK Choice)
    (owner : PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (target : Fin count)
    (candidate : Phase1Candidate) (publicKey : PublicIdentity) (decoded : Phase1KeyTuple)
    (finished : (sourceResult result).1 = some encoded)
    (found : encoded.2.2.owners[encoded.2.1.1]? = some owner)
    (chosen : selected codec result.1 = some candidate)
    (generated : result.1.2.refs[owner.1]? = some (.generated target.val))
    (key : sourceKeys setup.joint (sourceResult result).2.1.1.seeds owner.1 = some publicKey)
    (accepted : acceptPhase1Candidate setup.joint.verify candidate = some (publicKey.ed25519, decoded))
    (fresh : PqxdhRegistrationJointRoutedReveals.revealedAt owner.1 (sourceResult result).2.1.1.transcript = false) :
    (PqxdhRegistrationJointAttemptDecoding.Occurred decoded
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult result).2.1.1.transcript) ∧
      ((sourceResult result).2.1.2.keys[owner.2.1]?).map Prod.fst = some decoded.pqKey) ∨
    PqxdhRegistrationJointNativeOriginEvent.Failure setup codec result := by
  classical
  obtain ⟨receipt, fixed, exactHistory, nativeKey, _⟩ :=
    PqxdhRegistrationJointAttemptReports.owner_origin setup codec checks ensureInit supplied count program runtime
      result supported encoded finished encoded.2.1.1 owner found target generated publicKey candidate decoded key accepted fresh
  by_cases occurred : PqxdhRegistrationJointAttemptDecoding.Occurred decoded
      (PqxdhRegistrationJointSigningTranscript.messagesAt owner.1 (sourceResult result).2.1.1.transcript)
  · have member := (PqxdhRegistrationJointAttemptDecoding.occurred_iff decoded receipt.attempts).mp (exactHistory ▸ occurred)
    exact Or.inl ⟨occurred, nativeKey.trans (congrArg some (fixed decoded member).2.symm)⟩
  · exact Or.inr ⟨encoded, owner, target, candidate, publicKey, decoded,
      finished, found, chosen, generated, key, accepted, fresh, occurred⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin.selected_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin.key_or_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointNativeKemOrigin.key_or_failure
