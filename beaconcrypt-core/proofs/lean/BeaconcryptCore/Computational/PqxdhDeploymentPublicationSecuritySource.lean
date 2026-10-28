-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityFresh
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionEligible

/-! Actual modified source-state events are joined to the genuine ordinary report client. The complete source and native result are reconstructed only after the external challenger executes; no identity seed enters the executable client. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentPublicationSuppressionInitialized
open PqxdhDeploymentPublicationSuppressionGenerated (ReportResult)
open PqxdhDeploymentPublicationSecurityFresh
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

/-- Every reconstructed successful encoded state contains exactly the final actual private pool. -/
theorem projected_pool (count : Nat) (reached : ReportResult KemSK A Result count)
    (outcome : EncodedOutcome KemSK Result)
    (present : (initializedResult (reached.1, reached.2.2.source.2)).1 = some outcome) :
    outcome.2.2.1.pool = (initializedResult (reached.1, reached.2.2.source.2)).2.1 := by
  unfold initializedResult at present ⊢
  obtain ⟨original, _, equal⟩ := Option.map_eq_some_iff.mp present
  subst outcome
  rfl

/-- The reconstructed source transcript is the literal returned public transcript of the same actual client. -/
theorem projected_transcript (count : Nat) (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (reached : ReportResult KemSK A Result count) (outcome : EncodedOutcome KemSK Result)
    (present : (initializedResult (reached.1, reached.2.2.source.2)).1 = some outcome) :
    finalTranscript transcript reached.1 = transcript outcome.2.1 := by
  unfold initializedResult at present
  obtain ⟨original, originalFound, equal⟩ := Option.map_eq_some_iff.mp present
  subst outcome
  change reached.1.1.1 = some original at originalFound
  simp only [finalTranscript, attach, originalFound, Option.map_some, Option.getD_some]

/-- An actual modified-source fresh candidate is eligible for the existing terminal reporting reduction. Generated origin, index bounds and unrevealed status are proved from this very client. -/
theorem report_eligible (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (identityReads : budget (.inr 0) = 0) (kemReads : budget (.inr 1) = 0)
    (creationCap : 1 + budget (.inl 1) ≤ count) (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (reached : ReportResult KemSK A Result count)
    (supported : reached ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (sourceClient setup codec checks ensureInit none ordinal program runtime)))
    (happened : EncodedEvent setup codec transcript (initializedResult (reached.1, reached.2.2.source.2))) :
    PqxdhDeploymentPublicationSecurityClient.Eligible setup.joint codec (finalTranscript transcript) reached := by
  obtain ⟨created, result, state, present, target, candidate, publicKey, decoded, _, _, fresh,
    member, keyFound, accepted, sameKey⟩ := happened
  have samePool := projected_pool count reached (created, result, state) present
  have sameTranscript := projected_transcript count transcript reached (created, result, state) present
  apply PqxdhDeploymentPublicationSuppressionEligible.sourceClient_eligible setup codec checks ensureInit ordinal count
    program runtime budget certified identityReads kemReads creationCap transcript reached supported target.identityIndex
    publicKey candidate decoded
  · simpa only [sameTranscript] using member
  · simpa only [← samePool] using keyFound
  · exact accepted
  · simpa only [← samePool] using oneTime_unissued setup.joint state.1.pool.1 target candidate publicKey.ed25519 decoded
      accepted sameKey fresh

/-- Exact full-source reconstruction transfers the modified fresh-candidate event to the genuine report client, where the original terminal batches detect it. -/
theorem source_eligible (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (identityReads : budget (.inr 0) = 0) (kemReads : budget (.inr 1) = 0)
    (creationCap : 1 + budget (.inl 1) ≤ count) (transcript : Result → List PqxdhDeploymentInterface.Entry) :
    Pr{let outcome ← ((source setup codec checks ensureInit none ordinal program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))}[SourceEvent setup codec transcript outcome] ≤
    Pr{let reached ← (PqxdhJointPhase1Reports.run setup.joint count
        (sourceClient setup codec checks ensureInit none ordinal program runtime))}[PqxdhDeploymentPublicationSecurityClient.Eligible setup.joint codec (finalTranscript transcript) reached] := by
  have correspondence := congrArg (fun computation => Pr{let outcome ← computation}[EncodedEvent setup codec transcript outcome])
    (sourceClient_source setup codec checks ensureInit none ordinal count program runtime)
  simp only [prEvent_map] at correspondence
  have exactEvent : Pr{let outcome ← ((source setup codec checks ensureInit none ordinal program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))}[EncodedEvent setup codec transcript (outcome.1.map (encodeOutcome setup), outcome.2)] =
      Pr{let outcome ← ((source setup codec checks ensureInit none ordinal program).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))}[SourceEvent setup codec transcript outcome] :=
    prEvent_congr _ _ _ (encode_event setup codec transcript)
  rw [← exactEvent, ← correspondence]
  exact prEvent_mono_of_support _ _ _ fun reached supported happened =>
    report_eligible setup codec checks ensureInit ordinal count program runtime budget certified identityReads kemReads
      creationCap transcript reached supported happened

/-- A genuine selected source client supplies ordinary joint-use weak-EUF reductions for the complete modified experiment, with no final-event detection premise. -/
theorem source_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (ordinal count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (identityReads : budget (.inr 0) = 0) (kemReads : budget (.inr 1) = 0)
    (creationCap : 1 + budget (.inl 1) ≤ count + 1) (transcript : Result → List PqxdhDeploymentInterface.Entry)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let outcome ← ((source setup codec checks ensureInit none ordinal program).run
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))}[SourceEvent setup codec transcript outcome] ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (PqxdhDeploymentPublicationSecurityReduction.reduction setup.joint count
          (PqxdhDeploymentPublicationSecurityClient.terminal codec (count + 1) (finalTranscript transcript)
            (sourceClient setup codec checks ensureInit none ordinal program runtime)) fallback ordinaryFallback target) := by
  apply (source_eligible setup codec checks ensureInit ordinal (count + 1) program runtime budget certified identityReads
    kemReads creationCap transcript).trans
  apply PqxdhDeploymentPublicationSecurityClient.eligible_bound
  exact (PqxdhDeploymentPublicationSuppressionCosts.sourceClient_creates setup codec checks ensureInit none ordinal
    program runtime budget certified).mono creationCap

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.projected_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.projected_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.projected_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.projected_transcript

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.report_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.report_eligible

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.source_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.source_eligible

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecuritySource.source_bound
