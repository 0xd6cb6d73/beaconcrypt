import BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent

/-! Probability composition on the exact original audited source experiment. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootExecution
open PqxdhServerAuthRootObserved PqxdhServerAuthCommonEvent
open PqxdhSecretInputKdf PqxdhEd25519EufCma
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The final mathematical failure decision changes no source operation or reply; its private witnesses remain outside the adversary's interface. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Bool :=
  @decide (Failure setup codec checks result) (Classical.propDecidable _)

set_option linter.deprecated false in
/-- The complete eleven-field and decoded-record failure splits into two events on the same sampled execution. No target, field or attempted-call selection loss is inserted at this join. -/
theorem failure_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    Pr[Failure setup codec checks | game setup codec checks false adversary] ≤
      Pr[fun result => PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q
        (PqxdhServerAuthSessionRecord.observers codec Q) (observed result) |
        game setup codec checks false adversary] +
      Pr[fun result => changed setup codec result = true | game setup codec checks false adversary] := by
  refine (probEvent_mono (mx := game setup codec checks false adversary)
    (q := fun result => PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q
      (PqxdhServerAuthSessionRecord.observers codec Q) (observed result) ∨
      changed setup codec result = true) ?_).trans (probEvent_or_le _ _ _)
  exact fun result supported failed => failure_cases setup codec checks adversary Q qH qHash budget adapter
    result supported failed

set_option linter.deprecated false in
/-- Production-order complete session failure is bounded by the two exact source events whose constructed reductions are already established. Both projections retain the same complete continuation and state. -/
theorem ordered_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    (𝒟[decision setup codec checks <$> orderedGame setup codec checks false adversary] {true}).toReal ≤
      (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
        (PqxdhServerAuthPublicationOwnerFamily.observation setup Q
          (PqxdhServerAuthSessionRecord.observers codec Q))] {true}).toReal +
      (𝒟[PqxdhServerAuthJointIdentityEuf.sourceBad setup codec checks adversary] {true}).toReal := by
  have split := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩)
    (failure_split setup codec checks adversary Q qH qHash budget adapter)
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at split
  rw [← observation_order setup codec checks false adversary (decision setup codec checks),
    PqxdhServerAuthPublicationOwnerFamily.ordered_source, ← source_bad]
  rw [PqxdhServerAuthPublicationOwnerFamily.acceptedGame, ← game_observed]
  simpa only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map,
    Function.comp_def, decision, decide_eq_true_eq] using split

end BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.failure_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.failure_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.ordered_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.ordered_split
