import BeaconcryptCore.Computational.PqxdhServerAuthRootCommon
import BeaconcryptCore.Computational.PqxdhServerAuthSessionRecord

/-! Join the original same-owner seal and decoded record with the actual eleven-field source session. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootExecution
open PqxdhServerAuthRootObserved PqxdhServerAuthRootCommon
open PqxdhSecretInputKdf PqxdhEd25519EufCma
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Actual reachability and the same-owner seal show that the published owner is a real allocated partner. Associated data is retained in the seal receipt, never inferred from decoded-frame equality. -/
theorem owner_matching (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (result : Outcome KemSK) (supported : result ∈ support (game setup codec checks false adversary))
    (j : Fin (Q + 1))
    (owned : entryOwner setup result.context.seed result.context.scalar Q result.state.1.ghost = some j)
    (published : PqxdhServerAuthSessionRecordEvent.Published codec j.val result.state.1.ghost
      (result.state.2.map publicCall)) : MatchingPublication setup result j.val := by
  have original : observed result ∈ support (PqxdhServerAuthObservedGame.game setup codec checks false adversary) := by
    rw [← game_observed, support_map]
    exact ⟨result, supported, rfl⟩
  have actual := PqxdhServerAuthObservedGame.reachable setup codec checks false adversary (observed result) original
  obtain ⟨⟨snap, context, accepted, member, matched⟩, record⟩ := published
  obtain ⟨before, message, atomic, clean⟩ := actual.1.atomic snap accepted
  exact ⟨snap, context, accepted,
    owner_session_ghost setup result.context.seed result.context.scalar Q result.state.1.ghost snap
      (actual.1.frozen snap accepted).1 before message atomic clean j owned
      ((actual.1.sealedBelow (j.val, context) ((actual.1.frozen snap accepted).2.subset member)).trans_le
        (actual.2 Q qH qHash budget)),
    member, matched, PqxdhServerAuthRecordPublicationEvent.record_published codec j.val _ record⟩

/-- The same actual source coordinate has complete eleven-field agreement and earlier publication of the exact accepted decoded record. The common event retains the successful Phase1 generation, both initializations and the chronological matching publication. -/
def Authenticated (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Prop :=
  ∃ index, Common setup codec checks result index ∧
    PqxdhServerAuthRecordPublicationEvent.RecordPublished codec index (result.state.2.map publicCall)

/-- Authentication failure is defined on the actual accepted source execution, without an honest-candidate, partner, publication or unchanged-signed-fields premise. -/
def Failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Prop :=
  (∃ snap, result.state.1.ghost.acceptance = some snap) ∧ ¬ Authenticated setup codec checks result

/-- The complete accepted-session failure is covered by the stronger same-owner record event or the existing all-attempt signed-field substitution event, on this one exact audited run. -/
theorem failure_cases (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify)
    (result : Outcome KemSK) (supported : result ∈ support (game setup codec checks false adversary))
    (failed : Failure setup codec checks result) :
    PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q (PqxdhServerAuthSessionRecord.observers codec Q)
      (observed result) ∨ changed setup codec result = true := by
  cases substituted : changed setup codec result with
  | true => exact Or.inr rfl
  | false =>
      refine Or.inl ⟨failed.1, fun j owned => ?_⟩
      apply (PqxdhServerAuthSessionRecordEvent.observer_true codec j.val result.state.1.ghost
        (result.state.2.map publicCall)).mpr
      exact fun published => failed.2 ⟨j.val,
        game_common setup codec checks adversary result supported j.val
          (owner_matching setup codec checks adversary Q qH qHash budget result supported j owned published)
          adapter substituted,
        published.2⟩

end BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent.owner_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent.owner_matching

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent.failure_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent.failure_cases
