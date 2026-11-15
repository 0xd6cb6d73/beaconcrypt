import BeaconcryptCore.Computational.PqxdhServerAuthCommonEvent
import BeaconcryptCore.Computational.PqxdhServerAuthTranscriptCollision

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

/-- The final mathematical failure-or-collision decision: authentication failure, or two distinct BLAKE2b inputs with one digest in the final cache. It changes no source operation or reply. -/
noncomputable def collisionDecision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (result : Outcome KemSK) : Bool :=
  @decide (FailureOrCollision setup codec checks result) (Classical.propDecidable _)

/-- Authentication failure is contained in failure-or-collision, so its production-order probability is at most the failure-or-collision probability. -/
theorem decision_le_collision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) :
    (𝒟[decision setup codec checks <$> orderedGame setup codec checks false adversary] {true}).toReal ≤
      (𝒟[collisionDecision setup codec checks <$> orderedGame setup codec checks false adversary] {true}).toReal := by
  refine ENNReal.toReal_mono ?_ ?_
  · rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  · simp only [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
    exact prEvent_mono _ _ _ fun result failed => by
      simp only [decision, collisionDecision, decide_eq_true_eq] at failed ⊢
      exact Or.inl failed

/-- The complete eleven-field and decoded-record failure, or a collision of the final BLAKE2b cache, splits into three events on the same sampled execution. No target, field or attempted-call selection loss is inserted at this join. -/
theorem failure_or_collision_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    Pr{let x ← game setup codec checks false adversary}[(FailureOrCollision setup codec checks) x] ≤
      Pr{let result ← game setup codec checks false adversary}[PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q
        (PqxdhServerAuthSessionRecord.observers codec Q) (observed result)] +
      Pr{let result ← game setup codec checks false adversary}[changed setup codec result = true] +
      Pr{let result ← game setup codec checks false adversary}[CacheHasCollision result.state.1.ctx] := by
  refine (prEvent_mono_of_support (game setup codec checks false adversary) _
    (fun result => (PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q
      (PqxdhServerAuthSessionRecord.observers codec Q) (observed result) ∨
      changed setup codec result = true) ∨ CacheHasCollision result.state.1.ctx) ?_).trans
    ((prEvent_or_le _ _ _).trans (add_le_add_left (prEvent_or_le _ _ _) _))
  intro result supported failed
  rcases failure_cases_or_collision setup codec checks adversary Q qH qHash budget adapter result supported failed
    with accepted | substituted | collided
  · exact Or.inl (Or.inl accepted)
  · exact Or.inl (Or.inr substituted)
  · exact Or.inr collided

/-- The complete eleven-field and decoded-record failure splits into three events on the same sampled execution: the same-owner record event, the signed-field substitution event and a collision of the final BLAKE2b cache. No target, field or attempted-call selection loss is inserted at this join. -/
theorem failure_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    Pr{let x ← game setup codec checks false adversary}[(Failure setup codec checks) x] ≤
      Pr{let result ← game setup codec checks false adversary}[PqxdhServerAuthPublicationOwnerFamily.Accepted setup Q
        (PqxdhServerAuthSessionRecord.observers codec Q) (observed result)] +
      Pr{let result ← game setup codec checks false adversary}[changed setup codec result = true] +
      Pr{let result ← game setup codec checks false adversary}[CacheHasCollision result.state.1.ctx] :=
  (prEvent_mono_of_support (game setup codec checks false adversary) _ _
    (fun _ _ failed => Or.inl failed)).trans
    (failure_or_collision_split setup codec checks adversary Q qH qHash budget adapter)

/-- Production-order failure-or-collision is bounded by the two exact source events whose constructed reductions are already established and the collision of the final BLAKE2b cache. All projections retain the same complete continuation and state. -/
theorem collision_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    (𝒟[collisionDecision setup codec checks <$> orderedGame setup codec checks false adversary] {true}).toReal ≤
      (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
        (PqxdhServerAuthPublicationOwnerFamily.observation setup Q
          (PqxdhServerAuthSessionRecord.observers codec Q))] {true}).toReal +
      (𝒟[PqxdhServerAuthJointIdentityEuf.sourceBad setup codec checks adversary] {true}).toReal +
      (𝒟[PqxdhServerAuthTranscriptCollision.collision <$> orderedGame setup codec checks false adversary]
        {true}).toReal := by
  have split := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩, prEvent_ne_top _⟩)
    (failure_or_collision_split setup codec checks adversary Q qH qHash budget adapter)
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) (prEvent_ne_top _),
    ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at split
  rw [← observation_order setup codec checks false adversary (collisionDecision setup codec checks),
    PqxdhServerAuthPublicationOwnerFamily.ordered_source, ← source_bad,
    ← observation_order setup codec checks false adversary PqxdhServerAuthTranscriptCollision.collision]
  rw [PqxdhServerAuthPublicationOwnerFamily.acceptedGame, ← game_observed]
  simpa only [← prEvent_eq_evalDist_singleton _ true, prEvent_map, collisionDecision,
    PqxdhServerAuthTranscriptCollision.collision, Function.comp_def, decide_eq_true_eq] using split

/-- Production-order complete session failure is bounded by the two exact source events whose constructed reductions are already established and the collision of the final BLAKE2b cache. All projections retain the same complete continuation and state. -/
theorem ordered_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (adapter : HasAttachedVerificationAdapter
      (fun identity => setup.source.crypto.verify identity.toList) setup.joint.verify) :
    (𝒟[decision setup codec checks <$> orderedGame setup codec checks false adversary] {true}).toReal ≤
      (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
        (PqxdhServerAuthPublicationOwnerFamily.observation setup Q
          (PqxdhServerAuthSessionRecord.observers codec Q))] {true}).toReal +
      (𝒟[PqxdhServerAuthJointIdentityEuf.sourceBad setup codec checks adversary] {true}).toReal +
      (𝒟[PqxdhServerAuthTranscriptCollision.collision <$> orderedGame setup codec checks false adversary]
        {true}).toReal :=
  (decision_le_collision setup codec checks adversary).trans
    (collision_split setup codec checks adversary Q qH qHash budget adapter)

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

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.failure_or_collision_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.failure_or_collision_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.collision_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.collision_split

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.decision_le_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCommonProbability.decision_le_collision
