import BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution

/-! Publication observations retain the literal source owner coordinate across the existing accepted-event partition and five schedule changes. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedEntry
open PqxdhServerAuthObservedGame PqxdhServerAuthIntermediate
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Only the actual owner selects a member of the root-erased observer family. If no owner is available, the accepted event is retained for the original bad-event partition rather than silently discarded. -/
def Accepted (setup : Setup baseSpec KemSK) (Q : Nat) (observers : Fin (Q + 1) → Observer)
    (result : PqxdhServerAuthObservedGame.Result KemSK) : Prop :=
  (∃ snap, result.2.2.1.2.ghost.acceptance = some snap) ∧
    ∀ j, entryOwner setup result.1 result.2.1 Q result.2.2.1.2.ghost = some j →
      observers j (eraseGhost result.2.2.1.2.ghost) result.2.2.1.1 = true

/-- The exact source event is not weakened to publication by an arbitrary matching-field session. The family member is indexed by the actual source owner. -/
noncomputable def acceptedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q : Nat) (observers : Fin (Q + 1) → Observer) : ProbComp Bool :=
  (fun result => @decide (Accepted setup Q observers result) (Classical.propDecidable _)) <$>
    game setup codec checks revealSeed adversary

/-- Actual source reachability partitions an accepted family observation into the original bad events or its own literal owner coordinate. -/
theorem accepted_cases (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) (observers : Fin (Q + 1) → Observer)
    (result : PqxdhServerAuthObservedGame.Result KemSK)
    (supported : result ∈ support (game setup codec checks revealSeed adversary))
    (accepted : Accepted setup Q observers result) :
    BadB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      CollB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), Owned setup Q j (observers j) result := by
  have actual := reachable setup codec checks revealSeed adversary result supported
  rcases PqxdhServerAuthAcceptedEntry.accepted_cases setup result.1 result.2.1 Q result.2.2.1.2.ghost
    result.2.2.1.2.sessions actual.1.touched (actual.2 Q qH qHash budget) accepted.1 with
    bad | coll | ⟨j, owned⟩
  · exact Or.inl bad
  · exact Or.inr (Or.inl coll)
  · exact Or.inr (Or.inr ⟨j, Finset.mem_univ j, owned, accepted.2 j owned.2.2.2⟩)
set_option linter.deprecated false in
/-- The chronological observed event is charged to the original source disclosure/collision games and the same finite family of owner events. Observation conditions are dropped only on those two explicitly charged bad branches. -/
theorem accepted_probability (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) (observers : Fin (Q + 1) → Observer) :
    Pr[Accepted setup Q observers | game setup codec checks revealSeed adversary] ≤
      Pr[fun result => BadB setup result.1 result.2.1 result.2.2.1.ghost |
        gameState setup codec checks revealSeed adversary] +
      Pr[fun result => CollB setup result.1 result.2.1 result.2.2.1.ghost |
        gameState setup codec checks revealSeed adversary] +
      ∑ j : Fin (Q + 1), Pr[Owned setup Q j (observers j) | game setup codec checks revealSeed adversary] := by
  classical
  simp only [← game_erase setup codec checks revealSeed adversary, probEvent_map, Function.comp_def, erase]
  refine le_trans (probEvent_mono (q := fun result : Result KemSK =>
    BadB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
      (CollB setup result.1 result.2.1 result.2.2.1.2.ghost ∨
        ∃ j ∈ (Finset.univ : Finset (Fin (Q + 1))), Owned setup Q j (observers j) result))
    (fun result supported accepted => accepted_cases setup codec checks revealSeed adversary Q qH qHash
      budget observers result supported accepted)) ?_
  refine le_trans (probEvent_or_le (game setup codec checks revealSeed adversary) _ _) ?_
  rw [add_assoc]
  exact add_le_add le_rfl (le_trans (probEvent_or_le (game setup codec checks revealSeed adversary) _ _)
    (add_le_add le_rfl (probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin (Q + 1)))
      (game setup codec checks revealSeed adversary) _)))

/-- An actual accepted observation is partitioned over the original source bad events and the same owner coordinates. The observation predicate is dropped only in the two charged bad events. -/
theorem accepted_decomposition (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observers : Fin (Q + 1) → Observer) :
    𝒟[acceptedGame setup codec checks false adversary Q observers] {true} ≤
      𝒟[originalDisclosureGame setup codec checks adversary] {true} +
      𝒟[originalCollisionGame setup codec checks adversary] {true} +
      ∑ j : Fin (Q + 1), 𝒟[PqxdhServerAuthObservedPartition.ownerGame setup codec checks false adversary Q j (observers j)] {true} := by
  simpa only [acceptedGame, PqxdhServerAuthObservedPartition.ownerGame, originalDisclosureGame, originalCollisionGame,
    evalDist_apply_singleton, probOutput_map, decide_eq_true_eq] using
    accepted_probability setup codec checks false adversary Q qH qHash budget observers

/-- Every event and the finite owner sum have finite probability, giving the same partition over real-valued probabilities. -/
theorem accepted_decomposition_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observers : Fin (Q + 1) → Observer) :
    (𝒟[acceptedGame setup codec checks false adversary Q observers] {true}).toReal ≤
      (𝒟[originalDisclosureGame setup codec checks adversary] {true}).toReal +
      (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal +
      ∑ j : Fin (Q + 1), (𝒟[PqxdhServerAuthObservedPartition.ownerGame setup codec checks false adversary Q j (observers j)] {true}).toReal := by
  have finite (work : ProbComp Bool) : 𝒟[work] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have sumFinite : (∑ j : Fin (Q + 1),
      𝒟[PqxdhServerAuthObservedPartition.ownerGame setup codec checks false adversary Q j (observers j)] {true}) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => finite _
  have bounded := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩, sumFinite⟩)
    (accepted_decomposition setup codec checks adversary Q qH qHash budget observers)
  simpa only [ENNReal.toReal_add (finite _) (finite _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩) sumFinite,
    ENNReal.toReal_sum (fun _ _ => finite _)] using bounded

open PqxdhServerAuthAssumptions PqxdhServerAuthGapDh

/-- The complete original accepted observation has one original joint Gap-DH loss, the explicit distinct-Server collision loss, and Q+1 newly constructed schedule reductions. The uniform observed endpoints remain explicit obligations. -/
theorem accepted_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observers : Fin (Q + 1) → Observer)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[acceptedGame setup codec checks false adversary Q observers] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j (observers j)] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j (observers j)) := by
  exact (accepted_decomposition_real setup codec checks adversary Q qH qHash budget observers).trans
    (add_le_add (add_le_add (disclosure_le_gapDh setup codec checks adversary qH law budget.rom)
      (collision_le_scalar_spread setup codec checks adversary Q spread budget.accept))
      (Finset.sum_le_sum fun j _ => PqxdhServerAuthObservedPartition.owner_uniform setup codec checks adversary Q j (observers j) correct))

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts

/-- Resource ledger for the exact reductions in accepted_bound. It retains the unchanged disclosure extractor and the new observation-dependent schedule distinguishers. -/
structure ObservedBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (observers : Fin (Q + 1) → Observer) (caps : KemCaps)
    (qCoin qH qHash : Nat) : Prop where
  gapInterface : ∀ publicValue,
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
      PqxdhJointGapDh.IsSigning 0 ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
      PqxdhJointGapDh.IsDecision (2 * qH * (Q + 1) + 2 * (Q + 1) * (qH + Q + 1) + qH) ∧
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH) publicValue).IsQueryBoundP
      PqxdhJointGapDh.IsUniform (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1))
  gapGame : (PqxdhJointGapDh.game setup.joint setup.dh
    (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH)
  entries : ∀ j : Fin (Q + 1), EntryComponentBills setup.source setup.hmac
    (PqxdhServerAuthObservedSchedule.reduction setup codec checks adversary false Q j (observers j))
    (entryReductionBudget caps qCoin Q qHash qH)

/-- Original adversary and primitive-interface caps discharge the same disclosure extractor and every newly constructed schedule reduction, including the full context sampler and interpreted base work. -/
theorem observed_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (observers : Fin (Q + 1) → Observer) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin) :
    ObservedBills setup codec checks adversary Q observers caps qCoin qH qHash := by
  exact ⟨reduction_resources setup codec checks caps bounded adversary qCoin Q qHash qH
      coins budget.accept budget.hash budget.rom,
    gap_game_uniform setup codec checks caps bounded adversary qCoin Q qH qHash budget coins,
    fun j => PqxdhServerAuthObservedSchedule.component_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom false j (observers j)⟩

/-- The source event evaluates ownership in the mathematical source state and gives only that public coordinate's root-erased ghost and journal to its observer. No owner is silently dropped. -/
noncomputable def observation (setup : Setup baseSpec KemSK) (Q : Nat)
    (observers : Fin (Q + 1) → Observer) : PqxdhServerAuthObservedGame.Observation := fun seed scalar ghost journal =>
  @decide ((∃ snap, ghost.acceptance = some snap) ∧
    ∀ j, entryOwner setup seed scalar Q ghost = some j → observers j (eraseGhost ghost) journal = true)
    (Classical.propDecidable _)

/-- The literal production-order native execution has exactly the same owner-indexed accepted observation as the source game being partitioned. -/
theorem ordered_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (observers : Fin (Q + 1) → Observer) :
    𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary revealSeed
      (observation setup Q observers)] =
      𝒟[acceptedGame setup codec checks revealSeed adversary Q observers] := by
  convert PqxdhServerAuthObservedExecution.ordered_observed setup codec checks adversary revealSeed
    (observation setup Q observers) using 1
  rfl

/-- The original native accepted owner-family event has the same single disclosure extractor, scalar-collision term, and Q+1 observer-indexed schedule reductions with the concrete complete ledger. Its uniform publication probabilities remain to be bounded. -/
theorem ordered_bound_with_resources (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (observers : Fin (Q + 1) → Observer)
    (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false
      (observation setup Q observers)] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j
        (observers j)] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j (observers j)) ∧
    ObservedBills setup codec checks adversary Q observers caps qCoin qH qHash := by
  simpa only [ordered_source] using
    And.intro (accepted_bound setup codec checks adversary Q qH qHash budget observers law spread correct)
      (observed_bills setup codec checks caps bounded adversary qCoin Q qH qHash observers budget coins)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_cases
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_decomposition
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_decomposition_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_decomposition_real
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.accepted_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.observed_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.observed_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.ordered_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.ordered_source
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.ordered_bound_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily.ordered_bound_with_resources
