import BeaconcryptCore.Computational.PqxdhServerAuthObservedGame

/-! Accepted observations in the original R1 experiment have the original disclosure/collision losses and the same Q+1 selected schedule reductions. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthObservedEntry
open PqxdhServerAuthObservedGame PqxdhServerAuthIntermediate
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Original accepted observation with no disclosure/collision or owner exclusion. -/
noncomputable def acceptedGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (observer : Observer) : ProbComp Bool :=
  (fun result => @decide (PqxdhServerAuthObservedGame.Accepted observer result) (Classical.propDecidable _)) <$>
    game setup codec checks revealSeed adversary

/-- One same-run accepted-owner event of the original source experiment. -/
noncomputable def ownerGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) : ProbComp Bool :=
  (fun result => @decide (Owned setup Q j observer result) (Classical.propDecidable _)) <$>
    game setup codec checks revealSeed adversary

/-- The original per-owner observed game is exactly the source endpoint of the newly constructed schedule reductions. -/
theorem owner_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) :
    𝒟[ownerGame setup codec checks revealSeed adversary Q j observer] =
      𝒟[PqxdhServerAuthObservedSchedule.actualGame setup codec checks adversary revealSeed Q j observer] := by
  apply evalDist_eq_of_evalSPMF_eq
  convert observed_flat setup codec checks revealSeed adversary (fun seed scalar ghost journal =>
    @decide (PqxdhServerAuthAcceptedEntry.Gate setup seed scalar Q j ghost ∧
      observer (eraseGhost ghost) journal = true) (Classical.propDecidable _)) using 1 <;> rfl

/-- An actual accepted observation is partitioned over the original source bad events and the same owner coordinates. The observation predicate is dropped only in the two charged bad events. -/
theorem accepted_decomposition (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observer : Observer) :
    𝒟[acceptedGame setup codec checks false adversary observer] {true} ≤
      𝒟[originalDisclosureGame setup codec checks adversary] {true} +
      𝒟[originalCollisionGame setup codec checks adversary] {true} +
      ∑ j : Fin (Q + 1), 𝒟[ownerGame setup codec checks false adversary Q j observer] {true} := by
  simpa only [acceptedGame, ownerGame, originalDisclosureGame, originalCollisionGame,
    evalDist_apply_singleton, probOutput_map, decide_eq_true_eq] using
    accepted_probability setup codec checks false adversary Q qH qHash budget observer

/-- Every event and the finite owner sum have finite probability, giving the same partition over real-valued probabilities. -/
theorem accepted_decomposition_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observer : Observer) :
    (𝒟[acceptedGame setup codec checks false adversary observer] {true}).toReal ≤
      (𝒟[originalDisclosureGame setup codec checks adversary] {true}).toReal +
      (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal +
      ∑ j : Fin (Q + 1), (𝒟[ownerGame setup codec checks false adversary Q j observer] {true}).toReal := by
  have finite (work : ProbComp Bool) : 𝒟[work] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have sumFinite : (∑ j : Fin (Q + 1),
      𝒟[ownerGame setup codec checks false adversary Q j observer] {true}) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => finite _
  have bounded := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩, sumFinite⟩)
    (accepted_decomposition setup codec checks adversary Q qH qHash budget observer)
  simpa only [ENNReal.toReal_add (finite _) (finite _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩) sumFinite,
    ENNReal.toReal_sum (fun _ _ => finite _)] using bounded

/-- Each original owner coordinate uses its new observation-dependent schedule reductions, retaining the same journal and selected correlated output. -/
theorem owner_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (observer : Observer)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[ownerGame setup codec checks false adversary Q j observer] {true}).toReal ≤
      (𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j observer] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j observer := by
  simpa only [owner_source] using
    PqxdhServerAuthObservedSchedule.source_uniform setup codec checks adversary false Q j observer correct

open PqxdhServerAuthAssumptions PqxdhServerAuthGapDh

/-- The complete original accepted observation has one original joint Gap-DH loss, the explicit distinct-Server collision loss, and Q+1 newly constructed schedule reductions. The uniform observed endpoints remain explicit obligations. -/
theorem accepted_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash) (observer : Observer)
    (law : X25519ClassLaw setup.source.crypto) (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[acceptedGame setup codec checks false adversary observer] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[PqxdhServerAuthObservedSchedule.uniformGame setup codec checks adversary false Q j observer] {true}).toReal +
        PqxdhServerAuthObservedSchedule.scheduleLoss setup codec checks adversary false Q j observer) := by
  exact (accepted_decomposition_real setup codec checks adversary Q qH qHash budget observer).trans
    (add_le_add (add_le_add (disclosure_le_gapDh setup codec checks adversary qH law budget.rom)
      (collision_le_scalar_spread setup codec checks adversary Q spread budget.accept))
      (Finset.sum_le_sum fun j _ => owner_uniform setup codec checks adversary Q j observer correct))

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts

/-- Resource ledger for the exact reductions in accepted_bound. It retains the unchanged disclosure extractor and the new observation-dependent schedule distinguishers. -/
structure ObservedBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (observer : Observer) (caps : KemCaps)
    (qCoin Q qH qHash : Nat) : Prop where
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
    (PqxdhServerAuthObservedSchedule.reduction setup codec checks adversary false Q j observer)
    (entryReductionBudget caps qCoin Q qHash qH)

/-- Original adversary and primitive-interface caps discharge the same disclosure extractor and every newly constructed schedule reduction, including the full context sampler and interpreted base work. -/
theorem observed_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary) (observer : Observer)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin) :
    ObservedBills setup codec checks adversary observer caps qCoin Q qH qHash := by
  exact ⟨reduction_resources setup codec checks caps bounded adversary qCoin Q qHash qH
      coins budget.accept budget.hash budget.rom,
    gap_game_uniform setup codec checks caps bounded adversary qCoin Q qH qHash budget coins,
    fun j => PqxdhServerAuthObservedSchedule.component_bills setup codec checks caps bounded adversary
      qCoin Q qHash qH coins budget.accept budget.hash budget.rom false j observer⟩

end BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.owner_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_decomposition

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_decomposition_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_decomposition_real

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.owner_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.owner_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.accepted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.observed_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedPartition.observed_bills
