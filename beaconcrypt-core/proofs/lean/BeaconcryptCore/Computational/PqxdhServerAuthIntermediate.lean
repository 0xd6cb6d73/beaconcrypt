import BeaconcryptCore.Computational.PqxdhServerAuthEntryReductionResources
import BeaconcryptCore.Computational.PqxdhServerAuthCollision

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthIntermediate
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhServerAuthGapDh PqxdhServerAuthAssumptions PqxdhServerAuthCollision
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The original no-seed-reveal experiment, observed only at its actual Extract-input disclosure event. -/
noncomputable def originalDisclosureGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (BadB setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    gameState setup codec checks false adversary

/-- The same original experiment, observed only at its narrowed distinct-Server-attempt collision event. -/
noncomputable def originalCollisionGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (CollB setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    gameState setup codec checks false adversary

/-- The original experiment's checked event partition is retained exactly; no event partition is assumed by the composition. -/
theorem original_event_decomposition (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) :
    𝒟[serverAuthGame setup codec checks false adversary] {true} ≤
      𝒟[originalDisclosureGame setup codec checks adversary] {true} +
      𝒟[originalCollisionGame setup codec checks adversary] {true} +
      ∑ j : Fin (Q + 1), 𝒟[actualEntryGame setup codec checks adversary false Q j] {true} := by
  classical
  simpa only [← prEvent_eq_evalDist_singleton _ true, originalDisclosureGame, originalCollisionGame,
    actualEntryGame, prEvent_map, decide_eq_true_eq] using
    win_le_games setup codec checks false adversary Q qH qHash budget

/-- The same finite source decomposition in real-valued probabilities, with finiteness discharged for every event term. -/
theorem original_event_decomposition_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (𝒟[originalDisclosureGame setup codec checks adversary] {true}).toReal +
      (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal +
      ∑ j : Fin (Q + 1), (𝒟[actualEntryGame setup codec checks adversary false Q j] {true}).toReal := by
  have finite (work : ProbComp Bool) : 𝒟[work] {true} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
  have sumFinite : (∑ j : Fin (Q + 1),
      𝒟[actualEntryGame setup codec checks adversary false Q j] {true}) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun _ _ => finite _
  have bounded := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩, sumFinite⟩)
    (original_event_decomposition setup codec checks adversary Q qH qHash budget)
  simpa only [ENNReal.toReal_add (finite _) (finite _),
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨finite _, finite _⟩) sumFinite,
    ENNReal.toReal_sum (fun _ _ => finite _)] using bounded

/-- The actual source disclosure event costs one instance of the already constructed joint Gap-DH extractor, with no session-selection multiplier. -/
theorem disclosure_le_gapDh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (qH : Nat)
    (law : X25519ClassLaw setup.source.crypto)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH) :
    (𝒟[originalDisclosureGame setup codec checks adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal := by
  have bounded : 𝒟[originalDisclosureGame setup codec checks adversary] {true} ≤
      serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH)) := by
    simpa only [← prEvent_eq_evalDist_singleton _ true, originalDisclosureGame, prEvent_map, decide_eq_true_eq] using
      badB_le_gapDh setup codec checks adversary qH law rom
  exact ENNReal.toReal_mono (prEvent_ne_top _) bounded

/-- The original authentication game is bounded by one constructed Gap-DH advantage, its actual collision event and the finite family of actual uniform-entry games with their same five constructed losses. CTX closure remains explicit. -/
theorem authentication_intermediate (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash)
    (law : X25519ClassLaw setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal +
      ∑ j : Fin (Q + 1), ((𝒟[uniformEntryGame setup codec checks adversary false Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary false Q j) := by
  apply (original_event_decomposition_real setup codec checks adversary Q qH qHash budget).trans
  apply add_le_add
  · exact add_le_add (disclosure_le_gapDh setup codec checks adversary qH law budget.rom) le_rfl
  · exact Finset.sum_le_sum (fun j _ => entry_le_uniform setup codec checks adversary false Q j correct)

/-- The existing adaptive scalar-spread theorem bounds the same original collision event; Q counts every accept attempt, including rejection. -/
theorem collision_le_scalar_spread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat)
    (spread : X25519ScalarSpread setup.source.crypto)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q) :
    (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal ≤
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) := by
  have bounded : 𝒟[originalCollisionGame setup codec checks adversary] {true} ≤
      (Q.choose 2 : ℝ≥0∞) * 64 / (2 ^ 256 : ℝ≥0∞) := by
    simpa only [← prEvent_eq_evalDist_singleton _ true, originalCollisionGame, prEvent_map, decide_eq_true_eq] using
      collB_probability setup codec checks spread adversary Q accepts false
  have realBound := ENNReal.toReal_mono
    (ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num)) (by norm_num)) bounded
  simpa [ ] using realBound

/-- The intermediate original-R1 authentication bound with the checked adaptive collision term. It still exposes the remaining CTX entry games rather than assuming their security. -/
theorem authentication_intermediate_scalar (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q qH qHash : Nat)
    (budget : AuthBudget adversary Q qH qHash)
    (law : X25519ClassLaw setup.source.crypto)
    (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[uniformEntryGame setup codec checks adversary false Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary false Q j) := by
  apply (authentication_intermediate setup codec checks adversary Q qH qHash budget law correct).trans
  exact add_le_add (add_le_add le_rfl
    (collision_le_scalar_spread setup codec checks adversary Q spread budget.accept)) le_rfl

open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts

/-- The actual Gap-DH challenger and extractor use the same expanded source uniform budget as each context-folded entry reduction. The challenge's two 32-byte draws are included. -/
theorem gap_game_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin) :
    (PqxdhJointGapDh.game setup.joint setup.dh
      (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).IsTotalQueryBound
        (entryReductionBudget caps qCoin Q qHash qH) := by
  have same : 64 + (bodyCoinBudget caps qCoin Q qHash + 64 * (qH + Q + 1)) =
      entryReductionBudget caps qCoin Q qHash qH :=
    (reduction_game_budget caps qCoin Q qHash qH).trans
      (entry_reduction_budget_expanded caps qCoin Q qHash qH).symm
  rw [← same]
  exact reduction_game_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
    coins budget.accept budget.hash budget.rom

/-- Query ledgers for exactly the reductions in the intermediate inequality. Every entry is a separate concrete reduction; the record makes no assumption that the remaining CTX games are secure. -/
structure ReductionBills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (caps : KemCaps) (qCoin Q qH qHash : Nat) : Prop where
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
    (entryReduction setup codec checks adversary false Q j) (entryReductionBudget caps qCoin Q qHash qH)
  entryGames : ∀ j : Fin (Q + 1),
    (realEntryGame setup codec checks adversary false Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 64) ∧
    (uniformEntryGame setup codec checks adversary false Q j).IsTotalQueryBound
      (entryReductionBudget caps qCoin Q qHash qH + 108)

/-- The original source and adversary interfaces discharge every ledger field for the same finite family and the same Gap-DH extractor. No arbitrary observer or body resource premise remains. -/
theorem intermediate_reduction_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin) :
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash := by
  exact ⟨reduction_resources setup codec checks caps bounded adversary qCoin Q qHash qH
      coins budget.accept budget.hash budget.rom,
    gap_game_uniform setup codec checks caps bounded adversary qCoin Q qH qHash budget coins,
    fun j => actual_entry_component_bills setup codec checks caps bounded adversary qCoin Q qHash qH
      coins budget.accept budget.hash budget.rom false j,
    fun j => actual_entry_games_uniform setup codec checks caps bounded adversary qCoin Q qHash qH
      coins budget.accept budget.hash budget.rom false j⟩

/-- Original-R1 authentication composition together with the exact constructed reductions' source and challenger bills. B8b's combined bound supplies each entry, without an assumed cryptographic event partition or a new protocol-security premise. -/
theorem authentication_intermediate_with_resources (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (𝒟[originalCollisionGame setup codec checks adversary] {true}).toReal +
      ∑ j : Fin (Q + 1), ((𝒟[uniformEntryGame setup codec checks adversary false Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary false Q j) ∧
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash := by
  constructor
  · apply (original_event_decomposition_real setup codec checks adversary Q qH qHash budget).trans
    apply add_le_add
    · exact add_le_add (disclosure_le_gapDh setup codec checks adversary qH law budget.rom) le_rfl
    · exact Finset.sum_le_sum (fun j _ => (entry_bound_with_resources setup codec checks caps bounded
        adversary qCoin Q qHash qH coins budget.accept budget.hash budget.rom false j correct).1)
  · exact intermediate_reduction_bills setup codec checks caps bounded adversary qCoin Q qH qHash budget coins

/-- The checked intermediate bound with explicit scalar-collision loss and complete ledgers for the same reductions. The uniform-entry CTX probabilities remain visible obligations for B9b. -/
theorem authentication_intermediate_scalar_with_resources (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (adversary : Adversary) (qCoin Q qH qHash : Nat) (budget : AuthBudget adversary Q qH qHash)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (law : X25519ClassLaw setup.source.crypto)
    (spread : X25519ScalarSpread setup.source.crypto)
    (correct : SourceFullCorrect setup.source setup.hmac) :
    (𝒟[serverAuthGame setup codec checks false adversary] {true}).toReal ≤
      (serverGapDhAdvantage setup.source.crypto setup.joint setup.secretOfSeed setup.wiring
        (PqxdhJointGapDh.extractor (scanClient setup codec checks adversary qH))).toReal +
      (Q.choose 2 : ℝ) * 64 / (2 ^ 256 : ℝ) +
      ∑ j : Fin (Q + 1), ((𝒟[uniformEntryGame setup codec checks adversary false Q j] {true}).toReal +
        entryScheduleLoss setup codec checks adversary false Q j) ∧
    ReductionBills setup codec checks adversary caps qCoin Q qH qHash := by
  obtain ⟨eventBound, resources⟩ := authentication_intermediate_with_resources setup codec checks caps bounded
    adversary qCoin Q qH qHash budget coins law correct
  exact ⟨eventBound.trans (add_le_add (add_le_add le_rfl
    (collision_le_scalar_spread setup codec checks adversary Q spread budget.accept)) le_rfl), resources⟩

end BeaconcryptCore.Computational.PqxdhServerAuthIntermediate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.original_event_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.original_event_decomposition
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.original_event_decomposition_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.original_event_decomposition_real
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.disclosure_le_gapDh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.disclosure_le_gapDh
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.collision_le_scalar_spread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.collision_le_scalar_spread
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_scalar
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.gap_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.gap_game_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.intermediate_reduction_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.intermediate_reduction_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_with_resources
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_scalar_with_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthIntermediate.authentication_intermediate_scalar_with_resources
