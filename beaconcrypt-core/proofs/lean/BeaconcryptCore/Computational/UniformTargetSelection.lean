-- SPDX-License-Identifier: 0BSD
import VCVio.OracleComp.Constructions.SampleableType
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-! Generic target selection (CE-4). A run produces an outcome; a deterministic function `designate` of the outcome names at most one target in a finite domain `G`, and an outcome is eligible when it names one. Every statement here is an exact identity with no assumption and no loss. The split form writes the probability of an event on eligible outcomes as the exact sum over targets of the probability of the event together with that target's designation; it is the headline form, to be composed with per-target hops stated with absolute advantages. The event form writes the same probability as `card G` times the probability that a uniform guess drawn before an unchanged run equals the designated target. The advantage form is the split form for a left-or-right guess with the eligibility-weighted half subtracted, as a real-valued identity. The guessing combinator writes a sum of per-target probabilities, or of signed per-target differences, as `card G` times the probability, or the signed difference, of the run with a uniformly guessed target; with signed per-target hops it turns the exact sum into the `card G · Adv(B_guess)` wording. No security claim is made here. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.UniformTargetSelection
variable {Ω G : Type} [Fintype G] [DecidableEq G]

/-- The probability of an event as the evaluation measure of its indicator bit. -/
theorem chance_eq (run : ProbComp Ω) (event : Ω → Prop) [DecidablePred event] :
    𝒟[(fun outcome => decide (event outcome)) <$> run] {true} = Pr{let outcome ← run}[event outcome] := by
  rw [map_eq_bind_pure_comp]
  exact (prEvent_eq_evalDist_decide run event).symm

/-- Split form: the probability of an event on eligible outcomes is the exact sum over targets of the probability of the event with that target designated. -/
theorem split (run : ProbComp Ω) (event : Ω → Prop) [DecidablePred event] (designate : Ω → Option G) :
    𝒟[(fun outcome => decide (event outcome ∧ (designate outcome).isSome)) <$> run] {true} =
      ∑ target, 𝒟[(fun outcome => decide (event outcome ∧ designate outcome = some target)) <$> run] {true} := by
  simp only [chance_eq, OracleComp.prEvent_eq_tsum_ite]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun outcome => ?_
  generalize Pr{let y ← run}[y = outcome] = mass
  cases named : designate outcome with
  | none => simp
  | some chosen =>
      by_cases holds : event outcome
      · simp [holds, Finset.sum_ite_eq]
      · simp [holds]

/-- Split form for an event that implies eligibility. -/
theorem split_of_eligible (run : ProbComp Ω) (event : Ω → Prop) [DecidablePred event] (designate : Ω → Option G)
    (eligible : ∀ outcome, event outcome → designate outcome ≠ none) :
    𝒟[(fun outcome => decide (event outcome)) <$> run] {true} =
      ∑ target, 𝒟[(fun outcome => decide (event outcome ∧ designate outcome = some target)) <$> run] {true} := by
  rw [← split run event designate, chance_eq, chance_eq]
  refine prEvent_congr run _ _ fun outcome => ?_
  constructor
  · intro holds
    exact ⟨holds, Option.isSome_iff_ne_none.mpr (eligible outcome holds)⟩
  · exact fun both => both.1

omit [DecidableEq G] in
/-- Guessing combinator: a sum over targets of per-target probabilities is `card G` times the probability of the run of a uniformly guessed target. -/
theorem sum_eq_card_mul [SampleableType G] (runs : G → ProbComp Ω) (event : G → Ω → Prop)
    [∀ target, DecidablePred (event target)] :
    ∑ target, 𝒟[(fun outcome => decide (event target outcome)) <$> runs target] {true} =
      (Fintype.card G : ℝ≥0∞) * 𝒟[(fun pair : G × Ω => decide (event pair.1 pair.2)) <$> do
        let target ← $ᵗ G
        let outcome ← runs target
        pure (target, outcome)] {true} := by
  simp only [chance_eq]
  rw [OracleComp.prEvent_bind_eq_tsum, tsum_fintype]
  have each : ∀ target : G, Pr{let pair ← (do
      let outcome ← runs target
      pure (target, outcome))}[event pair.1 pair.2] = Pr{let outcome ← runs target}[event target outcome] := by
    intro target
    have shape : (do let outcome ← runs target; pure (target, outcome)) =
        (fun outcome => (target, outcome)) <$> runs target := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [shape, prEvent_map]
  simp only [each, SampleableType.prEvent_uniformSample_eq_singleton]
  rw [← Finset.mul_sum, ← mul_assoc]
  have positive : (Fintype.card G : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this.ne'
  rw [ENNReal.mul_inv_cancel positive (ENNReal.natCast_ne_top _), one_mul]

/-- Event form: for an event that implies eligibility, its probability is `card G` times the probability that a uniform guess drawn before the unchanged run is the designated target. -/
theorem guess [SampleableType G] (run : ProbComp Ω) (event : Ω → Prop) [DecidablePred event]
    (designate : Ω → Option G) (eligible : ∀ outcome, event outcome → designate outcome ≠ none) :
    𝒟[(fun outcome => decide (event outcome)) <$> run] {true} =
      (Fintype.card G : ℝ≥0∞) * 𝒟[(fun pair : G × Ω => decide (event pair.2 ∧ designate pair.2 = some pair.1)) <$> do
        let target ← $ᵗ G
        let outcome ← run
        pure (target, outcome)] {true} := by
  rw [split_of_eligible run event designate eligible]
  exact sum_eq_card_mul (fun _ => run) fun target outcome => event outcome ∧ designate outcome = some target

/-- Evaluation probabilities are finite. -/
theorem chance_ne_top (run : ProbComp Ω) (event : Ω → Bool) : 𝒟[event <$> run] {true} ≠ ⊤ := by
  rw [← prEvent_eq_evalDist_singleton]
  exact prEvent_ne_top _

/-- Advantage form: the eligibility-weighted guessing advantage of a left-or-right bit is the exact sum over targets of the per-target weighted advantages. -/
theorem advantage (run : ProbComp Ω) (correct : Ω → Prop) [DecidablePred correct] (designate : Ω → Option G) :
    (𝒟[(fun outcome => decide (correct outcome ∧ (designate outcome).isSome)) <$> run] {true}).toReal -
        (1 / 2 : ℝ) * (𝒟[(fun outcome => (designate outcome).isSome) <$> run] {true}).toReal =
      ∑ target, ((𝒟[(fun outcome => decide (correct outcome ∧ designate outcome = some target)) <$> run] {true}).toReal -
        (1 / 2 : ℝ) * (𝒟[(fun outcome => decide (designate outcome = some target)) <$> run] {true}).toReal) := by
  have eligible := split run (fun _ => True) designate
  simp only [true_and] at eligible
  have bits : (fun outcome => (designate outcome).isSome) = fun outcome => decide ((designate outcome).isSome = true) := by
    funext outcome
    simp
  rw [split run correct designate, bits, eligible, ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), Finset.mul_sum, ← Finset.sum_sub_distrib]

omit [DecidableEq G] in
/-- Signed guessing combinator: a sum over targets of signed per-target differences is `card G` times the signed difference of the two runs with a uniformly guessed target. -/
theorem signed [SampleableType G] (left right : G → ProbComp Ω) (event : G → Ω → Prop)
    [∀ target, DecidablePred (event target)] :
    ∑ target, ((𝒟[(fun outcome => decide (event target outcome)) <$> left target] {true}).toReal -
        (𝒟[(fun outcome => decide (event target outcome)) <$> right target] {true}).toReal) =
      (Fintype.card G : ℝ) * ((𝒟[(fun pair : G × Ω => decide (event pair.1 pair.2)) <$> do
          let target ← $ᵗ G
          let outcome ← left target
          pure (target, outcome)] {true}).toReal -
        (𝒟[(fun pair : G × Ω => decide (event pair.1 pair.2)) <$> do
          let target ← $ᵗ G
          let outcome ← right target
          pure (target, outcome)] {true}).toReal) := by
  rw [Finset.sum_sub_distrib, ← ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _),
    ← ENNReal.toReal_sum (fun _ _ => chance_ne_top _ _), sum_eq_card_mul left event, sum_eq_card_mul right event,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]

end BeaconcryptCore.Computational.UniformTargetSelection

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.chance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.chance_eq

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.split

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.split_of_eligible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.split_of_eligible

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.sum_eq_card_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.sum_eq_card_mul

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.guess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.guess

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.chance_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.chance_ne_top

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.advantage

/-- info: 'BeaconcryptCore.Computational.UniformTargetSelection.signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.UniformTargetSelection.signed
