import BeaconcryptCore.Computational.VCVioForwardOracleComp
import ToMathlib.MeasureTheory.Measure.Bool
import VCVio.CryptoFoundations.SecExp

/-!
# Forward shim: the Boolean distinguishing bound (VCVio pin 98dc1089)

The pinned VCVio deprecates `ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage` (the bound `Pr[= true | p] ≤ Pr[= true | q] + ENNReal.ofReal (p.boolDistAdvantage q)`) in favour of `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage`, the same bound on the measures `𝒟[p] {true}`. That replacement is itself removed upstream (afa6593f), together with the real-valued `ProbComp.boolDistAdvantage`; upstream states the bound as `MeasureTheory.Measure.apply_true_le_add_boolDist 𝒟[p] 𝒟[q]` with an `ℝ≥0∞`-valued `boolDist μ ν = ENNReal.absDiff (μ {true}) (ν {true})`.

This module follows the deprecation warning behind one project lemma, `evalDist_apply_true_le_add_ofReal_boolDistAdvantage`, so that the project's uses of the bound depend on the pin-only replacement in one place. It also states the bound in the `ENNReal.absDiff` form, which upstream is `Measure.apply_true_le_add_boolDist` by unfolding, and the pin-only equation linking the two forms. The names are project names because the upstream statement uses an `ℝ≥0∞` distance that the pin does not have. Nothing here is assumed.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.VCVioForward

/-- The real Boolean advantage, embedded in `ℝ≥0∞`, is the absolute difference of the two success masses. Pin-only: `ProbComp.boolDistAdvantage` is removed upstream. -/
theorem ofReal_boolDistAdvantage_eq_absDiff (p q : ProbComp Bool) :
    ENNReal.ofReal (p.boolDistAdvantage q) = ENNReal.absDiff (𝒟[p] {true}) (𝒟[q] {true}) := by
  rw [ProbComp.boolDistAdvantage,
    ← ENNReal.absDiff_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _,
      measure_ne_top _ _⟩) (ENNReal.absDiff_le_add _ _))]

/-- The Boolean distinguishing bound on success masses, the statement named by the deprecation of `ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage`; its proof is that replacement. -/
theorem evalDist_apply_true_le_add_ofReal_boolDistAdvantage (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.ofReal (p.boolDistAdvantage q) :=
  ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage p q

/-- The Boolean distinguishing bound with the `ℝ≥0∞` distance; upstream this is `MeasureTheory.Measure.apply_true_le_add_boolDist 𝒟[p] 𝒟[q]` by unfolding `boolDist`. -/
theorem evalDist_apply_true_le_add_absDiff (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.absDiff (𝒟[p] {true}) (𝒟[q] {true}) := by
  simpa only [ofReal_boolDistAdvantage_eq_absDiff] using
    evalDist_apply_true_le_add_ofReal_boolDistAdvantage p q

end BeaconcryptCore.VCVioForward

/--
info: 'BeaconcryptCore.VCVioForward.ofReal_boolDistAdvantage_eq_absDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioForward.ofReal_boolDistAdvantage_eq_absDiff

/--
info: 'BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage

/--
info: 'BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_absDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_absDiff
