import BeaconcryptCore.Computational.VCVioForwardOracleComp
import ToMathlib.MeasureTheory.Measure.Bool

/-!
The Boolean distinguishing bound is stated directly in terms of the two success masses. VCVio 4.35 supplies the bound as `MeasureTheory.Measure.apply_true_le_add_boolDist`; unfolding its extended nonnegative Boolean distance gives the project statement below.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.VCVioForward

/-- The success mass of one Boolean computation is bounded by the other's mass plus their absolute difference. -/
theorem evalDist_apply_true_le_add_absDiff (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.absDiff (𝒟[p] {true}) (𝒟[q] {true}) := by
  simpa only [Measure.boolDist] using Measure.apply_true_le_add_boolDist 𝒟[p] 𝒟[q]

end BeaconcryptCore.VCVioForward

/--
info: 'BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_absDiff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioForward.evalDist_apply_true_le_add_absDiff
