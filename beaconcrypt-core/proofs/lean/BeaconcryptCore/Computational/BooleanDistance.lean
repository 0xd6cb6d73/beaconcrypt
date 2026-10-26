import VCVio.OracleComp.ProbComp
import ToMathlib.MeasureTheory.Measure.Bool

/-!
The project expresses its existing real-valued Boolean bounds as the absolute difference of native output-measure success masses. This distance is the real value of VCVio's extended nonnegative `Measure.boolDist`; the equivalence below connects the two interfaces without changing the games or their success events.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace ProbComp

/-- The absolute difference between two Boolean computations' real success masses. -/
noncomputable def boolDistance (p q : ProbComp Bool) : ℝ :=
  |(𝒟[p] {true}).toReal - (𝒟[q] {true}).toReal|

/-- The project real distance is the real value of the native measure distance. -/
theorem boolDistance_eq_toReal_boolDist (p q : ProbComp Bool) :
    p.boolDistance q = (𝒟[p].boolDist 𝒟[q]).toReal :=
  (Measure.toReal_boolDist 𝒟[p] 𝒟[q]).symm

/-- A Boolean computation has zero distance from itself. -/
@[simp] theorem boolDistance_self (p : ProbComp Bool) : p.boolDistance p = 0 := by
  simp only [boolDistance, sub_self, abs_zero]

/-- Boolean distance is symmetric. -/
theorem boolDistance_comm (p q : ProbComp Bool) : p.boolDistance q = q.boolDistance p :=
  abs_sub_comm _ _

/-- Boolean distance satisfies the triangle inequality. -/
theorem boolDistance_triangle (p q r : ProbComp Bool) :
    p.boolDistance r ≤ p.boolDistance q + q.boolDistance r :=
  abs_sub_le _ _ _

/-- The native success-mass comparison expressed with the project real distance. -/
theorem evalDist_apply_true_le_add_ofReal_boolDistance (p q : ProbComp Bool) :
    𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.ofReal (p.boolDistance q) := by
  rw [boolDistance_eq_toReal_boolDist, ENNReal.ofReal_toReal (Measure.boolDist_ne_top _ _)]
  exact Measure.apply_true_le_add_boolDist 𝒟[p] 𝒟[q]

end ProbComp

/--
info: 'ProbComp.boolDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.boolDistance

/--
info: 'ProbComp.boolDistance_eq_toReal_boolDist' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.boolDistance_eq_toReal_boolDist

/--
info: 'ProbComp.boolDistance_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.boolDistance_self

/--
info: 'ProbComp.boolDistance_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.boolDistance_comm

/--
info: 'ProbComp.boolDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.boolDistance_triangle

/--
info: 'ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
