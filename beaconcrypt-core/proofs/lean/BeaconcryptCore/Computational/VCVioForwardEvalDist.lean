import VCVio.EvalDist.EvalDistEq
import VCVio.EvalDist.ProbabilityNotation
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.Monad.Measure
import VCVio.EvalDist.Defs.Support

/-!
Event probabilities and equality in distribution are supplied directly by VCVio 4.35. This import module keeps the project's existing dependency surface while retiring the former pin-specific backports.
-/

/--
info: 'EvalDistEq.prEvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.prEvent_eq

/--
info: 'EvalDistEq.of_forall_prEvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.of_forall_prEvent_eq

/--
info: 'EvalDistEq.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.refl

/--
info: 'EvalDistEq.rfl' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.rfl

/--
info: 'EvalDistEq.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.symm

/--
info: 'EvalDistEq.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.trans

/--
info: 'EvalDistEq.map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.map

/--
info: 'EvalDistEq.evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.evalDist_eq

/--
info: 'EvalDistEq.of_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.of_evalDist_eq

/--
info: 'evalDistEq_iff_evalDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDistEq_iff_evalDist_eq

/--
info: 'evalDistEq_iff_forall_prEvent_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDistEq_iff_forall_prEvent_eq_output

/--
info: 'EvalDistEq.bind' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind

/--
info: 'EvalDistEq.map_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.map_congr

/--
info: 'EvalDistEq.bind_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_congr

/--
info: 'EvalDistEq.bind_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_left

/--
info: 'EvalDistEq.bind_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms EvalDistEq.bind_right

/--
info: 'prEvent_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_false

/--
info: 'prEvent_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_pure

/--
info: 'prEvent_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_le_one

/--
info: 'prEvent_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_ne_top

/--
info: 'prEvent_lt_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_lt_top

/--
info: 'prEvent_true_eq_evalDist_apply_univ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_true_eq_evalDist_apply_univ

/--
info: 'prEvent_bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_const

/--
info: 'prEvent_bind_eq_sum_fintype' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_eq_sum_fintype

/--
info: 'prEvent_bind_eq_tsum_of_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_eq_tsum_of_countable

/--
info: 'prEvent_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_or_le

/--
info: 'prEvent_exists_finset_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_exists_finset_le

/--
info: 'prEvent_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_exists_le

/--
info: 'prEvent_eq_prEvent_and_add_prEvent_and_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_prEvent_and_add_prEvent_and_not

/--
info: 'prEvent_le_prEvent_add_prEvent_and_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_le_prEvent_add_prEvent_and_not

/--
info: 'prEvent_add_prEvent_not_eq_prEvent_true' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_add_prEvent_not_eq_prEvent_true

/--
info: 'prEvent_and_le_left' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_and_le_left

/--
info: 'prEvent_and_le_right' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_and_le_right

/--
info: 'prEvent_bind_le_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_of_forall_le

/--
info: 'prEvent_bind_mono_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_mono_of_forall_le

/--
info: 'prEvent_bind_le_add_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_add_of_forall_le

/--
info: 'le_prEvent_bind_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms le_prEvent_bind_of_forall_le

/--
info: 'prEvent_bind_le_prEvent_add_mul_prEvent_not' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_mul_prEvent_not

/--
info: 'prEvent_bind_le_prEvent_of_forall_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_of_forall_eq_zero

/--
info: 'prEvent_bind_le_prEvent_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add

/--
info: 'bind_eq_attach_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bind_eq_attach_bind

/--
info: 'prEvent_true_attach' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_true_attach

/--
info: 'prEvent_mono_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_mono_of_support

/--
info: 'prEvent_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_congr_of_support

/--
info: 'prEvent_eq_zero_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_zero_of_forall_mem_support

/--
info: 'prEvent_eq_zero_of_not_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_eq_zero_of_not_mem_support

/--
info: 'prEvent_bind_le_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_of_forall_le_of_support

/--
info: 'prEvent_bind_mono_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_mono_of_forall_le_of_support

/--
info: 'le_prEvent_bind_of_forall_le_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms le_prEvent_bind_of_forall_le_of_support

/--
info: 'prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support

/--
info: 'prEvent_bind_le_prEvent_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_of_support

/--
info: 'prEvent_bind_le_prEvent_add_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prEvent_bind_le_prEvent_add_of_support

/--
info: 'evalDist.ae_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms evalDist.ae_of_forall_mem_support
