import BeaconcryptCore.Computational.VCVioForwardEvalDist
import BeaconcryptCore.Computational.BooleanDistance
import BeaconcryptCore.Computational.DiscreteDistance
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.EvalDist.Sum
import VCVio.OracleComp.Support
import VCVio.OracleComp.Constructions.SampleableType.Measure
import ToMathlib.MeasureTheory.Integral.Countable
import ToMathlib.Probability.UniformOn

/-!
Oracle event, output-sum and uniform-sampling laws are supplied directly by VCVio 4.35. The former backported declarations are no longer defined by the project.
-/

/--
info: 'MeasureTheory.lintegral_eq_tsum_of_ae_mem_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.lintegral_eq_tsum_of_ae_mem_countable

/--
info: 'MeasureTheory.lintegral_eq_tsum_mul_of_ae_mem_countable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.lintegral_eq_tsum_mul_of_ae_mem_countable

/--
info: 'OracleComp.prEvent_true_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_true_eq_one

/--
info: 'OracleComp.prEvent_not_eq_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_not_eq_one_sub

/--
info: 'OracleComp.prEvent_bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_const

/--
info: 'OracleComp.EvalDistEq.bind_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_const

/--
info: 'OracleComp.EvalDistEq.map_const' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.map_const

/--
info: 'OracleComp.ae_evalDist_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.ae_evalDist_of_forall_mem_support

/--
info: 'OracleComp.prEvent_eq_one_of_forall_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_one_of_forall_mem_support

/--
info: 'OracleComp.prEvent_bind_mono_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_mono_of_support

/--
info: 'OracleComp.prEvent_bind_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_congr_of_support

/--
info: 'OracleComp.EvalDistEq.bind_congr_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_congr_of_support

/--
info: 'OracleComp.evalDist_ae_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_ae_mem_support

/--
info: 'OracleComp.lintegral_evalDist_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.lintegral_evalDist_eq_tsum

/--
info: 'OracleComp.tsum_prEvent_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.tsum_prEvent_eq_one

/--
info: 'OracleComp.tsum_prEvent_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.tsum_prEvent_le_one

/--
info: 'OracleComp.prEvent_bind_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_bind_eq_tsum

/--
info: 'OracleComp.prEvent_eq_tsum_ite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_tsum_ite

/--
info: 'OracleComp.evalDist_bind_bind_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_bind_bind_swap

/--
info: 'OracleComp.evalDist_bind_bind_swap_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDist_bind_bind_swap_of_uniform

/--
info: 'OracleComp.EvalDistEq.bind_bind_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.EvalDistEq.bind_bind_swap

/--
info: 'OracleComp.evalDistEq_of_forall_prEvent_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.evalDistEq_of_forall_prEvent_eq_output

/--
info: 'OracleComp.prEvent_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_one_iff

/--
info: 'OracleComp.prEvent_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OracleComp.prEvent_eq_zero_iff

/--
info: 'SampleableType.evalDist_uniformSample_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.evalDist_uniformSample_singleton

/--
info: 'SampleableType.prEvent_uniformSample_eq_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.prEvent_uniformSample_eq_singleton

/--
info: 'SampleableType.map_uniformSample_evalDistEq_of_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SampleableType.map_uniformSample_evalDistEq_of_bijective
