import BeaconcryptCore.Computational.PqxdhComposition
import BeaconcryptCore.Computational.VCVioForwardProbabilityTheory
import BeaconcryptCore.Computational.VCVioLegacyBridge

/-!
A shared original sampler averages the same explicit local bad-event costs over its complete context. These arithmetic laws retain the sampler distribution and do not replace it by a worst-case source-independent state. They construct no cryptographic reduction; their consuming protocol proof must discharge each local comparison for its actual continuation.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxBadEventMixture

/-- An explicit Boolean bad-event probability bounds the one-sided probability change implied by a local advantage bound. -/
theorem local_probability (left right bad : ProbComp Bool)
    (bound : left.boolDistAdvantage right ≤ Pr{let x ← bad}[x = true].toReal) :
    Pr{let x ← left}[x = true] ≤ Pr{let x ← right}[x = true] + Pr{let x ← bad}[x = true] := by
  have comparison := VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage left right
  rw [← prEvent_eq_evalDist_singleton left true, ← prEvent_eq_evalDist_singleton right true] at comparison
  refine comparison.trans ?_
  exact add_le_add le_rfl (by simpa only [ENNReal.ofReal_toReal (prEvent_ne_top _)] using
    (ENNReal.ofReal_le_ofReal bound))

/-- The same complete context sampler averages local comparison costs into the original bad-event game. -/
theorem bind_probability {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤ Pr{let x ← bad context}[x = true].toReal) :
    Pr{let x ← sample >>= left}[x = true] ≤ Pr{let x ← sample >>= right}[x = true] + Pr{let x ← sample >>= bad}[x = true] := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  simpa only [mul_add, ENNReal.tsum_add] using
    (ENNReal.tsum_le_tsum fun context => mul_le_mul' le_rfl
      (local_probability (left context) (right context) (bad context) (bound context)))

/-- Averaging the same local absolute differences charges one full sampled bad-event probability, with coefficient one. -/
theorem bind_bound {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤ Pr{let x ← bad context}[x = true].toReal) :
    (sample >>= left).boolDistAdvantage (sample >>= right) ≤ Pr{let x ← sample >>= bad}[x = true].toReal := by
  have forward := bind_probability sample left right bad bound
  have backward := bind_probability sample right left bad (fun context => by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using bound context)
  have forwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) forward
  have backwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) backward
  simp only [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at forwardReal backwardReal
  simp only [ProbComp.boolDistAdvantage]
  rw [← prEvent_eq_evalDist_singleton (sample >>= left) true,
    ← prEvent_eq_evalDist_singleton (sample >>= right) true]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_bound_vcvioLegacy :
    ∀ {Context : Type} (sample : ProbComp Context) (left right bad : Context → ProbComp Bool) (bound : ∀ (context : Context), (left context).boolDistAdvantage (right context) ≤ Pr[= Bool.true | bad context].toReal), (sample >>= left).boolDistAdvantage (sample >>= right) ≤ Pr[= Bool.true | sample >>= bad].toReal :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_bound

end BeaconcryptCore.Computational.RawCtxBadEventMixture
/-- info: 'BeaconcryptCore.Computational.RawCtxBadEventMixture.local_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBadEventMixture.local_probability

/-- info: 'BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_probability

/-- info: 'BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBadEventMixture.bind_bound
