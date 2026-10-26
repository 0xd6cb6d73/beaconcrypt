import BeaconcryptCore.Computational.PqxdhInitialSourceLaterMixture
import BeaconcryptCore.Computational.VCVioForwardProbabilityTheory
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
A uniform statistical comparison bound lifts through the same actual preparation distribution using only supported continuations. This arithmetic lemma preserves every branch and does not replace a mixture of cryptographic advantages by the advantage of an unconstructed reduction.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSupportedMixture

/-- A fixed local distinguishing bound gives the same one-sided probability allowance after the complete supported sampler. -/
theorem probability {Context : Type} (sampler : ProbComp Context) (left right : Context → ProbComp Bool) (cost : ENNReal)
    (bound : ∀ context ∈ support sampler, ENNReal.ofReal ((left context).boolDistance (right context)) ≤ cost) :
    Pr{let x ← sampler >>= left}[x = true] ≤ Pr{let x ← sampler >>= right}[x = true] + cost := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' context, Pr{let x ← sampler}[x = context] * (Pr{let x ← right context}[x = true] + cost) := by
      apply ENNReal.tsum_le_tsum
      intro context
      by_cases supported : context ∈ support sampler
      · have comparison := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance (left context) (right context)
        rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true] at comparison
        exact mul_le_mul' le_rfl (comparison.trans (add_le_add le_rfl (bound context supported)))
      · simp only [prEvent_eq_zero_of_not_mem_support _ supported, zero_mul, le_refl]
    _ = (∑' context, Pr{let x ← sampler}[x = context] * Pr{let x ← right context}[x = true]) + (∑' context, Pr{let x ← sampler}[x = context]) * cost := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (by simpa only [one_mul] using mul_le_mul_left (OracleComp.tsum_prEvent_le_one sampler) cost)

/-- One uniform statistical allowance is preserved through arbitrary original preparation and initializer sampling, with no context or response selection factor. -/
theorem bound {Context : Type} (sampler : ProbComp Context) (left right : Context → ProbComp Bool) (cost : ENNReal)
    (localBound : ∀ context ∈ support sampler, ENNReal.ofReal ((left context).boolDistance (right context)) ≤ cost) :
    ENNReal.ofReal ((sampler >>= left).boolDistance (sampler >>= right)) ≤ cost := by
  rcases eq_or_ne cost ⊤ with infinite | infinite
  · simp only [infinite, le_top]
  · have forward := probability sampler left right cost localBound
    have backward := probability sampler right left cost (fun context supported => by
      simpa only [ProbComp.boolDistance, abs_sub_comm] using localBound context supported)
    have forwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), infinite⟩) forward
    have backwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), infinite⟩) backward
    simp only [ENNReal.toReal_add (prEvent_ne_top _) infinite] at forwardReal backwardReal
    rw [← ENNReal.ofReal_toReal infinite]
    apply ENNReal.ofReal_le_ofReal
    simp only [ProbComp.boolDistance]
    rw [← prEvent_eq_evalDist_singleton (sampler >>= left) true,
      ← prEvent_eq_evalDist_singleton (sampler >>= right) true]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end BeaconcryptCore.Computational.RawCtxSupportedMixture

/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedMixture.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedMixture.probability
/-- info: 'BeaconcryptCore.Computational.RawCtxSupportedMixture.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSupportedMixture.bound
