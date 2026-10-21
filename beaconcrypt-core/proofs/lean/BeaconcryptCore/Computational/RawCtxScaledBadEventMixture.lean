import BeaconcryptCore.Computational.RawCtxBadEventMixture
import BeaconcryptCore.Computational.VCVioForwardProbabilityTheory
import BeaconcryptCore.Computational.VCVioLegacyBridge

/-!
A fixed finite coefficient on the same explicit local candidate event remains that coefficient after the original full context sampler is averaged. The sampler's complete distribution is retained. This arithmetic result does not replace a reached source distribution with an independent state or construct a cryptographic reduction; its consumer must supply the actual local comparison and same bad-event game.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxScaledBadEventMixture

/-- A local comparison with a finite explicit coefficient gives the corresponding one-sided probability bound. -/
theorem local_probability (left right bad : ProbComp Bool) (coefficient : Nat)
    (bound : left.boolDistAdvantage right ≤ coefficient * Pr{let x ← bad}[x = true].toReal) :
    Pr{let x ← left}[x = true] ≤ Pr{let x ← right}[x = true] + coefficient * Pr{let x ← bad}[x = true] := by
  have comparison := VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage left right
  rw [← prEvent_eq_evalDist_singleton left true, ← prEvent_eq_evalDist_singleton right true] at comparison
  refine comparison.trans ?_
  exact add_le_add le_rfl (by simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ coefficient),
    ENNReal.ofReal_natCast, ENNReal.ofReal_toReal (prEvent_ne_top _)] using ENNReal.ofReal_le_ofReal bound)

/-- Averaging over the same original complete sampler retains the displayed coefficient and original candidate event. -/
theorem bind_probability {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool) (coefficient : Nat)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤
      coefficient * Pr{let x ← bad context}[x = true].toReal) :
    Pr{let x ← sample >>= left}[x = true] ≤ Pr{let x ← sample >>= right}[x = true] + coefficient * Pr{let x ← sample >>= bad}[x = true] := by
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  simpa only [mul_add, ENNReal.tsum_add, mul_left_comm, ← ENNReal.tsum_mul_left] using
    (ENNReal.tsum_le_tsum fun context => mul_le_mul' (le_refl (Pr{let x ← sample}[x = context]))
      (local_probability (left context) (right context) (bad context) coefficient (bound context)))

/-- The complete mixed experiment retains the exact finite candidate coefficient without conditioning on reaching a cut or changing the source sampler. -/
theorem bind_bound {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool) (coefficient : Nat)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤
      coefficient * Pr{let x ← bad context}[x = true].toReal) :
    (sample >>= left).boolDistAdvantage (sample >>= right) ≤
      coefficient * Pr{let x ← sample >>= bad}[x = true].toReal := by
  have forward := bind_probability sample left right bad coefficient bound
  have backward := bind_probability sample right left bad coefficient (fun context => by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using bound context)
  have finite : (coefficient : ENNReal) * Pr{let x ← sample >>= bad}[x = true] ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (prEvent_ne_top _)
  have forwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), finite⟩) forward
  have backwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), finite⟩) backward
  simp only [ENNReal.toReal_add (prEvent_ne_top _) finite, ENNReal.toReal_mul, ENNReal.toReal_natCast] at forwardReal backwardReal
  simp only [ProbComp.boolDistAdvantage]
  rw [← prEvent_eq_evalDist_singleton (sample >>= left) true,
    ← prEvent_eq_evalDist_singleton (sample >>= right) true]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end BeaconcryptCore.Computational.RawCtxScaledBadEventMixture

/-- info: 'BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.local_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.local_probability
/-- info: 'BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.bind_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.bind_probability
/-- info: 'BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxScaledBadEventMixture.bind_bound
