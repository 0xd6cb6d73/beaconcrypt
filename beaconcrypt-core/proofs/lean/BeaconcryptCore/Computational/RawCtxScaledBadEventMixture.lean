import BeaconcryptCore.Computational.RawCtxBadEventMixture

/-!
A fixed finite coefficient on the same explicit local candidate event remains that coefficient after the original full context sampler is averaged. The sampler's complete distribution is retained. This arithmetic result does not replace a reached source distribution with an independent state or construct a cryptographic reduction; its consumer must supply the actual local comparison and same bad-event game.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxScaledBadEventMixture

/-- A local comparison with a finite explicit coefficient gives the corresponding one-sided probability bound. -/
theorem local_probability (left right bad : ProbComp Bool) (coefficient : Nat)
    (bound : left.boolDistAdvantage right ≤ coefficient * Pr[= true | bad].toReal) :
    Pr[= true | left] ≤ Pr[= true | right] + coefficient * Pr[= true | bad] := by
  refine (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage left right).trans ?_
  exact add_le_add le_rfl (by simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ coefficient),
    ENNReal.ofReal_natCast, ENNReal.ofReal_toReal probOutput_ne_top] using ENNReal.ofReal_le_ofReal bound)

/-- Averaging over the same original complete sampler retains the displayed coefficient and original candidate event. -/
theorem bind_probability {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool) (coefficient : Nat)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤
      coefficient * Pr[= true | bad context].toReal) :
    Pr[= true | sample >>= left] ≤ Pr[= true | sample >>= right] + coefficient * Pr[= true | sample >>= bad] := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  simpa only [mul_add, ENNReal.tsum_add, mul_left_comm, ← ENNReal.tsum_mul_left] using
    (ENNReal.tsum_le_tsum fun context => mul_le_mul' (le_refl (Pr[= context | sample]))
      (local_probability (left context) (right context) (bad context) coefficient (bound context)))

/-- The complete mixed experiment retains the exact finite candidate coefficient without conditioning on reaching a cut or changing the source sampler. -/
theorem bind_bound {Context : Type} (sample : ProbComp Context)
    (left right bad : Context → ProbComp Bool) (coefficient : Nat)
    (bound : ∀ context, (left context).boolDistAdvantage (right context) ≤
      coefficient * Pr[= true | bad context].toReal) :
    (sample >>= left).boolDistAdvantage (sample >>= right) ≤
      coefficient * Pr[= true | sample >>= bad].toReal := by
  have forward := bind_probability sample left right bad coefficient bound
  have backward := bind_probability sample right left bad coefficient (fun context => by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using bound context)
  have finite : (coefficient : ENNReal) * Pr[= true | sample >>= bad] ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) probOutput_ne_top
  have forwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, finite⟩) forward
  have backwardReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, finite⟩) backward
  simp only [ENNReal.toReal_add probOutput_ne_top finite, ENNReal.toReal_mul, ENNReal.toReal_natCast] at forwardReal backwardReal
  simp only [ProbComp.boolDistAdvantage, evalDist_apply_singleton]
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
