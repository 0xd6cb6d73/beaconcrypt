import BeaconcryptCore.Computational.RawCtxFreshChainCut
import BeaconcryptCore.Computational.PqxdhMaterialKeyCollisions

/-!
The existing 256-bit primitive collision lemma bounds a possibly repeating candidate list. In the same prior-full76 cut, the target is delayed past the entire target-free adaptive observer while retaining its complete result. The resulting unconditioned bound charges the actual supported list length and does not multiply by success, stopping or owner choices.

The concrete list of retained/publicly evaluated values and its length must still be supplied from the same source execution. A target-free observer can include actual public HKDF, known chains and adaptive decisions, but cannot be given the selected target or a prior expansion/ancestor that the source-to-hybrid comparison has not justified removing. This module does not assert source freshness, erase earlier authorized compromise, bound an arbitrary unrecorded trace, or establish a consistent ideal KDF table. Snapshot/persistence/restore services are excluded.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInputCandidates
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids RawCtxFreshChainCut

/-- Reuse the existing exact256-bit collision lemma for one independent chain coordinate and a possibly repeating candidate list. -/
theorem uniform_candidates (candidates : List RootOutput) :
    Pr{let target ← $ᵗ RootOutput}[target ∈ candidates] ≤
      (candidates.length : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  have firstUniform : EvalDistEq (Prod.fst <$> ($ᵗ Material : ProbComp Material)) ($ᵗ RootOutput : ProbComp RootOutput) := by
    rw [← pairSample]
    simpa only [map_bind, map_pure, bind_pure] using
      EvalDistEq.bind_right ($ᵗ RootOutput) fun target =>
        OracleComp.EvalDistEq.bind_const ($ᵗ NonceOutput) (pure target)
  rw [← firstUniform.prEvent_eq (fun target : RootOutput => target ∈ candidates), prEvent_map]
  simpa only [PqxdhMaterialKeyCollisions.material_key_card, Nat.cast_pow, Nat.cast_ofNat] using
    PqxdhMaterialKeyCollisions.material_key_mem candidates

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.uniform_candidates_vcvioLegacy :
    ∀ (candidates : List BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput), (probEvent ($ᵗ BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput) fun (target : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput) => target ∈ candidates) ≤ ↑candidates.length / 2 ^ 256 :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.uniform_candidates

/-- In the same full-reply cut, an arbitrary continued candidate trace is charged without conditioning on success or stopping. -/
theorem observed_candidates {Context Stopped Result : Type} (sample : ProbComp Context)
    (stop : Context → beaconcrypt_core.ratchet.RatchetMaterial → Stopped)
    (observe : Stopped → ProbComp Result) (candidates : Result → List RootOutput) (budget : Nat)
    (bounded : ∀ context result, result ∈ support (observe context) → (candidates result).length ≤ budget) :
    Pr{let result ← observedCut sample stop observe}[result.1 ∈ candidates result.2] ≤
      (budget : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [(observedCut_delayed sample stop observe).prEvent_eq (fun result : RootOutput × Result => result.1 ∈ candidates result.2),
    delayedCut]
  refine prEvent_bind_le_of_forall_le _ _ _ (fun context => ?_)
  refine prEvent_bind_le_of_forall_le _ _ _ (fun value => ?_)
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ (fun result supported => ?_)
  rw [bind_pure_comp _ ($ᵗ RootOutput), prEvent_map]
  refine (uniform_candidates (candidates result)).trans ?_
  exact ENNReal.div_le_div_right (by exact_mod_cast bounded _ result supported) _

end BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.uniform_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.uniform_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.observed_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInputCandidates.observed_candidates
