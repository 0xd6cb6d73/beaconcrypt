import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule

/-!
# The key schedule from a uniform root (item 2, stage S4a, lemma G2)

This module is generic and contains no protocol code. It isolates the middle segment of `PqxdhServerAuthKeySchedule.keySchedule_bound`: the part of the key schedule that starts from a uniform 32-byte root instead of from a uniform 64-byte PRK. The item 2 plan uses it after the root Expand hybrid, where the root of the first hidden table entry is already a uniform 32-byte value and only the production initial and step ratchet HKDF calls remain.

The main theorem `fromRoot_bound` says that for any distinguisher of the 108-byte output `(step(first32 init), second32 init)` with `init = HKDF(root, INFO_R, 64)` and a uniform `root`, the advantage against 108 uniform bytes is at most the sum of four advantages of reductions built from the distinguisher: the Extract game on an independent uniform 32-byte input for the root (`initExtractReduction`), the HMAC-SHA-512 PRF game for the first ratchet Expand block (`initExpandReduction`, one challenge query), the Extract game on an independent uniform 32-byte input for the first chain (`stepExtractReduction`), and the HMAC-SHA-512 PRF game for the two-block step Expand (`stepExpandReduction`, two challenge queries). The only premise is the functional contract `SourceFullCorrect source hmac`, which rewrites the production HKDF as Extract followed by Expand.

Every hop is an equality with exactly one reduction's advantage (`initExtract_hop`, `initExpand_hop`, `stepExtract_hop`, `stepExpand_hop`), and the uniform 64-byte initializer splits into two independent uniform halves at no cost (`init_split`). The only inequalities are triangle inequalities. No existing module is changed, and no public HKDF or HMAC evaluation is replaced by a random table: only secret-keyed Expand outputs and Extract outputs on a hidden uniform 32-byte input are replaced, as in the existing key-schedule hops.

`fromRoot_bound_context` restates the bound when side information is sampled before the root, with the reductions built from the folded distinguisher `withContext sample distinguisher`.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot

open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhServerAuthKeySchedule

/-- G2: from a uniform 32-byte root, the 108-byte key-schedule output is indistinguishable from 108 uniform bytes up to two Extract advantages on an independent uniform 32-byte input and two HMAC-SHA-512 PRF advantages, all of reductions built from the distinguisher, under the functional contract `SourceFullCorrect`. -/
theorem fromRoot_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (rootHybrid source distinguisher).boolDistAdvantage
        (PqxdhServerAuthKeySchedule.uniformGame distinguisher) ≤
      (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
        (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
        (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction distinguisher)) := by
  rw [← initExtract_hop correct, ← initExpand_hop, ← stepExtract_hop correct, ← stepExpand_hop]
  have split : (initHybrid source distinguisher).boolDistAdvantage
      (PqxdhServerAuthKeySchedule.uniformGame distinguisher) =
      (splitHybrid source distinguisher).boolDistAdvantage
        (PqxdhServerAuthKeySchedule.uniformGame distinguisher) :=
    advantage_congr (init_split source distinguisher) rfl
  have first := ProbComp.boolDistAdvantage_triangle (rootHybrid source distinguisher)
    (initKeyHybrid source hmac distinguisher) (PqxdhServerAuthKeySchedule.uniformGame distinguisher)
  have second := ProbComp.boolDistAdvantage_triangle (initKeyHybrid source hmac distinguisher)
    (initHybrid source distinguisher) (PqxdhServerAuthKeySchedule.uniformGame distinguisher)
  have third := ProbComp.boolDistAdvantage_triangle (splitHybrid source distinguisher)
    (stepKeyHybrid hmac distinguisher) (PqxdhServerAuthKeySchedule.uniformGame distinguisher)
  linarith

/-- G2 with side information sampled before the root: the four reductions are built from the folded distinguisher `withContext sample distinguisher`. -/
theorem fromRoot_bound_context {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (sample : ProbComp Context)
    (distinguisher : Context → Distinguisher) :
    (do let context ← sample
        let root ← $ᵗ RootOutput
        distinguisher context (fromRoot source root)).boolDistAdvantage
      (do let context ← sample
          let output ← $ᵗ Output
          distinguisher context output) ≤
      (extractRealGame hmac uniform32
          (initExtractReduction source hmac (withContext sample distinguisher))).boolDistAdvantage
          (extractUniformGame uniform32
            (initExtractReduction source hmac (withContext sample distinguisher))) +
        (hmacPrfRealGame hmac (initExpandReduction source (withContext sample distinguisher))).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source (withContext sample distinguisher))) +
        (extractRealGame hmac uniform32
            (stepExtractReduction hmac (withContext sample distinguisher))).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac (withContext sample distinguisher))) +
        (hmacPrfRealGame hmac (stepExpandReduction (withContext sample distinguisher))).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction (withContext sample distinguisher))) := by
  have real := evalDist_eq_of_evalSPMF_eq _ _ (PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy sample
    ($ᵗ RootOutput) (fun context root => distinguisher context (fromRoot source root)))
  have ideal := evalDist_eq_of_evalSPMF_eq _ _ (PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy sample
    ($ᵗ Output) (fun context output => distinguisher context output))
  rw [advantage_congr real ideal]
  exact fromRoot_bound source hmac correct (withContext sample distinguisher)

end BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot.fromRoot_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot.fromRoot_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot.fromRoot_bound_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKeyScheduleFromRoot.fromRoot_bound_context
