-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollision

/-! Unconditional 512-bit guessing with one explicitly exposed bit. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess
open CtxRomAuth
local instance (α : Type) : MeasurableSpace α := ⊤
local instance (α : Type) : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
variable {X : Type}
local instance : MeasurableSpace (CtxDigest × X) := ⊤
local instance : DiscreteMeasurableSpace (CtxDigest × X) := ⟨fun _ => trivial⟩

/-- An optional fixed candidate has at most one point mass under the actual uniform commitment law. -/
theorem fixed_guess (candidate : Option CtxDigest) :
    𝒟[$ᵗ CtxDigest] {digest | candidate = some digest} ≤
      ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  rw [← ctxDigest_card]
  cases candidate with
  | none => simp only [reduceCtorEq, Set.ofPred_false, measure_empty, zero_le]
  | some digest =>
    simp only [Option.some.injEq]
    have event : {value : CtxDigest | digest = value} = {digest} := Set.ext fun _ => eq_comm
    rw [event, SampleableType.evalDist_uniformSample, uniformOn_univ_apply_singleton]

/-- A full probabilistic continuation independent of the sampled commitment retains the unconditional point-mass bound. -/
theorem independent_guess (work : ProbComp X) (guess : X → Option CtxDigest) :
    𝒟[(do let digest ← $ᵗ CtxDigest
          let result ← work
          pure (digest, result))] {result | guess result.2 = some result.1} ≤ ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  generalize hsample : ($ᵗ CtxDigest) = sample
  have same := (OracleComp.EvalDistEq.bind_bind_swap
    sample work (fun digest result => pure (digest, result))).evalDist_eq
  rw [same]
  refine PqxdhRecordFactsCollision.bind_le work _ _ _ fun result => ?_
  rw [bind_pure_comp, evalDist_map_of_discrete, Measure.map_apply Measurable.of_discrete (.of_discrete)]
  change 𝒟[sample] {digest | guess result = some digest} ≤ _
  have bound := fixed_guess (guess result)
  rw [hsample] at bound
  exact bound

/-- Selecting one of two fixed probabilistic continuations by any digest-dependent bit costs at most the sum of their unconditioned guessing probabilities. -/
theorem bit_guess_split (leak : CtxDigest → Bool) (work : Bool → ProbComp X)
    (guess : X → Option CtxDigest) :
    𝒟[(do let digest ← $ᵗ CtxDigest
          let result ← work (leak digest)
          pure (digest, result))] {result | guess result.2 = some result.1} ≤
    𝒟[(do let digest ← $ᵗ CtxDigest
          let result ← work false
          pure (digest, result))] {result | guess result.2 = some result.1} +
    𝒟[(do let digest ← $ᵗ CtxDigest
          let result ← work true
          pure (digest, result))] {result | guess result.2 = some result.1} := by
  simp only [evalDist_bind_of_discrete]
  simp only [Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  rw [← lintegral_add_left Measurable.of_discrete]
  refine lintegral_mono fun digest => ?_
  cases leak digest
  · exact le_self_add
  · exact le_add_self

/-- One arbitrary bit of leakage permits two unconditional fixed-continuation guesses, with no conditioning on either bit outcome. -/
theorem one_bit_guess (leak : CtxDigest → Bool) (work : Bool → ProbComp X)
    (guess : X → Option CtxDigest) :
    𝒟[(do let digest ← $ᵗ CtxDigest
          let result ← work (leak digest)
          pure (digest, result))] {result | guess result.2 = some result.1} ≤ 2 * ((2 ^ 512 : Nat) : ℝ≥0∞)⁻¹ := by
  refine (bit_guess_split leak work guess).trans ?_
  simpa only [two_mul] using add_le_add (independent_guess (work false) guess) (independent_guess (work true) guess)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.fixed_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.fixed_guess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.independent_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.independent_guess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.bit_guess_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.bit_guess_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.one_bit_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginGuess.one_bit_guess
