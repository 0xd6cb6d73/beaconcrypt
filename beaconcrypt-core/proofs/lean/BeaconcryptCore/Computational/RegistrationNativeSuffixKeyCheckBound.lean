-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckSource

/-! The actual terminal key tester pays for an independently sampled160-byte head colliding with any earlier oracle address, then uses the fresh ideal answer's32-byte coordinate. The prior table may be adaptive; only its actual finite address coverage is used. Whole-client coverage and query bills are separate structural consequences of the concrete ordinary PRF adversary. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound
open RegistrationNativeSuffixKeyPrf (Prefix Secret Oracle idealImpl)
open RegistrationNativeSuffixKeyCheck (Output Matches testAt test)
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

/-- The whole finite list of earlier heads has at most its cardinality's share of the full fresh160-byte domain. -/
theorem head_list (earlier : List Prefix) :
    Pr{let sampled ← $ᵗ Prefix}[sampled ∈ earlier] ≤ earlier.length * (256 ^ 160 : ℝ≥0∞)⁻¹ := by
  induction earlier with
  | nil =>
      rw [prEvent_eq_zero_of_forall_not _ _ (fun _ member => List.not_mem_nil member)]
      exact zero_le
  | cons head rest ih =>
      rw [prEvent_congr ($ᵗ Prefix) _ (fun sampled => sampled = head ∨ sampled ∈ rest)
        (fun sampled => List.mem_cons)]
      refine (prEvent_or_le ($ᵗ Prefix) (fun sampled => sampled = head) (fun sampled => sampled ∈ rest)).trans ?_
      rw [RegistrationNativeSuffixKeyCheck.head_point]
      calc (256 ^ 160 : ℝ≥0∞)⁻¹ + Pr{let sampled ← $ᵗ Prefix}[sampled ∈ rest]
          ≤ (256 ^ 160 : ℝ≥0∞)⁻¹ + rest.length * (256 ^ 160 : ℝ≥0∞)⁻¹ := add_le_add le_rfl ih
        _ = (rest.length + 1 : Nat) * (256 ^ 160 : ℝ≥0∞)⁻¹ := by simp [Nat.cast_add, add_mul, add_comm]

/-- A reached cache miss uses a fresh complete ideal answer, after which the checker has only the explicit finite-list match probability. -/
theorem ideal_fresh (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (head : Prefix) (cache : Oracle.QueryCache) (fresh : cache head = none) :
    Pr{let result ← (simulateQ idealImpl (testAt source guesses head)).run' cache}[result = true] ≤
      guesses.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  rw [StateT.run'_eq, RegistrationNativeSuffixKeyCheckSource.ideal_at source guesses head cache fresh]
  simpa only [Functor.map_map, prEvent_map, decide_eq_true_eq] using
    RegistrationNativeSuffixKeyCheck.uniform_match source guesses head

/-- A full actual ideal checker after an adaptive prior cache has a derived bound, without guessing that prior answers were fresh. -/
theorem ideal_test_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (cache : Oracle.QueryCache) (earlier : List Prefix)
    (covered : ∀ head, cache head ≠ none → head ∈ earlier) :
    Pr{let result ← (simulateQ idealImpl (test source guesses)).run' cache}[result = true] ≤
      earlier.length * (256 ^ 160 : ℝ≥0∞)⁻¹ + guesses.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  rw [RegistrationNativeSuffixKeyCheckSource.ideal_test]
  refine (prEvent_bind_le_prEvent_add_of_support ($ᵗ Prefix)
    (fun head => (simulateQ idealImpl (testAt source guesses head)).run' cache)
    (fun head => head ∈ earlier) (fun result => result = true)
    (ε := guesses.length * (256 ^ 32 : ℝ≥0∞)⁻¹) ?_).trans ?_
  · intro head _possible separate
    have fresh : cache head = none := by
      by_contra missing
      exact separate (covered head missing)
    exact ideal_fresh source guesses head cache fresh
  · exact add_le_add (head_list earlier) le_rfl

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.head_list' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.head_list
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.ideal_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.ideal_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.ideal_test_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheckBound.ideal_test_bound
