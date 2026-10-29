-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork

/-! The miss event of the actual adaptive prefix and fresh batch has a finite bound from the original derive budget and reached candidate-list cap. Cache coverage, earlier-address count and the post-prefix tester state are all derived from the same actual execution from the empty Family state. No extractor or native-game correspondence is assumed here. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacSha512)
open RegistrationNativeRelatedFamily (Spec State)
open RegistrationNativeKnownInputBatchBound (Matches)
open RegistrationNativeKnownInputBatchCache (addresses)
open RegistrationNativeKnownInputBatchCounting (IsDerive)
open RegistrationNativeKnownInputBatchWork (program program_run)

/-- A matching candidate returned by the actual ideal prefix is missed only with the explicit derive-plus-list suffix allowance and one512-bit point term. -/
theorem ideal_false (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec (List DhOutput))
    (deriveBudget candidateCap : Nat) (bounded : work.IsQueryBoundP IsDerive deriveBudget)
    (capped : ∀ leading, leading ∈ support
      ((simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) work).run RegistrationNativeRelatedFamily.empty) →
      leading.1.length ≤ candidateCap) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
      (program work)).run' RegistrationNativeRelatedFamily.empty}[
        Matches joint dh seed scalar result.1 ∧ result.2 = false] ≤
      ((deriveBudget + candidateCap : Nat) : ℝ≥0∞) * (256 ^ 32 : ℝ≥0∞)⁻¹ + (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  rw [StateT.run'_eq, program_run, prEvent_map]
  apply prEvent_bind_le_of_forall_le_of_support
  intro leading reached
  rw [prEvent_map]
  by_cases matching : Matches joint dh seed scalar leading.1
  · simp only [matching, true_and]
    have covered := RegistrationNativeKnownInputBatchCache.program_covers hmac joint dh seed scalar work
      RegistrationNativeRelatedFamily.empty leading (RegistrationNativeKnownInputBatchCache.empty joint dh seed scalar) reached
    have checked := RegistrationNativeKnownInputBatchBound.ideal_false hmac joint dh seed scalar leading.1 matching leading.2 covered
    rw [StateT.run'_eq, prEvent_map] at checked
    refine checked.trans ?_
    have count := RegistrationNativeKnownInputBatchCounting.program_count hmac joint dh seed scalar work deriveBudget bounded
      RegistrationNativeRelatedFamily.empty leading reached
    simp only [RegistrationNativeRelatedFamily.empty, addresses, List.filterMap_nil, List.length_nil, Nat.zero_add] at count
    have total := Nat.add_le_add count (capped leading reached)
    have cast : (((addresses joint dh seed scalar leading.2.history).length + leading.1.length : Nat) : ℝ≥0∞) ≤
        ((deriveBudget + candidateCap : Nat) : ℝ≥0∞) := by
      exact_mod_cast total
    gcongr
  · simp only [matching, false_and, prEvent_false]
    exact zero_le

/-- A cap on the actual open prefix's supported candidate outputs suffices without any additional interpretation premise. -/
theorem ideal_false_of_source_cap (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec (List DhOutput))
    (deriveBudget candidateCap : Nat) (bounded : work.IsQueryBoundP IsDerive deriveBudget)
    (capped : ∀ candidates ∈ support work, candidates.length ≤ candidateCap) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
      (program work)).run' RegistrationNativeRelatedFamily.empty}[
        Matches joint dh seed scalar result.1 ∧ result.2 = false] ≤
      ((deriveBudget + candidateCap : Nat) : ℝ≥0∞) * (256 ^ 32 : ℝ≥0∞)⁻¹ + (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  apply ideal_false hmac joint dh seed scalar work deriveBudget candidateCap bounded
  intro leading reached
  apply capped leading.1
  apply support_simulateQ_run'_subset (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) work RegistrationNativeRelatedFamily.empty
  rw [StateT.run'_eq, support_map]
  exact ⟨leading, reached, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound.ideal_false' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound.ideal_false
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound.ideal_false_of_source_cap' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWorkBound.ideal_false_of_source_cap
