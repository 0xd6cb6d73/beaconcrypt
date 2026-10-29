-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyLog

/-! A concrete ordinary suffix-key PRF adversary runs the whole adaptive symbolic experiment, collects its literal key guesses, and appends the public terminal checker. Recovering the true key therefore implies acceptance in the real PRF game. The ideal game's error is derived from its actual chronological cache coverage and query cap. This route remains valid when real off-protected computations leak information about the candidate; no independence of the real guessed list is assumed. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery
open RegistrationNativeSuffixKeyPrf (Prefix Secret Spec realImpl idealImpl real ideal advantage)
open RegistrationNativeSuffixKeyCheck (test)
open RegistrationNativeSuffixKeyLog (IsQuery)
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value

noncomputable def adversary (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (work : OracleComp Spec (List Secret)) : OracleComp Spec Bool := work >>= test source

noncomputable def guessed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (work : OracleComp Spec (List Secret)) : ProbComp Bool := do
  let key ← $ᵗ Secret
  let guesses ← simulateQ (realImpl source key) work
  pure (decide (key ∈ guesses))

/-- The real ordinary tester accepts with probability one after its list contains the actual key. -/
theorem real_test_true (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (key : Secret) (guesses : List Secret) (member : key ∈ guesses) :
    Pr{let result ← simulateQ (realImpl source key) (test source guesses)}[result = true] = 1 := by
  rw [RegistrationNativeSuffixKeyCheckSource.real_test source key guesses member]
  rw [prEvent_map]
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr (fun _ => by trivial)

/-- Guessing the hidden key in an adaptive real execution implies acceptance of one explicitly constructed ordinary PRF adversary. -/
theorem real_catches (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (work : OracleComp Spec (List Secret)) :
    Pr{let result ← guessed source work}[result = true] ≤ Pr{let result ← real source (adversary source work)}[result = true] := by
  simp only [guessed, real, adversary, simulateQ_bind, map_bind]
  apply prEvent_bind_mono_of_support
  intro key _possible
  apply prEvent_bind_mono_of_support
  intro guesses _reached
  by_cases member : key ∈ guesses
  · rw [real_test_true source key guesses member]
    exact prEvent_le_one _
  · simp only [member, decide_false, prEvent_pure, Bool.false_eq_true, ite_false]
    exact zero_le

/-- The ideal whole tester has only its actual earlier-head and candidate-list allowances, with both bills derived at the reached prefix. -/
theorem ideal_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (work : OracleComp Spec (List Secret))
    (queryCap guessCap : Nat) (bounded : work.IsQueryBoundP IsQuery queryCap)
    (capped : ∀ guesses ∈ support work, guesses.length ≤ guessCap) :
    Pr{let result ← ideal (adversary source work)}[result = true] ≤
      queryCap * (256 ^ 160 : ℝ≥0∞)⁻¹ + guessCap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  simp only [ideal, adversary, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  have logged := RegistrationNativeSuffixKeyLog.program_source work RegistrationNativeSuffixKeyLog.initial
  simp only [RegistrationNativeSuffixKeyLog.initial] at logged
  rw [← logged, bind_map_left]
  have estimated : Pr{let result ← ((simulateQ RegistrationNativeSuffixKeyLog.handler work).run RegistrationNativeSuffixKeyLog.initial >>= fun leading =>
      (simulateQ idealImpl (test source leading.1)).run' leading.2.cache)}[result = true] ≤
      queryCap * (256 ^ 160 : ℝ≥0∞)⁻¹ + guessCap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
    apply prEvent_bind_le_of_forall_le_of_support
    intro leading reached
    have covered := RegistrationNativeSuffixKeyLog.program_covers work RegistrationNativeSuffixKeyLog.initial leading
      RegistrationNativeSuffixKeyLog.initial_covers reached
    have count := RegistrationNativeSuffixKeyLog.program_count work queryCap bounded RegistrationNativeSuffixKeyLog.initial leading reached
    simp only [RegistrationNativeSuffixKeyLog.initial, List.length_nil, Nat.zero_add] at count
    have plain : leading.1 ∈ support work := by
      apply support_simulateQ_run'_subset RegistrationNativeSuffixKeyLog.handler work RegistrationNativeSuffixKeyLog.initial
      rw [StateT.run'_eq, support_map]
      exact ⟨leading, reached, rfl⟩
    have guesses := capped leading.1 plain
    have localBound := RegistrationNativeSuffixKeyCheckBound.ideal_test_bound source leading.1 leading.2.cache leading.2.history covered
    refine localBound.trans ?_
    gcongr
  simpa only [StateT.run'_eq, map_bind, Prod.map_def, id_eq, RegistrationNativeSuffixKeyLog.initial] using estimated

/-- Ordinary suffix-key PRF security bounds the actual adaptive hidden-key recovery event, even when its real side information depends on that key. -/
theorem key_recovery_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (work : OracleComp Spec (List Secret))
    (queryCap guessCap : Nat) (bounded : work.IsQueryBoundP IsQuery queryCap)
    (capped : ∀ guesses ∈ support work, guesses.length ≤ guessCap) :
    Pr{let result ← guessed source work}[result = true] ≤
      ENNReal.ofReal (advantage source (adversary source work)) +
        queryCap * (256 ^ 160 : ℝ≥0∞)⁻¹ + guessCap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have comparison := ProbComp.evalDist_apply_true_le_add_ofReal_boolDistance
    (real source (adversary source work)) (ideal (adversary source work))
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true] at comparison
  refine (real_catches source work).trans (comparison.trans ?_)
  have bound := ideal_bound source work queryCap guessCap bounded capped
  simpa only [RegistrationNativeSuffixKeyPrf.advantage, add_assoc, add_comm, add_left_comm] using
    add_le_add_right bound (ENNReal.ofReal (advantage source (adversary source work)))

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.real_test_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.real_test_true
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.real_catches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.real_catches
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.ideal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.ideal_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.key_recovery_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyRecovery.key_recovery_bound
