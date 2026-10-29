-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchCounting

/-! The executable batch is an ordinary Family client: it freshly checks the returned candidate list in order and stops on its first positive test. It reads neither selected secret, private cache nor protection classifier. Actual state and suffix draws are retained throughout the program. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacSha512)
open RegistrationNativeRelatedFamily (Spec State)
open RegistrationNativeKnownInputBatchCounting (IsDerive)

noncomputable def test : List DhOutput → OracleComp Spec Bool
  | [] => pure false
  | first :: rest => do
      let found ← RegistrationNativeKnownInputCheck.check first
      if found then pure true else test rest

/-- The actual batch continues from the exact post-check state, including every new literal cache entry. -/
theorem cons_run (implementation : QueryImpl Spec (StateT State ProbComp))
    (first : DhOutput) (rest : List DhOutput) (before : State) :
    (simulateQ implementation (test (first :: rest))).run before =
      ((simulateQ implementation (RegistrationNativeKnownInputCheck.check first)).run before >>= fun result =>
        if result.1 then pure (true, result.2) else (simulateQ implementation (test rest)).run result.2) := by
  simp only [test, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, simulateQ_pure, StateT.run_pure]

/-- Observing the actual batch result leaves the same reached prefix state for the continuation. -/
theorem cons_run' (implementation : QueryImpl Spec (StateT State ProbComp))
    (first : DhOutput) (rest : List DhOutput) (before : State) :
    (simulateQ implementation (test (first :: rest))).run' before =
      ((simulateQ implementation (RegistrationNativeKnownInputCheck.check first)).run before >>= fun result =>
        if result.1 then pure true else (simulateQ implementation (test rest)).run' result.2) := by
  rw [StateT.run'_eq, cons_run, map_bind]
  apply bind_congr
  intro result
  cases result.1 <;> simp only [Bool.false_eq_true, ite_false, ite_true, map_pure, StateT.run'_eq]

/-- A batch adds at most one possible literal input per returned candidate. -/
theorem test_cap (candidates : List DhOutput) : (test candidates).IsQueryBoundP IsDerive candidates.length := by
  induction candidates with
  | nil => exact isQueryBoundP_pure IsDerive false 0
  | cons first rest ih =>
      unfold test
      have bounded := isQueryBoundP_bind
        (ob := fun found => if found then pure true else test rest) (m := rest.length)
        (RegistrationNativeKnownInputBatchCounting.check_cap first)
        (fun found _ => by
          cases found with
          | false => exact ih
          | true => exact isQueryBoundP_pure IsDerive true rest.length)
      simpa only [List.length_cons, Nat.add_comm] using bounded

/-- Every supported actual real single check has false output after any prior Family state. -/
theorem real_check_supported (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first : DhOutput) (before : State) (result : Bool × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.check first)).run before)) : result.1 = false := by
  have projected : result.1 ∈ support ((simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.check first)).run' before) := by
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  rw [RegistrationNativeKnownInputBatch.real_false, support_map] at projected
  obtain ⟨suffix, _sampled, returned⟩ := projected
  exact returned.symm

/-- Every supported actual real batch has false output, including duplicate and adaptively chosen candidates. -/
theorem real_supported (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput) (before : State) (result : Bool × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (test candidates)).run before)) : result.1 = false := by
  induction candidates generalizing before with
  | nil =>
      simp only [test, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | cons first rest ih =>
      rw [cons_run, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have noMatch := real_check_supported hmac joint dh seed scalar first before middle reached
      simp only [noMatch, Bool.false_eq_true, ite_false] at continued
      exact ih middle.2 continued

/-- The actual real batch never returns a positive known-input test. -/
theorem real_true_zero (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput) (before : State) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (test candidates)).run' before}[result = true] = 0 := by
  rw [StateT.run'_eq, prEvent_map]
  rw [prEvent_eq_zero_iff]
  intro result supported positive
  rw [real_supported hmac joint dh seed scalar candidates before result supported] at positive
  cases positive

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.cons_run' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.cons_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.cons_run'' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.cons_run'
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.test_cap' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.test_cap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_check_supported' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_check_supported
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_supported' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_supported
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_true_zero' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram.real_true_zero
