-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound

/-! An actual root-free Family client first computes its candidate list and then runs the fresh batch checker in the same reached Family state. Candidate bytes remain an internal returned observation for the probability proof; every prefix effect and every suffix draw remains in the actual executable program. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacSha512)
open RegistrationNativeRelatedFamily (Spec State)

noncomputable def program (work : OracleComp Spec (List DhOutput)) : OracleComp Spec (List DhOutput × Bool) := do
  let candidates ← work
  (fun result => (candidates, result)) <$> RegistrationNativeKnownInputBatchProgram.test candidates

/-- The actual work and tester share the literal reached state; every cache entry and suffix draw is retained. -/
theorem program_run (implementation : QueryImpl Spec (StateT State ProbComp))
    (work : OracleComp Spec (List DhOutput)) (before : State) :
    (simulateQ implementation (program work)).run before =
      ((simulateQ implementation work).run before >>= fun leading =>
        (fun result => ((leading.1, result.1), result.2)) <$>
          (simulateQ implementation (RegistrationNativeKnownInputBatchProgram.test leading.1)).run leading.2) := by
  simp only [program, simulateQ_bind, simulateQ_map, StateT.run_bind, StateT.run_map]

/-- An arbitrary actual real prefix cannot make any supported later real batch positive. -/
theorem real_supported (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec (List DhOutput))
    (before : State) (result : (List DhOutput × Bool) × State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (program work)).run before)) : result.1.2 = false := by
  rw [program_run, mem_support_bind_iff] at supported
  obtain ⟨leading, _prefix, continued⟩ := supported
  rw [support_map] at continued
  obtain ⟨checked, reached, returned⟩ := continued
  cases returned
  exact RegistrationNativeKnownInputBatchProgram.real_supported hmac joint dh seed scalar leading.1 leading.2 checked reached

/-- The actual composed real client has zero positive probability, with its actual randomized suffix checks still executed. -/
theorem real_true_zero (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp Spec (List DhOutput)) (before : State) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (program work)).run' before}[result.2 = true] = 0 := by
  rw [StateT.run'_eq, prEvent_map, prEvent_eq_zero_iff]
  intro result supported positive
  rw [real_supported hmac joint dh seed scalar work before result supported] at positive
  cases positive

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.program_run' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.program_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.real_supported' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.real_supported
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.real_true_zero' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchWork.real_true_zero
