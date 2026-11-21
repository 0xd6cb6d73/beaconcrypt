-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRootCandidateBatch

/-! The fresh batch retains the candidate prefix's first-result marginal while executing every actual suffix draw. Its positive observation is precisely the ordinary Boolean tester used by the native related-Family advantage. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra
open RegistrationNativeRelatedFamily (Spec State)
open PqxdhJointIdentity (DhOutput)

/-- Running the actual later randomized tester does not change the probability of any event of the returned candidate list. -/
theorem first_marginal (implementation : QueryImpl Spec (StateT State ProbComp))
    (work : OracleComp Spec (List DhOutput)) (before : State) (event : List DhOutput → Prop) :
    Pr{let result ← (simulateQ implementation (RegistrationNativeKnownInputBatchWork.program work)).run' before}[event result.1] =
      Pr{let candidates ← (simulateQ implementation work).run' before}[event candidates] := by
  rw [StateT.run'_eq, RegistrationNativeKnownInputBatchWork.program_run, prEvent_map, StateT.run'_eq, prEvent_map]
  calc
    _ = Pr{let candidates ← (simulateQ implementation work).run before >>= fun leading => pure leading.1}[event candidates] := by
      apply prEvent_bind_congr
      intro leading
      rw [prEvent_map, prEvent_pure]
      by_cases matched : event leading.1
      · simp only [matched, ite_true, prEvent_true_eq_one]
      · simp only [matched, ite_false, prEvent_false]
    _ = _ := by rw [bind_pure_comp, prEvent_map]

/-- Projecting the actual pair program to its Boolean answer retains its literal success probability. -/
theorem positive (implementation : QueryImpl Spec (StateT State ProbComp))
    (work : OracleComp Spec (List DhOutput × Bool)) (before : State) :
    Pr{let result ← (simulateQ implementation (Prod.snd <$> work)).run' before}[result = true] =
      Pr{let result ← (simulateQ implementation work).run' before}[result.2 = true] := by
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_map]

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra.first_marginal' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra.first_marginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra.positive' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstFamilyAlgebra.positive
