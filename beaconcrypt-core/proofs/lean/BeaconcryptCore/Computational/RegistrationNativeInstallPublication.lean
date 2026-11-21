-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! Raw publication callbacks preserve the actual complete Word chronology while retaining their exact original replies. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallPublication
open RegistrationNativeG2Trace (State handler begin finish)
variable {n : Nat} {KemSK Value : Type}

def publication : QueryImpl RegistrationBoundPublication.Spec (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  fun query => (RegistrationNativePublicFrontend.Spec n KemSK).query (.inl (.inr (.inl (.inr (.inl query)))))

/-- The original raw signing/encoding/record-publication continuation leaves the same demanded descriptor and every chronological event intact. -/
theorem source (work : OracleComp RegistrationBoundPublication.Spec Value) (before : State) :
    (simulateQ handler (simulateQ (publication (n := n) (KemSK := KemSK)) work)).run before =
      (fun value => (value, before)) <$> simulateQ publication work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, publication]
      rw [StateT.run_bind]
      simp only [handler, StateT.run, begin, finish, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply before
end BeaconcryptCore.Computational.RegistrationNativeInstallPublication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallPublication.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallPublication.source
