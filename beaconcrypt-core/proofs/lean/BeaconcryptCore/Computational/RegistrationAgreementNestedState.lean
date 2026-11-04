-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
/-! Reassociation retains both the complete private source capture and the external shared state. It commutes with every adaptive request program; neither state is erased. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementNestedState
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Private Shared : Type}

def flatten {Value : Type} (work : StateT Private (StateT Shared m) Value) : StateT (Private × Shared) m Value :=
  fun before => (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2

omit [LawfulMonad m] in
private theorem flatten_run {Value : Type} (work : StateT Private (StateT Shared m) Value)
    (before : Private × Shared) : (flatten work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2 := rfl

variable {ι : Type} {spec : OracleSpec ι}
def implementation (base : QueryImpl spec (StateT Private (StateT Shared m))) :
    QueryImpl spec (StateT (Private × Shared) m) := fun request => flatten (base request)

theorem program {Value : Type} (base : QueryImpl spec (StateT Private (StateT Shared m)))
    (work : OracleComp spec Value) (before : Private × Shared) :
    (simulateQ (implementation base) work).run before =
      (flatten (simulateQ base work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [flatten_run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind request next ih =>
    simp only [flatten_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation, flatten_run]
    simp only [StateT.run, map_bind, bind_map_left]
    apply bind_congr
    rintro ⟨⟨reply, privateAfter⟩, sharedAfter⟩
    exact ih reply (privateAfter, sharedAfter)
end BeaconcryptCore.Computational.RegistrationAgreementNestedState
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementNestedState.program' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementNestedState.program
