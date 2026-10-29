-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericTypedFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetTracedProgram

/-! The actual Word observer may be threaded inside the private interpreter while retaining its same trace and all original private state. Its erasure is pointwise for complete local programs, so actual internal preparation cuts can be projected without selecting a different execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate
open RegistrationNativeSecretWordFrontendTrace (State handler)
variable {n : Nat} {KemSK Private Value : Type}

noncomputable def combined (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp)) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT (State × Private) ProbComp) :=
  (implementation.mapStateTBase handler).flattenStateT

/-- The actual private chronological observer erases through every adaptive original callback program. -/
theorem program (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value) (trace : State) (privateState : Private) :
    Prod.map id Prod.snd <$> (simulateQ (combined implementation) work).run (trace, privateState) =
      (simulateQ implementation work).run privateState := by
  have erased := RegistrationNativeSecretWordFrontendTrace.program_erase work trace
  have closed := congrArg (fun program => (simulateQ implementation program).run privateState) erased
  rw [simulateQ_map, StateT.run_map] at closed
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT implementation handler work trace privateState] at closed
  simpa only [combined, Functor.map_map, Prod.map_def, id_eq] using closed

/-- The original local controller preserves the same environment and private state when only its chronological observer is erased. -/
theorem lower (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (work : StateT RegistrationServerReferenceCompiler.Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : State) (privateState : Private) :
    Prod.map id (Prod.map id Prod.snd) <$>
      (RegistrationNativeSecretWordGenericLower.lower (combined implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false) work).run (env, (trace, privateState)) =
      (RegistrationNativeSecretWordGenericLower.lower (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false) work).run (env, privateState) := by
  have erased := program implementation (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) (work.run env)) trace privateState
  have mapped := congrArg (fun program => (fun result => (result.1.1, (result.1.2, result.2))) <$> program) erased
  simpa only [RegistrationNativeSecretWordGenericLower.lower, StateT.run, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq] using mapped
/-- Every actual internal local controller cut retains a supported execution of its same chronological Word observer. -/
theorem lower_open_support (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (work : StateT RegistrationServerReferenceCompiler.Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : State) (privateState : Private)
    (result : Value × (RegistrationServerReferenceCompiler.Environment × (State × Private)))
    (supported : result ∈ support
      ((RegistrationNativeSecretWordGenericLower.lower (combined implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false) work).run (env, (trace, privateState)))) :
    ((result.1, result.2.1), result.2.2.1) ∈ support
      ((simulateQ handler (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) (work.run env))).run trace) := by
  rw [RegistrationNativeSecretWordGenericLower.lower_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  rw [QueryImpl.simulateQ_compose] at called
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT implementation handler
    (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) (work.run env)) trace privateState
  have closed : ((reached.1, reached.2.1), reached.2.2) ∈ support
      ((simulateQ implementation
        ((simulateQ handler (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) (work.run env))).run trace)).run privateState) := by
    rw [actual, support_map]
    exact ⟨reached, called, rfl⟩
  apply OracleComp.support_simulateQ_run'_subset implementation _ privateState
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst closed

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.lower_open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTracedPrivate.lower_open_support
