-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracket

/-! Stateful closure of the exact local G2 observer/World reassociation. Arbitrary original callbacks and the complete actual trace remain in the same compiled program. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec)
open RegistrationNativeG3MaterializedTracedServerRebracket (Spec Old New join result fallback)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState Value : Type}

def merge (before : RegistrationNativeG2Trace.State × Old n KeyState) : New n KeyState := join before.1 before.2

noncomputable def combined (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp)) :=
  ((RegistrationNativeG3MaterializedFrontendInterface.interface full seeds service implementation).mapStateTBase
    RegistrationNativeG3MaterializedTracedServerTrace.handler).flattenStateT

theorem query_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (query : (Spec n KemSK).Domain) (before : RegistrationNativeG2Trace.State × Old n KeyState) :
    Prod.map id merge <$> (combined full seeds service implementation query).run before =
      (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service
        (fallback full seeds service implementation) query).run (merge before) := by
  rcases before with ⟨trace, privateState⟩
  rw [combined, QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map]
  exact RegistrationNativeG3MaterializedTracedServerRebracket.query_source full seeds service implementation query trace privateState

/-- The original observer AST and the explicit traced private interface have exactly the same complete stateful execution. -/
theorem program_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (work : OracleComp (Spec n KemSK) Value) (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) :
    result <$> (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface full seeds service implementation)
      ((simulateQ RegistrationNativeG3MaterializedTracedServerTrace.handler work).run trace)).run before =
      (simulateQ (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service
        (fallback full seeds service implementation)) work).run (join trace before) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (combined full seeds service implementation)
    (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service (fallback full seeds service implementation)) merge
    (query_source full seeds service implementation) work (trace, before)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram.program_source
