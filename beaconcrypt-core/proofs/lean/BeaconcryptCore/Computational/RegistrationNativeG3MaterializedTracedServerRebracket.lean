-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerTrace

/-! Reassociate the actual local chronological observer into the private trace/World state. Demand and effect queries have the exact explicit traced interface; all other original callbacks are retained as an executable observed fallback. This is an operational source equality, not an assumed trace equivalence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracket
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState Value : Type}
abbrev Spec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK
abbrev Old (n : Nat) (KeyState : Type) := RegistrationNativeG3MaterializedFrontendInterface.Private n KeyState
abbrev New (n : Nat) (KeyState : Type) := RegistrationNativeG3MaterializedTracedServerInterface.Private n KeyState

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

def join (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) : New n KeyState :=
  (before.1, (trace, before.2))

def result (reached : (Value × RegistrationNativeG2Trace.State) × Old n KeyState) : Value × New n KeyState :=
  (reached.1.1, join reached.1.2 reached.2)

noncomputable def fallback (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp)) :
    QueryImpl (Spec n KemSK) (StateT (New n KeyState) ProbComp) := fun query before =>
  result <$> (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface full seeds service implementation)
    ((RegistrationNativeG3MaterializedTracedServerTrace.handler query).run before.2.1)).run (before.1, before.2.2)

theorem query_source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (query : (Spec n KemSK).Domain) (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) :
    result <$> (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface full seeds service implementation)
      ((RegistrationNativeG3MaterializedTracedServerTrace.handler query).run trace)).run before =
      (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service
        (fallback full seeds service implementation) query).run (join trace before) := by
  rcases query with message | (message | (publication | effect)) | kem
  · rfl
  · cases full <;> simp only [RegistrationNativeG3MaterializedTracedServerTrace.handler, StateT.run,
      RegistrationNativeG3MaterializedTracedServerTrace.begin, RegistrationNativeG3MaterializedTracedServerTrace.finish,
      simulateQ_map, simulateQ_spec_query, RegistrationNativeG3MaterializedFrontendInterface.interface,
      RegistrationNativeG3MaterializedFrontendInterface.keys, RegistrationNativeG3MaterializedTracedServerInterface.interface,
      RegistrationNativeG3MaterializedTracedServerInterface.keys, Functor.map_map, join, result,
      Bool.false_eq_true, ite_true, ite_false, state_map_apply, Prod.map_def, id_eq,
      ]
    all_goals rfl
  · rfl
  · cases full <;> cases effect with
    | inl coin =>
        simp [RegistrationNativeG3MaterializedTracedServerTrace.handler, StateT.run,
          RegistrationNativeG3MaterializedTracedServerTrace.begin, RegistrationNativeG3MaterializedTracedServerTrace.finish,
          RegistrationNativeG3MaterializedFrontendInterface.interface, RegistrationNativeG3MaterializedFrontendInterface.effect,
          RegistrationNativeG3MaterializedTracedServerInterface.interface, RegistrationNativeG3MaterializedTracedServerInterface.effect,
          RegistrationNativeG3MaterializedTracedServerCommon.effect, RegistrationNativeG3MaterializedTracedServerCommon.effectQuery,
          RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, join, result, Functor.map_map, state_map_apply, Prod.map_def, id_eq]
    | inr capability =>
        cases capability
        all_goals try (rename_i first second kernel; guard_hyp kernel : PqxdhRecordLiftInterface.KernelRef n; cases kernel)
        all_goals simp [RegistrationNativeG3MaterializedTracedServerTrace.handler, StateT.run,
          RegistrationNativeG3MaterializedTracedServerTrace.begin, RegistrationNativeG3MaterializedTracedServerTrace.finish,
          RegistrationNativeG3MaterializedFrontendInterface.interface, RegistrationNativeG3MaterializedFrontendInterface.effect,
          RegistrationNativeG3MaterializedTracedServerInterface.interface, RegistrationNativeG3MaterializedTracedServerInterface.effect,
          RegistrationNativeG3MaterializedTracedServerCommon.effect, RegistrationNativeG3MaterializedTracedServerCommon.effectQuery,
          RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.effect, join, result, Functor.map_map, state_map_apply, Prod.map_def, id_eq]
  · rfl

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracket

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracket.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracket.query_source
