-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerBuild
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerRebracketProgram
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFootprint

/-! The exact original local G2 observer remains in the actual inlined Server build. Traced private-state reassociation and the finite current-environment build equality preserve its complete descriptor chronology, all receipts and the World. Unused fallback callbacks are eliminated by the actual build footprint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec)
open RegistrationNativeG3MaterializedTracedServerTrace (Spec Allowed handler)
open RegistrationNativeG3MaterializedTracedServerRebracket (Old New join result fallback)
variable {n : Nat} {KemSK KeyState Value : Type}

theorem interface_congr (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (first second : QueryImpl (Spec n KemSK) (StateT (New n KeyState) ProbComp))
    (work : OracleComp (Spec n KemSK) Value) (allowed : AllQueriesSatisfy work Allowed) :
    simulateQ (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service first) work =
      simulateQ (RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service second) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨current, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      have same : RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service first query =
          RegistrationNativeG3MaterializedTracedServerInterface.interface full seeds service second query := by
        rcases query with message | (message | (publication | effect)) | kem
        · exact current.elim
        · rfl
        · exact current.elim
        · rfl
        · exact current.elim
      simp only [simulateQ_bind, simulateQ_spec_query, same]
      congr 1
      funext reply
      exact ih reply (later reply)

def restoreResult (reached : Value × New n KeyState) : (Value × RegistrationNativeG2Trace.State) × Old n KeyState :=
  ((reached.1, reached.2.2.1), (reached.2.1, reached.2.2.2))

theorem restore_result (reached : (Value × RegistrationNativeG2Trace.State) × Old n KeyState) :
    restoreResult (result reached) = reached := by
  rcases reached with ⟨⟨value, trace⟩, ⟨keys, world⟩⟩
  rfl

/-- The original local observer's complete result and original private state are retained through actual known108/public44 Server build materialization. -/
theorem build (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (control : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) :
    (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface true seeds service implementation)
      ((simulateQ handler (((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run control).run env)).run trace)).run before =
      (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface false seeds service implementation)
        ((simulateQ handler (((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run control).run env)).run trace)).run before := by
  let work := (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK) hkdf wire checks sign handle application).run control).run env)
  have allowed : AllQueriesSatisfy work Allowed := RegistrationNativeG3MaterializedTracedServerFootprint.build_allowed hkdf wire checks sign handle application control env
  have materialized := RegistrationNativeG3MaterializedTracedServerBuild.build_source seeds service
    (fallback true seeds service implementation) hkdf wire checks sign handle application control (env, join trace before)
  simp only [RegistrationNativeG3MaterializedTracedServerInterface.lower, StateT.run] at materialized
  have changed := congrArg (Functor.map (fun reached => ((reached.1, reached.2.1), reached.2.2))) materialized
  simp only [Functor.map_map, id_map'] at changed
  change (simulateQ (RegistrationNativeG3MaterializedTracedServerInterface.interface true seeds service
    (fallback true seeds service implementation)) work).run (join trace before) =
    (simulateQ (RegistrationNativeG3MaterializedTracedServerInterface.interface false seeds service
      (fallback true seeds service implementation)) work).run (join trace before) at changed
  have swap := congrArg (fun action => action.run (join trace before))
    (interface_congr false seeds service (fallback false seeds service implementation) (fallback true seeds service implementation) work allowed)
  have coupled := (RegistrationNativeG3MaterializedTracedServerRebracketProgram.program_source true seeds service implementation work trace before).trans
    (changed.trans (swap.symm.trans (RegistrationNativeG3MaterializedTracedServerRebracketProgram.program_source false seeds service implementation work trace before).symm))
  have restored := congrArg (Functor.map restoreResult) coupled
  simpa only [Functor.map_map, Function.comp_def, restore_result, id_map'] using restored

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.interface_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.interface_congr

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.restore_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.restore_result

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerObservedBuild.build
