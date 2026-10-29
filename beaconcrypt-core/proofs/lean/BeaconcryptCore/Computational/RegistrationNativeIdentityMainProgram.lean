-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainInvariant

/-! Concrete generated-credential ownership composes through arbitrary adaptive whole native programs. The resulting source equation retains every original typed reply and full native poststate without a supplied simulation or invariant-preservation hypothesis. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityMainSource (interpret project Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Private interpretation distributes over every actual adaptive executable client program. -/
theorem interpret_program {I : Type} {spec : OracleSpec I}
    (joint : PqxdhJointIdentity.Primitives) (client : QueryImpl spec (M n KemSK mlSource))
    (work : OracleComp spec Value) :
    interpret joint (simulateQ client work) = simulateQ (fun query => interpret joint (client query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using RegistrationNativeIdentityMainOrdinary.interpret_pure joint value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityMainOrdinary.interpret_bind]
      apply congrArg (fun continuation => interpret joint (client query) >>= continuation)
      funext reply
      exact ih reply

noncomputable def compiled (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK mlSource × SourceState) ProbComp) :=
  fun query => interpret setup.joint (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential query)

/-- Every reached adaptive source state retains the generated credential invariant established at initialization. -/
theorem program_owned (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK mlSource × SourceState)
    (result : Value × (State n KemSK mlSource × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint
      (simulateQ (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential) work)).run before)) :
    Owned setup.joint result.2 := by
  rw [interpret_program] at reached
  exact simulateQ_run_preservesInv (compiled setup checks wire route representation created credential)
    (Owned setup.joint)
    (fun query current prior after supported => RegistrationNativeIdentityMainInvariant.handler_owned
      setup checks wire route representation created credential query current after prior supported)
    work before owned result reached

/-- The actual adaptive whole typed client recovers the original complete native execution with no supplied whole-game correspondence. -/
theorem program_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK mlSource × SourceState) (owned : Owned setup.joint before) :
    Prod.map id project <$> (interpret setup.joint
      (simulateQ (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential) work)).run before =
      (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) work).run (project before) := by
  rw [interpret_program]
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← RegistrationNativeIdentityMainTyped.handler_source setup checks wire route representation created credential query before owned,
        bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result reached
      exact ih result.1 result.2 (RegistrationNativeIdentityMainInvariant.handler_owned
        setup checks wire route representation created credential query before result owned reached)

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.interpret_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.interpret_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.program_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram.program_source
