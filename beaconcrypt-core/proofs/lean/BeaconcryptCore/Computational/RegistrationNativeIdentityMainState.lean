-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOrdinary

/-! Ordinary native state access, Server operations and World effects preserve the full original native source when public credentials are privately realized. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainState
open RegistrationNativeIdentityMain (State M)
open RegistrationNativeIdentityMainSource (interpret project)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {KemSK Value : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- Pure replies retain their literal API value and entire privately realized native state. -/
theorem pure_source (joint : PqxdhJointIdentity.Primitives) (value : Value)
    (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$> (interpret joint (pure value)).run before = pure (value, project before) := by
  rw [RegistrationNativeIdentityMainOrdinary.interpret_pure]
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq]

/-- Executable state lookup does not reveal any privately stored Beacon identity seed. -/
theorem get_source (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK mlSource × SourceState) :
    (interpret joint (get : M n KemSK mlSource (State n KemSK mlSource))).run before = pure (before.1, before) := rfl

/-- A local executable update leaves the private joint identity table and transcript unchanged. -/
theorem modify_source (joint : PqxdhJointIdentity.Primitives)
    (change : State n KemSK mlSource → State n KemSK mlSource) (before : State n KemSK mlSource × SourceState) :
    (interpret joint (modify change : M n KemSK mlSource Unit)).run before = pure ((), (change before.1, before.2)) := rfl

/-- Actual SDK Server operations retain the literal control, moved tokens, signing receipts, World and KEM/owner state. -/
theorem server_source (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$> (interpret joint (RegistrationNativeIdentityMain.server work)).run before =
      (RegistrationNativeExperiment.server work).run (project before) := by
  have law := RegistrationNativeIdentityMainOrdinary.ordinary_source joint
    (fun current => (fun result => (result.1, { current with server := result.2 })) <$> work.run current.server) before
  simp only [RegistrationNativeIdentityMain.server, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, Prod.map, id_eq, project,
    RegistrationNativeIdentityMainOrdinary.attach] at law ⊢
  exact law

/-- Actual shared-World operations retain every native refusal and reached operational state. -/
theorem world_source (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$> (interpret joint (RegistrationNativeIdentityMain.world work)).run before =
      (RegistrationNativeExperiment.world work).run (project before) := by
  exact server_source joint _ before

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.pure_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.get_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.get_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.modify_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.modify_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.server_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainState.world_source
