-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOld

/-! Whole native Beacon interpretation retains its complete public frontend and private generated identity table after projecting only the joint game's extra uniform transcript entries. This exact execution law supports both source realization and derived ownership invariants. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret project)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def poolProjection (before : State n KemSK mlSource × SourceState) :=
  (before.1, RegistrationNativeIdentityCompiler.poolView before.2)

def assemble (result : ((Value × RegistrationNativeIdentityFrontend.State mlSource) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
      RegistrationNativeIdentityWorld.State n KemSK) : Value × (State n KemSK mlSource × SourceState) :=
  (result.1.1.1, ({
    context := { result.2.context with
      server := { result.2.context.server with
        world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.context.server.world.world.1 } }
    beacons := result.1.1.2 }, result.2.identities))

private theorem dynamic_apply (joint : PqxdhJointIdentity.Primitives)
    (work : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value) (before : SourceState) :
    simulateQ (RegistrationNativeIdentityMainSource.implementation joint)
      (simulateQ RegistrationNativeIdentityMain.dynamicLift work) before =
      simulateQ (PqxdhDynamicIdentityPool.lazyImpl joint) work before :=
  RegistrationNativeIdentityMainSource.dynamic_program joint work before

/-- The complete actual public owner/Env native program opens to its same-World indexed source with all private seed and transcript state retained. -/
theorem beacon_execution (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value)
    (before : State n KemSK mlSource × SourceState) :
    Prod.map id poolProjection <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created work)).run before =
      assemble <$>
        (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := mlSource) setup checks representation created)
          ((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world))).run
          ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ := by
  let script := (work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
  have law := congrArg (fun distribution => assemble <$> distribution)
    (RegistrationNativeIdentityCompiler.program_source (source := mlSource) setup checks representation created script (before.1.context, before.2))
  rw [RegistrationNativeIdentityCompiler.compiled_program] at law
  simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeIdentityCompiler.project] at law
  change Prod.map id poolProjection <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
        ((RegistrationNativeIdentityMain.beacon setup checks representation created work).run before.1)).run before.2) = _
  simp only [RegistrationNativeIdentityMain.beacon, StateT.run, bind_pure_comp,
    simulateQ_map, RegistrationNativeIdentityMainOrdinary.map_apply, dynamic_apply, Functor.map_map,
    Prod.map, id_eq, poolProjection, assemble, script] at law ⊢
  exact law

/-- Private native source realization ignores only the additional uniform transcript entries and restores every generated owner seed. -/
theorem beacon_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value)
    (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created work)).run before =
      (fun result => RegistrationNativeIdentityMainOld.assemble
        (RegistrationNativeIdentityRealization.observe (fun _ reply => reply) result)) <$>
        (simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := mlSource) setup checks representation created)
          ((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world))).run
          ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ := by
  have law := congrArg (fun distribution => Prod.map id project <$> distribution)
    (beacon_execution setup checks representation created work before)
  simp only [Functor.map_map, Prod.map, id_eq, poolProjection,
    assemble,
    RegistrationNativeIdentityMainOld.assemble, RegistrationNativeIdentityRealization.observe,
    project] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon.beacon_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon.beacon_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon.beacon_source
