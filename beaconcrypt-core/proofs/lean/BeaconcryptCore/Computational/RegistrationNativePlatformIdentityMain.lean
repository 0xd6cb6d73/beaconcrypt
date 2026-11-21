-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCompiler
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainBeacon

/-! The effectful generated-Ed client executes ordinary indexed joint requests while retaining the complete opaque owner roster, native context and external platform state. Native and external randomness use their literal branches; only the joint game's extra uniform transcript entries are projected away. This execution spine does not yet assert source correspondence of the whole runtime handler or a publication-security bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDynamicIdentityPool (SourceState)
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeIdentityMain (State)
variable {n : Nat} {ι KemSK Value Platform : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev M (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (State n KemSK source × Platform) (OracleComp ProtocolSpec)

def liftMain (work : RegistrationNativeIdentityMain.M n KemSK source Value) : M n KemSK Platform source Value :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value) :
    M n KemSK Platform source Value := fun before => do
  let result ← simulateQ RegistrationNativeIdentityMain.dynamicLift
    ((simulateQ (RegistrationNativePlatformIdentityCompiler.implementation (source := source) setup checks representation created)
      (((work.run before.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)).run before.2)).run before.1.context)
  pure (result.1.1.1.1, ({
    context := { result.2 with server := { result.2.server with
      world := RegistrationWorldAgreementCompiler.join result.1.1.2 result.2.server.world.world.1 } }
    beacons := result.1.1.1.2 }, result.1.2))

def interpret (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK Platform source Value) :
    StateT ((State n KemSK source × Platform) × SourceState) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeIdentityMainSource.implementation joint) (work.run before.1)).run before.2

def project (before : (State n KemSK source × Platform) × SourceState) :
    RegistrationNativeExperiment.State n KemSK source × Platform :=
  (RegistrationNativeIdentityMainSource.project (before.1.1, before.2), before.1.2)

def poolProjection (before : (State n KemSK source × Platform) × SourceState) :=
  (before.1, RegistrationNativeIdentityCompiler.poolView before.2)

def assemble (result : (((Value × RegistrationNativeIdentityFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × Platform) ×
    RegistrationNativeIdentityWorld.State n KemSK) : Value × ((State n KemSK source × Platform) × SourceState) :=
  (result.1.1.1.1, (({
    context := { result.2.context with server := { result.2.context.server with
      world := RegistrationWorldAgreementCompiler.join result.1.1.2 result.2.context.server.world.world.1 } }
    beacons := result.1.1.1.2 }, result.1.2), result.2.identities))

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem dynamic_apply (joint : PqxdhJointIdentity.Primitives)
    (work : OracleComp PqxdhDynamicIdentityPool.DynamicSpec Value) (before : SourceState) :
    simulateQ (RegistrationNativeIdentityMainSource.implementation joint)
      (simulateQ RegistrationNativeIdentityMain.dynamicLift work) before =
      simulateQ (PqxdhDynamicIdentityPool.lazyImpl joint) work before :=
  RegistrationNativeIdentityMainSource.dynamic_program joint work before

/-- The whole effectful indexed frontend has its literal ordinary joint-source execution, including the reached platform state and private service log. -/
theorem beacon_execution (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (before : (State n KemSK source × Platform) × SourceState) :
    Prod.map id poolProjection <$> (interpret setup.joint (beacon setup checks representation created work)).run before =
      assemble <$> (simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created)
        (((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2)).run
          ⟨before.1.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ := by
  let script := ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world)).run before.1.2
  have law := congrArg (fun distribution => assemble <$> distribution)
    (RegistrationNativePlatformIdentityCompiler.program_source (source := source) setup checks representation created script (before.1.1.context, before.2))
  rw [RegistrationNativePlatformIdentityCompiler.compiled_program] at law
  simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeIdentityCompiler.project] at law
  simp only [interpret, beacon, StateT.run, bind_pure_comp, simulateQ_map,
    RegistrationNativeIdentityMainOrdinary.map_apply, dynamic_apply, Functor.map_map,
    Prod.map, id_eq, poolProjection, assemble, script] at law ⊢
  exact law

/-- Ordinary native subtrees reuse their original counted compiler; adding external state does not reset or re-count any native primitive work. -/
theorem beacon_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source Value) :
    beacon setup checks representation created (RegistrationNativePlatformIdentityProgram.native (Platform := Platform) work) =
      liftMain (RegistrationNativeIdentityMain.beacon setup checks representation created work) := by
  funext before
  have composite : RegistrationNativePlatformIdentityCompiler.implementation (source := source) setup checks representation created ∘ₛ
      (RegistrationNativePlatformIdentityProgram.nativeLift (n := n) (KemSK := KemSK)) =
      RegistrationNativeIdentityCompiler.implementation (source := source) setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePlatformIdentityProgram.nativeLift,
      simulateQ_spec_query, RegistrationNativePlatformIdentityCompiler.implementation]
  simp only [beacon, RegistrationNativePlatformIdentityProgram.native, StateT.run, simulateQ_map]
  rw [← QueryImpl.simulateQ_compose, composite]
  simp only [liftMain, RegistrationNativeIdentityMain.beacon, StateT.run, bind_pure_comp,
    state_map_apply, simulateQ_map, Functor.map_map, Prod.map, id_eq]

/-- Source interpretation of independent native work retains the exact external state as an additional coordinate. -/
theorem interpret_lift (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativeIdentityMain.M n KemSK source Value)
    (before : (State n KemSK source × Platform) × SourceState) :
    (interpret joint (liftMain work)).run before =
      (fun result => (result.1, ((result.2.1, before.1.2), result.2.2))) <$>
        (RegistrationNativeIdentityMainSource.interpret joint work).run (before.1.1, before.2) := by
  simp only [interpret, liftMain, RegistrationNativeIdentityMainSource.interpret, StateT.run,
    simulateQ_map, RegistrationNativeIdentityMainOrdinary.map_apply, Functor.map_map, Prod.map, id_eq]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.beacon_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.beacon_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.beacon_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.beacon_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.interpret_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMain.interpret_lift
