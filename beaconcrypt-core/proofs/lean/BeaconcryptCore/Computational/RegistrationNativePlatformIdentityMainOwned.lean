-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishMetadata
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned

/-! Every actual current-runtime indexed identity callback preserves genuine generated-handle ownership on all outcomes. Immutable owner metadata and private seed-prefix facts are derived from the actual controller; creation derives its fresh row from the ordinary joint source. No ownership condition is imposed on a public protocol event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def core (before : (State n KemSK source × Platform) × SourceState) := (before.1.1, before.2)
def Owned (joint : PqxdhJointIdentity.Primitives) (before : (State n KemSK source × Platform) × SourceState) :=
  RegistrationNativeIdentityMainSource.Owned joint (core before)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem interpret_map (joint : PqxdhJointIdentity.Primitives) {Next : Type} (change : Value → Next)
    (work : M n KemSK Platform source Value) (before : (State n KemSK source × Platform) × SourceState) :
    (interpret joint (change <$> work)).run before = Prod.map change id <$> (interpret joint work).run before := by
  simp only [interpret, StateT.run, map_apply, simulateQ_map, Functor.map_map, Prod.map, id_eq]

private theorem ordinary_execution (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState) :
    Prod.map id RegistrationNativePlatformIdentityMain.poolProjection <$>
      (interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary work)).run before =
      (fun result => (result.1, (({before.1.1 with context := result.2.1}, result.2.2), RegistrationNativeIdentityCompiler.poolView before.2))) <$>
        work.run (before.1.1.context, before.1.2) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    (({before.1.1 with context := result.1.2.1}, result.1.2.2), result.2))) <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint (work.run (before.1.1.context, before.1.2)) before.2)
  simp only [interpret, RegistrationNativePlatformIdentityMainOrdinary.ordinary, StateT.run, simulateQ_map,
    map_apply, Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformIdentityMain.poolProjection] at law ⊢
  exact law

/-- Actual ordinary native/platform work preserves all generated handles and rows. -/
theorem ordinary_owned (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (owned : Owned joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary work)).run before)) :
    Owned joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativePlatformIdentityMain.poolProjection) reached
  rw [← support_map, ordinary_execution, support_map] at viewed
  obtain ⟨inner, _supported, same⟩ := viewed
  have retained : Owned joint (({before.1.1 with context := inner.2.1}, inner.2.2), RegistrationNativeIdentityCompiler.poolView before.2) := owned
  have shifted := congrArg (fun output => Owned joint output.2) same
  exact shifted ▸ retained

private theorem beacon_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (metadata : RegistrationNativePlatformIdentityBundleMetadata.Preserves work)
    (keeps : RegistrationNativePlatformIdentityProgram.Keeps setup checks representation created work)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMain.beacon setup checks representation created work)).run before)) :
    Owned setup.joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativePlatformIdentityMain.poolProjection) reached
  rw [← support_map, RegistrationNativePlatformIdentityMain.beacon_execution, support_map] at viewed
  obtain ⟨inner, supported, same⟩ := viewed
  have fields := metadata before.1.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world) before.1.2 inner.1 (by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) _
      (⟨before.1.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ : RegistrationNativeIdentityWorld.State n KemSK)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported)
  have seeds := keeps (((before.1.1.beacons, RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world),
    ⟨before.1.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩), before.1.2)
    (inner.1.1.1.1, (((inner.1.1.1.2, inner.1.1.2), inner.2), inner.1.2)) (by
      simp only [RegistrationNativePlatformIdentityProgram.runNew, support_map]
      exact Set.mem_image_of_mem _ supported)
  have retained : Owned setup.joint (RegistrationNativePlatformIdentityMain.assemble inner).2 :=
    RegistrationNativeIdentityLifecycleOwned.owned_after_fields setup.joint
      (RegistrationNativeIdentityCompiler.poolView before.2) inner.2.identities before.1.1.beacons inner.1.1.1.2 owned fields seeds
  rw [same] at retained
  exact retained

/-- Actual creation obtains the same genuinely generated row and preserves every prior handle, including failures. -/
theorem create_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Nat) × ((State n KemSK source × Platform) × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMainLifecycle.create setup edPin mlPin keyId checks representation created)).run before)) :
    Owned setup.joint result.2 := by
  rw [RegistrationNativePlatformIdentityMainLifecycle.create, RegistrationNativePlatformIdentityMain.beacon_native,
    RegistrationNativePlatformIdentityMain.interpret_lift, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact RegistrationNativeIdentityMainOwned.create_owned setup checks representation created edPin mlPin keyId (core before) inner owned supported

/-- Every stateful bundle outcome preserves genuine generated ownership, including Ed/ML signing and source writer failures. -/
theorem bundle_owned {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × ((State n KemSK source × Platform) × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainBundle.bundle setup checks representation created writer index)).run before)) :
    Owned setup.joint result.2 := by
  rw [RegistrationNativePlatformIdentityMainBundle.bundle, interpret_map, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact beacon_owned setup checks representation created _
    (RegistrationNativePlatformIdentityBundleMetadata.bundle_preserves setup index writer)
    (RegistrationNativePlatformIdentityBundleRun.bundle_keeps setup checks representation created index writer) before inner owned supported

/-- Actual corrected assigned-ID finish keeps generated handles through all authentication, agreement, record and installation outcomes. -/
theorem finish_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × ((State n KemSK source × Platform) × SourceState)) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityMainLifecycle.finish setup checks representation created wire index packet)).run before)) :
    Owned setup.joint result.2 :=
  beacon_owned setup checks representation created _
    (RegistrationNativePlatformIdentityBundleMetadata.native_preserves _ (RegistrationNativePlatformIdentityFinishMetadata.finish_preserves setup wire index packet))
    (RegistrationNativePlatformIdentityProgram.native_keeps setup checks representation created _
      (RegistrationNativePlatformIdentityFinishRun.finish_keeps setup checks representation created wire index packet)) before result owned reached

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.ordinary_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.ordinary_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.create_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.create_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.bundle_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned.finish_owned
