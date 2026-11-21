-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceKeyPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistorySync

/-! The actual shared-CTX owner callbacks preserve immutable key indices. Construction extends the old list; every other literal callback keeps it. Generated-handle distinctness is proved from actual private row ownership, without any restriction on public-key aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMetadata (keys)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret project)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem native_support (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State source A)
    (before : Full n KemSK Platform source) (result : A × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityProgram.native work))).run before)) :
    ∃ raw, raw ∈ support ((simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := source) setup checks representation created)
      ((work.run before.1.1.beacons).run (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world))).run
        ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,
          RegistrationNativeIdentityCompiler.poolView before.2.1⟩) ∧ raw.1.1.2 = result.2.1.1.beacons := by
  have viewed := Set.mem_image_of_mem (Prod.map id project) reached
  rw [← support_map, RegistrationNativePlatformIdentityCtxMain.beacon_execution, support_map] at viewed
  obtain ⟨inner, supported, same⟩ := viewed
  have regrouped := Set.mem_image_of_mem (fun output => (output.1.1.1.1, (((output.1.1.1.2, output.1.1.2), output.2), output.1.2))) supported
  rw [← support_map] at regrouped
  change _ ∈ support (RegistrationNativePlatformIdentityProgram.runNew setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native work)
      (((before.1.1.beacons, RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world),
        ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,
          RegistrationNativeIdentityCompiler.poolView before.2.1⟩), before.1.2)) at regrouped
  rw [RegistrationNativePlatformIdentityProgram.native_run, support_map] at regrouped
  obtain ⟨middle, called, middleEq⟩ := regrouped
  rw [RegistrationNativeIdentitySourceSimulation.runNew, support_map] at called
  obtain ⟨raw, rawCall, rawEq⟩ := called
  refine ⟨raw, rawCall, ?_⟩
  have first := congrArg (fun value => value.2.1.1.1) middleEq
  have second := congrArg (fun value => value.2.1.1.beacons) same
  have third := congrArg (fun value => value.2.1.1) rawEq
  exact third.trans (first.trans second)

private theorem beacon_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (metadata : RegistrationNativePlatformIdentityBundleMetadata.Preserves work)
    (before : Full n KemSK Platform source) (result : A × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work)).run before)) :
    keys result.2.1.1.beacons = keys before.1.1.beacons := by
  have viewed := Set.mem_image_of_mem (Prod.map id project) reached
  rw [← support_map, RegistrationNativePlatformIdentityCtxMain.beacon_execution, support_map] at viewed
  obtain ⟨inner, supported, same⟩ := viewed
  have fields := metadata before.1.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world) before.1.2 inner.1 (by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) _
      (⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,
        RegistrationNativeIdentityCompiler.poolView before.2.1⟩ : RegistrationNativeIdentityWorld.State n KemSK)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported)
  exact (congrArg (fun value => keys value.2.1.1.beacons) same).symm.trans fields

/-- Creation preserves all old immutable tuples at exactly their original positions. -/
theorem create_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Full n KemSK Platform source) (result : RustM (Option Nat) × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created)).run before)) :
    keys before.1.1.beacons <+: keys result.2.1.1.beacons := by
  obtain ⟨raw, called, same⟩ := native_support setup checks representation created
    (RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId) before result reached
  rw [← same]
  exact RegistrationNativeIdentitySourceKeyPrefix.create_prefix setup checks representation created edPin mlPin keyId _ _ _ raw called

/-- The actual private source assigns a distinct handle even if public keys alias. -/
theorem create_distinct (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Full n KemSK Platform source) (result : RustM (Option Nat) × Full n KemSK Platform source)
    (owned : Owned setup.joint before) (distinct : RegistrationNativeIdentityHistorySync.Distinct before.1.1.beacons)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.create setup edPin mlPin keyId checks representation created)).run before)) :
    RegistrationNativeIdentityHistorySync.Distinct result.2.1.1.beacons := by
  obtain ⟨raw, called, same⟩ := native_support setup checks representation created
    (RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId) before result reached
  rw [← same]
  have prior : RegistrationNativeIdentityRealization.Owned setup.joint
      (RegistrationNativeIdentityCompiler.poolView before.2.1) before.1.1.beacons := owned
  exact RegistrationNativeIdentitySourceDistinct.create_distinct setup checks representation created edPin mlPin keyId
    before.1.1.beacons _ ⟨RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context,
      RegistrationNativeIdentityCompiler.poolView before.2.1⟩ raw prior distinct called

/-- Stateful publication, including a failed writer, changes no immutable tuple. -/
theorem bundle_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : Full n KemSK Platform source) (result : RustM (Option Pqxdh.Bytes) × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before)) :
    keys result.2.1.1.beacons = keys before.1.1.beacons := by
  have same : (interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index)).run before =
      Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$>
        (interpret setup.joint (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer))).run before := by
    simp only [RegistrationNativePlatformIdentityCtxLifecycle.bundle, interpret, StateT.run,
      map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq]
  rw [same, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact beacon_keys setup checks representation created _ (RegistrationNativePlatformIdentityBundleMetadata.bundle_preserves setup index writer) before inner supported

/-- Corrected assigned-ID finish retains every captured key tuple through all terminal branches. -/
theorem finish_keys (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : Full n KemSK Platform source) (result : RustM (Option Pqxdh.Bytes) × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.finish setup checks representation created wire index packet)).run before)) :
    keys result.2.1.1.beacons = keys before.1.1.beacons :=
  beacon_keys setup checks representation created _
    (RegistrationNativePlatformIdentityBundleMetadata.native_preserves _
      (RegistrationNativePlatformIdentityFinishMetadata.finish_preserves setup wire index packet)) before result reached

/-- All non-Beacon SDK routes retain the complete owner roster through the physical backend. -/
theorem ordinary_keys (joint : PqxdhJointIdentity.Primitives)
    (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A)
    (before : Full n KemSK Platform source) (result : A × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret joint (RegistrationNativePlatformIdentityCtxOrdinary.ordinary work)).run before)) :
    result.2.1.1.beacons = before.1.1.beacons := by
  have viewed := Set.mem_image_of_mem (Prod.map id project) reached
  rw [← support_map, RegistrationNativePlatformIdentityCtxOrdinary.ordinary_source, support_map] at viewed
  obtain ⟨inner, _called, same⟩ := viewed
  exact (congrArg (fun value => value.2.1.1.beacons) same).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.create_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.create_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.create_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.create_distinct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.bundle_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.bundle_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.finish_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.finish_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.ordinary_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyPrefix.ordinary_keys
