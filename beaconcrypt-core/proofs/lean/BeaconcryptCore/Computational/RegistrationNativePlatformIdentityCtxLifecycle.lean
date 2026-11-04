-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxMain
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned
/-! Actual creation, stateful bundle writing and assigned-ID finish share the same physical CTX backend and ordinary indexed service. Full native and persistent platform states are restored; prior uniform source transcript entries alone are normalized. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret project)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def oldBefore (before : Full n KemSK Platform source) :
    (RegistrationNativeIdentityMain.State n KemSK source × Platform) × PqxdhDynamicIdentityPool.SourceState :=
  (({before.1.1 with context := RegistrationNativePlatformIdentityCtxAmbient.replace before.2.2.1 before.1.1.context}, before.1.2), before.2.1)

def native (before : Full n KemSK Platform source) : RegistrationNativeExperiment.State n KemSK source × Platform :=
  RegistrationNativePlatformIdentityMain.project (project before)

def Owned (joint : PqxdhJointIdentity.Primitives) (before : Full n KemSK Platform source) : Prop :=
  RegistrationNativePlatformIdentityMainOwned.Owned joint (oldBefore before)

private theorem pool_projection (before : (RegistrationNativeIdentityMain.State n KemSK source × Platform) × PqxdhDynamicIdentityPool.SourceState) :
    RegistrationNativePlatformIdentityMain.project (RegistrationNativePlatformIdentityMain.poolProjection before) =
      RegistrationNativePlatformIdentityMain.project before :=
  congrArg (fun value => (value, before.1.2)) (RegistrationNativeIdentityMainSource.project_pool_view before.1.1 before.2)

/-- Source restoration preserves every native field and ignores only the indexed service's extra uniform transcript entries. -/
theorem beacon_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source A)
    (before : Full n KemSK Platform source) :
    Prod.map id native <$> (interpret setup.joint (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created work)).run before =
      Prod.map id RegistrationNativePlatformIdentityMain.project <$>
        (RegistrationNativePlatformIdentityMain.interpret setup.joint
          (RegistrationNativePlatformIdentityMain.beacon setup checks representation created work)).run (oldBefore before) := by
  have same := congrArg (fun distribution => Prod.map id RegistrationNativePlatformIdentityMain.project <$> distribution)
    (RegistrationNativePlatformIdentityCtxMain.beacon_source setup checks representation created work before)
  simpa only [Functor.map_map, native, oldBefore, Prod.map_def, id_eq, pool_projection] using same

noncomputable def create (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) : M n KemSK Platform source (RustM (Option Nat)) :=
  RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native (RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId))

/-- Actual creation retains its generated row, optional failure, complete native counters and original P. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    Prod.map id native <$> (interpret setup.joint (create setup edPin mlPin keyId checks representation created)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon setup checks representation created (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))).run
          (native before).1).run (native before).2 := by
  exact (beacon_native setup checks representation created _ before).trans
    (RegistrationNativePlatformIdentityMainLifecycle.create_source setup checks representation created edPin mlPin keyId (oldBefore before) owned)

noncomputable def finish (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK Platform source (RustM (Option Pqxdh.Bytes)) :=
  RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
    (RegistrationNativePlatformIdentityProgram.native (RegistrationNativePlatformIdentityFinishRun.finish setup source wire index packet))

/-- The source finish retains early abort, assigned sender ID, copied payload, installation and every failed prefix. -/
theorem finish_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    Prod.map id native <$> (interpret setup.joint (finish setup checks representation created wire index packet)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins
          (RegistrationNativeExperiment.beacon setup checks representation created (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet))).run
          (native before).1).run (native before).2 := by
  exact (beacon_native setup checks representation created _ before).trans
    (RegistrationNativePlatformIdentityMainLifecycle.finish_source setup checks representation created wire index packet (oldBefore before) owned)

noncomputable def bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) : M n KemSK Platform source (RustM (Option Pqxdh.Bytes)) :=
  RegistrationNativePlatformIdentityNativeBundle.reply <$>
    RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer)

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The complete effectful six-field writer uses the same P and physical cache on successful and failed publication. -/
theorem bundle_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    Prod.map id native <$> (interpret setup.joint (bundle setup checks representation created writer index)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformExperiment.bundle RegistrationNativePlatformMldsaProgram.coins setup checks representation created source writer index).run
          (native before).1).run (native before).2 := by
  have same := congrArg (fun distribution => Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$> distribution)
    (beacon_native setup checks representation created (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) before)
  calc
    _ = Prod.map id RegistrationNativePlatformIdentityMain.project <$>
      (RegistrationNativePlatformIdentityMain.interpret setup.joint
        (RegistrationNativePlatformIdentityMainBundle.bundle setup checks representation created writer index)).run (oldBefore before) := by
      simpa only [bundle, RegistrationNativePlatformIdentityMainBundle.bundle, interpret,
        RegistrationNativePlatformIdentityMain.interpret, StateT.run, state_map_apply, simulateQ_map,
        Functor.map_map, Prod.map_def, id_eq] using same
    _ = _ := RegistrationNativePlatformIdentityMainBundle.bundle_source setup checks representation created writer index (oldBefore before) owned

private theorem owned_from_projection (joint : PqxdhJointIdentity.Primitives)
    (left : ProbComp (A × Full n KemSK Platform source))
    (right : ProbComp (A × ((RegistrationNativeIdentityMain.State n KemSK source × Platform) × PqxdhDynamicIdentityPool.SourceState)))
    (same : Prod.map id project <$> left = Prod.map id RegistrationNativePlatformIdentityMain.poolProjection <$> right)
    (keeps : ∀ inner ∈ support right, RegistrationNativePlatformIdentityMainOwned.Owned joint inner.2)
    (result : A × Full n KemSK Platform source) (reached : result ∈ support left) : Owned joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id project) reached
  rw [← support_map, same, support_map] at viewed
  obtain ⟨inner, supported, equal⟩ := viewed
  have retained : RegistrationNativePlatformIdentityMainOwned.Owned joint (RegistrationNativePlatformIdentityMain.poolProjection inner.2) := keeps inner supported
  have shifted := congrArg (fun output => RegistrationNativePlatformIdentityMainOwned.Owned joint output.2) equal
  have carried : RegistrationNativePlatformIdentityMainOwned.Owned joint (project result.2) := shifted ▸ retained
  exact carried

/-- The actual CTX creation callback preserves every genuine generated row through all optional outcomes. -/
theorem create_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : Full n KemSK Platform source) (result : RustM (Option Nat) × Full n KemSK Platform source)
    (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (create setup edPin mlPin keyId checks representation created)).run before)) :
    Owned setup.joint result.2 := by
  apply owned_from_projection setup.joint _ _ (RegistrationNativePlatformIdentityCtxMain.beacon_source setup checks representation created _ before) _ result reached
  intro inner supported
  exact RegistrationNativePlatformIdentityMainOwned.create_owned setup checks representation created edPin mlPin keyId (oldBefore before) inner owned supported

/-- The actual assigned-ID finish retains generated ownership through every failed source operation. -/
theorem finish_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : Full n KemSK Platform source) (result : RustM (Option Pqxdh.Bytes) × Full n KemSK Platform source)
    (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (finish setup checks representation created wire index packet)).run before)) :
    Owned setup.joint result.2 := by
  apply owned_from_projection setup.joint _ _ (RegistrationNativePlatformIdentityCtxMain.beacon_source setup checks representation created _ before) _ result reached
  intro inner supported
  exact RegistrationNativePlatformIdentityMainOwned.finish_owned setup checks representation created wire index packet (oldBefore before) inner owned supported

private theorem bundle_projection (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : Full n KemSK Platform source) :
    Prod.map id project <$> (interpret setup.joint (bundle setup checks representation created writer index)).run before =
      Prod.map id RegistrationNativePlatformIdentityMain.poolProjection <$>
        (RegistrationNativePlatformIdentityMain.interpret setup.joint
          (RegistrationNativePlatformIdentityMainBundle.bundle setup checks representation created writer index)).run (oldBefore before) := by
  have same := congrArg (fun distribution => Prod.map RegistrationNativePlatformIdentityNativeBundle.reply id <$> distribution)
    (RegistrationNativePlatformIdentityCtxMain.beacon_source setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) before)
  simpa only [bundle, RegistrationNativePlatformIdentityMainBundle.bundle, interpret,
    RegistrationNativePlatformIdentityMain.interpret, StateT.run, state_map_apply, simulateQ_map,
    Functor.map_map, Prod.map_def, id_eq, oldBefore] using same

/-- Stateful source writing keeps every generated row even when signing or serialization fails. -/
theorem bundle_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : Full n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × Full n KemSK Platform source) (owned : Owned setup.joint before)
    (reached : result ∈ support ((interpret setup.joint (bundle setup checks representation created writer index)).run before)) :
    Owned setup.joint result.2 := by
  apply owned_from_projection setup.joint _ _ (bundle_projection setup checks representation created writer index before) _ result reached
  intro inner supported
  exact RegistrationNativePlatformIdentityMainOwned.bundle_owned setup checks representation created writer index (oldBefore before) inner owned supported
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.beacon_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.beacon_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.bundle_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.create_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.create_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.finish_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.bundle_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycle.bundle_owned
