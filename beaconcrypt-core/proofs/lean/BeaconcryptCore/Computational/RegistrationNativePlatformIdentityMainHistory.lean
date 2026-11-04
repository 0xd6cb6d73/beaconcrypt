-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryCore
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOwned
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory
/-! Actual current-runtime callbacks synchronize the ordinary generated signing histories with their retained owners. The complete platform state and every failed publication prefix remain in the same execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret poolProjection)
open RegistrationNativeIdentityHistoryInvariant (Holds)
open RegistrationNativeIdentityHistoryReserved (ReservedEmpty)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {I KemSK Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def core (before : (State n KemSK source × Platform) × SourceState) := (before.1.1,before.2)
def Inv (joint : PqxdhJointIdentity.Primitives) (before : (State n KemSK source × Platform) × SourceState) :=
  RegistrationNativeIdentityMainHistory.Inv joint (core before)

/-- The bookkeeping projection preserves all signed-message synchronization facts. -/
theorem projection_inv (joint : PqxdhJointIdentity.Primitives)
    (before : (State n KemSK source × Platform) × SourceState) :
    Inv joint (poolProjection before) ↔ Inv joint before :=
  RegistrationNativeIdentityMainHistory.projection_inv joint (core before)

private theorem ordinary_execution (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState) :
    Prod.map id poolProjection <$>
      (interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary work)).run before =
      (fun result => (result.1, (({before.1.1 with context := result.2.1}, result.2.2), RegistrationNativeIdentityCompiler.poolView before.2))) <$>
        work.run (before.1.1.context, before.1.2) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    (({before.1.1 with context := result.1.2.1}, result.1.2.2), result.2))) <$> distribution)
    (RegistrationNativeIdentityMainSource.coins_source joint (work.run (before.1.1.context, before.1.2)) before.2)
  simp only [interpret, RegistrationNativePlatformIdentityMainOrdinary.ordinary, StateT.run, simulateQ_map,
    RegistrationNativeIdentityMainOrdinary.map_apply, Functor.map_map, Prod.map, id_eq, poolProjection] at law ⊢
  exact law

/-- Arbitrary actual native/platform ambient work preserves all owner histories and future-handle rejection receipts. -/
theorem ordinary_inv (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (RegistrationNativeIdentityWorld.Context n KemSK × Platform) ProbComp Value)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Inv joint before)
    (reached : result ∈ support ((interpret joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary work)).run before)) :
    Inv joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id poolProjection) reached
  rw [←support_map,ordinary_execution,support_map] at viewed
  obtain ⟨inner,_supported,same⟩ := viewed
  have retained : Inv joint (({before.1.1 with context := inner.2.1},inner.2.2),RegistrationNativeIdentityCompiler.poolView before.2) :=
    (projection_inv joint before).mpr prior
  have shifted := congrArg (fun output => Inv joint output.2) same
  exact (projection_inv joint result.2).mp (shifted ▸ retained)

/-- External platform coins preserve the private future-handle invariant, and actual native queries use its existing per-leaf receipt. -/
theorem reserved_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Domain)
    (before : RegistrationNativeIdentityWorld.State n KemSK)
    (result : (RegistrationNativePlatformIdentityProgram.Spec n KemSK).Range query × RegistrationNativeIdentityWorld.State n KemSK)
    (prior : ReservedEmpty before.identities)
    (supported : result ∈ support ((RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created query).run before)) :
    ReservedEmpty result.2.identities := by
  cases query with
  | inl query =>
    simp only [RegistrationNativePlatformIdentityProgram.implementation,StateT.run_lift,bind_pure_comp,support_map] at supported
    obtain ⟨_reply,_reached,rfl⟩ := supported
    exact prior
  | inr query => exact RegistrationNativeIdentityHistoryReserved.world_step setup checks representation created query before result prior supported

/-- The actual combined source interpreter retains every future generated row through arbitrary adaptive trees. -/
theorem reserved_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    {A : Type} (work : OracleComp (RegistrationNativePlatformIdentityProgram.Spec n KemSK) A)
    (before : RegistrationNativeIdentityWorld.State n KemSK) (result : A × RegistrationNativeIdentityWorld.State n KemSK)
    (prior : ReservedEmpty before.identities)
    (supported : result ∈ support ((simulateQ (RegistrationNativePlatformIdentityProgram.implementation (source := source) setup checks representation created) work).run before)) :
    ReservedEmpty result.2.identities :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => ReservedEmpty current.identities)
    (fun query current valid next reached => reserved_query setup checks representation created query current next valid reached)
    work before prior result supported

private theorem beacon_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativePlatformIdentityProgram.M n KemSK RegistrationServerRoleBackend.State Platform source Value)
    (preserves : ∀ before result,Holds setup.joint before.1.2.identities before.1.1.1 → ReservedEmpty before.1.2.identities →
      result ∈ support (RegistrationNativePlatformIdentityProgram.runNew setup checks representation created work before) →
      Holds setup.joint result.2.1.2.identities result.2.1.1.1)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : Value × ((State n KemSK source × Platform) × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMain.beacon setup checks representation created work)).run before)) :
    Inv setup.joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id poolProjection) supported
  rw [←support_map,RegistrationNativePlatformIdentityMain.beacon_execution,support_map] at viewed
  obtain ⟨inner,reached,same⟩ := viewed
  have initial := (projection_inv setup.joint before).mpr prior
  have held := preserves (((before.1.1.beacons,RegistrationWorldAgreementCompiler.erase before.1.1.context.server.world),
    ⟨before.1.1.context,RegistrationNativeIdentityCompiler.poolView before.2⟩),before.1.2)
    (inner.1.1.1.1,(((inner.1.1.1.2,inner.1.1.2),inner.2),inner.1.2)) initial.1 initial.2 (by
      simp only [RegistrationNativePlatformIdentityProgram.runNew,support_map]
      exact Set.mem_image_of_mem _ reached)
  have reserved := reserved_program setup checks representation created _
    ⟨before.1.1.context,RegistrationNativeIdentityCompiler.poolView before.2⟩ inner initial.2 reached
  have retained : Inv setup.joint (RegistrationNativePlatformIdentityMain.assemble inner).2 := ⟨held,reserved⟩
  rw [same] at retained
  exact (projection_inv setup.joint result.2).mp retained

/-- Actual current creation retains all earlier histories and obtains the new row from the genuine ordinary source. -/
theorem create_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Nat) × ((State n KemSK source × Platform) × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMainLifecycle.create setup edPin mlPin keyId checks representation created)).run before)) :
    Inv setup.joint result.2 := by
  rw [RegistrationNativePlatformIdentityMainLifecycle.create,RegistrationNativePlatformIdentityMain.beacon_native,
    RegistrationNativePlatformIdentityMain.interpret_lift,support_map] at supported
  obtain ⟨inner,reached,rfl⟩ := supported
  exact RegistrationNativeIdentityMainHistory.create_inv setup checks representation created edPin mlPin keyId (core before) inner prior reached

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem interpret_map {Next : Type} (joint : PqxdhJointIdentity.Primitives) (change : Value → Next)
    (work : M n KemSK Platform source Value) (before : (State n KemSK source × Platform) × SourceState) :
    (interpret joint (change <$> work)).run before = Prod.map change id <$> (interpret joint work).run before := by
  simp only [interpret,StateT.run,map_apply,simulateQ_map,Functor.map_map,Prod.map,id_eq]

/-- Full actual stateful publication preserves every attempted Ed signature through allocation and serialization failures. -/
theorem bundle_inv {E : Type} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × ((State n KemSK source × Platform) × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMainBundle.bundle setup checks representation created writer index)).run before)) :
    Inv setup.joint result.2 := by
  rw [RegistrationNativePlatformIdentityMainBundle.bundle,interpret_map,support_map] at supported
  obtain ⟨inner,reached,rfl⟩ := supported
  exact beacon_inv setup checks representation created _
    (fun current next holds _reserved called => RegistrationNativePlatformIdentityHistoryCore.bundle_holds setup checks representation created index writer current next holds called)
    before inner prior reached

/-- The actual corrected assigned-ID finish retains every owner's synchronized signing history on all outcomes. -/
theorem finish_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : (State n KemSK source × Platform) × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × ((State n KemSK source × Platform) × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityMainLifecycle.finish setup checks representation created wire index packet)).run before)) :
    Inv setup.joint result.2 := by
  apply beacon_inv setup checks representation created _ _ before result prior supported
  intro current next holds _reserved called
  rw [RegistrationNativePlatformIdentityProgram.native_run,support_map] at called
  obtain ⟨inner,reached,rfl⟩ := called
  exact RegistrationNativePlatformIdentityHistoryFinish.finish_holds setup checks representation created wire index packet current.1 inner holds reached

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.projection_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.projection_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.ordinary_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.ordinary_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.reserved_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.reserved_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.reserved_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.reserved_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.create_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.create_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.bundle_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.bundle_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.finish_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistory.finish_inv
