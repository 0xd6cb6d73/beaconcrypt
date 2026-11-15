-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainOwned
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryBundle
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryFinish
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryObservation

/-! The whole public native client retains exact chronological indexed signing histories. These invariants lift through the actual same-World Beacon compiler and ordinary native SDK effects; only duplicate uniform transcript entries are projected in the internal execution correspondence. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityMainSource (interpret)
open RegistrationNativeIdentityHistoryInvariant (Holds)
open RegistrationNativeIdentityHistoryReserved (ReservedEmpty)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

def Inv (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK mlSource × SourceState) : Prop :=
  Holds joint before.2 before.1.beacons ∧ ReservedEmpty before.2

theorem projection_inv (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK mlSource × SourceState) :
    Inv joint (RegistrationNativeIdentityMainBeacon.poolProjection before) ↔ Inv joint before := by
  simp only [Inv, RegistrationNativeIdentityMainBeacon.poolProjection, Holds,
    RegistrationNativeIdentityRealization.Owned, RegistrationNativeIdentityCallbacks.Owns,
    RegistrationNativeIdentityCompiler.poolView, RegistrationNativeIdentityHistorySync.Synced,
    RegistrationNativeIdentityHistoryReserved.ReservedEmpty,
    RegistrationNativeIdentityHistoryObservation.history_filter]

/-- Ordinary native effects retain exact owner histories and all future-handle rejection receipts. -/
theorem ordinary_inv (joint : PqxdhJointIdentity.Primitives)
    (work : StateT (Context n KemSK) ProbComp Value) (before : State n KemSK mlSource × SourceState)
    (result : Value × (State n KemSK mlSource × SourceState)) (prior : Inv joint before)
    (supported : result ∈ support ((interpret joint (RegistrationNativeIdentityMain.ordinary work)).run before)) :
    Inv joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityMainBeacon.poolProjection) supported
  rw [← support_map, RegistrationNativeIdentityMainOwned.ordinary_execution, support_map] at viewed
  obtain ⟨inner, _reached, same⟩ := viewed
  have retained : Inv joint ({ before.1 with context := inner.2 }, RegistrationNativeIdentityCompiler.poolView before.2) :=
    (projection_inv joint before).mpr prior
  have shifted := congrArg (fun output => Inv joint output.2) same
  have projected : Inv joint (RegistrationNativeIdentityMainBeacon.poolProjection result.2) := shifted ▸ retained
  exact (projection_inv joint result.2).mp projected

private theorem beacon_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeIdentityFrontend.M n KemSK RegistrationServerRoleBackend.State mlSource Value)
    (preserves : ∀ current env prior next,
      Holds setup.joint prior.identities current → ReservedEmpty prior.identities →
      next ∈ support ((simulateQ (RegistrationNativeIdentityWorld.implementation (mlSource := mlSource)
        setup checks representation created) ((work.run current).run env)).run prior) →
      Holds setup.joint next.2.identities next.1.1.2)
    (before : State n KemSK mlSource × SourceState) (result : Value × (State n KemSK mlSource × SourceState))
    (prior : Inv setup.joint before)
    (supported : result ∈ support
      ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created work)).run before)) :
    Inv setup.joint result.2 := by
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityMainBeacon.poolProjection) supported
  rw [← support_map, RegistrationNativeIdentityMainBeacon.beacon_execution, support_map] at viewed
  obtain ⟨inner, reached, same⟩ := viewed
  have initial := (projection_inv setup.joint before).mpr prior
  have held := preserves before.1.beacons (RegistrationWorldAgreementCompiler.erase before.1.context.server.world)
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ inner initial.1 initial.2 reached
  have reserved := RegistrationNativeIdentityHistoryReserved.world_program setup checks representation created _
    ⟨before.1.context, RegistrationNativeIdentityCompiler.poolView before.2⟩ inner initial.2 reached
  have retained : Inv setup.joint (RegistrationNativeIdentityMainBeacon.assemble inner).2 := ⟨held, reserved⟩
  rw [same] at retained
  exact (projection_inv setup.joint result.2).mp retained

/-- Actual complete opaque-identity creation establishes the new generated history and retains every older owner's history. -/
theorem create_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Nat) × (State n KemSK mlSource × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.create setup mlSource edPin mlPin keyId))).run before)) :
    Inv setup.joint result.2 := by
  apply beacon_inv setup checks representation created _ _ before result prior supported
  intro current env previous next holds reserved reached
  exact RegistrationNativeIdentityHistoryConstruction.create_holds setup checks representation created
    edPin mlPin keyId current env previous next holds reserved reached

/-- Whole outgoing execution retains every attempted indexed signature, including packing or final publication failure. -/
theorem bundle_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × (State n KemSK mlSource × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.bundle setup mlSource wire index))).run before)) :
    Inv setup.joint result.2 := by
  apply beacon_inv setup checks representation created _ _ before result prior supported
  intro current env previous next holds _reserved reached
  apply RegistrationNativeIdentityHistoryBundle.bundle_holds setup checks representation created wire index
    ((current, env), previous) (next.1.1.1, ((next.1.1.2, next.1.2), next.2)) holds
  simp only [RegistrationNativeIdentitySourceSimulation.runNew, support_map]
  exact Set.mem_image_of_mem _ reached

/-- Whole incoming finish retains the same signing history through terminal abort and consumed-kernel installation. -/
theorem finish_inv (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (before : State n KemSK mlSource × SourceState)
    (result : RustM (Option Pqxdh.Bytes) × (State n KemSK mlSource × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint (RegistrationNativeIdentityMain.beacon setup checks representation created
      (RegistrationNativeIdentityFrontend.finish setup mlSource wire index packet))).run before)) :
    Inv setup.joint result.2 := by
  apply beacon_inv setup checks representation created _ _ before result prior supported
  intro current env previous next holds _reserved reached
  apply RegistrationNativeIdentityHistoryFinish.finish_holds setup checks representation created wire index packet
    ((current, env), previous) (next.1.1.1, ((next.1.1.2, next.1.2), next.2)) holds
  simp only [RegistrationNativeIdentitySourceSimulation.runNew, support_map]
  exact Set.mem_image_of_mem _ reached

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.projection_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.projection_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.ordinary_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.ordinary_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.create_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.create_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.bundle_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.bundle_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.finish_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistory.finish_inv
