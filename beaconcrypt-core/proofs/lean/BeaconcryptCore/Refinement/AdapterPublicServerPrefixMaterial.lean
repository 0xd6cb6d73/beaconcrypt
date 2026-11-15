-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationFrame
import BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal
import BeaconcryptCore.Refinement.AdapterPublicServerLookupNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual pin/authentication effects retain source Server material before the enclosing lookup. Agreement receipt restoration overwrites only its own reached World, so preceding real hash effects can be retained in the same source/native projection without resetting any request journal, role state, owner or private KEM pool. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial
open BeaconcryptCore.Computational
open AdapterPublicAgreementNativeWorldMap (putWorld)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R : Type} {mlSource : RegistrationNativeMldsa.Source}

omit platform in
theorem restore_world (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before current : RegistrationNativeExperiment.State n KemSK mlSource) (world : PqxdhRecordLiftWorld.State n)
    (receipt : AdapterPublicServerAgreementReceipt.Receipt R) :
    AdapterPublicAgreementNativeWorldInterpreter.restore view (putWorld before world) (receipt, current) =
      AdapterPublicAgreementNativeWorldInterpreter.restore view before (receipt, current) := by
  cases receipt with
  | fail error | div => rfl
  | ok pair => rcases pair with ⟨⟨effect, journal⟩, capture⟩; rfl

theorem project_world (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) (world : PqxdhRecordLiftWorld.State n)
    (result : (AdapterPublicServerReservationReceipt.Receipt R × RustM (AdapterPublicServerAgreementReceipt.Word R)) ×
      RegistrationNativeExperiment.State n KemSK mlSource) :
    AdapterPublicServerReservationNative.project view (putWorld before world) result =
      AdapterPublicServerReservationNative.project view before result := by
  unfold AdapterPublicServerReservationNative.project
  cases result.1.1 with
  | none => rfl
  | some receipt =>
    unfold AdapterPublicServerAgreementRetention.project
    simp only [restore_world]

theorem related_world (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (world : PqxdhRecordLiftWorld.State n)
    (unchanged : world.server = before.server.world.world.1.server) :
    AdapterPublicWrapperState.Server view views created credential self (putWorld before world).server := by
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa,
    related.replay, records, unchanged.trans reached, sender, identity, peers⟩

omit material platform ed in
theorem pin_server (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before after : PqxdhRecordLiftWorld.State n)
    (reply : RegistrationNativeServerPinRecompute.PinReply)
    (supported : (reply, after) ∈ support ((RegistrationNativeServerPinRecompute.native binding publicKey).run before)) :
    after.server = before.server := by
  rw [RegistrationNativeServerPinRecompute.native_run] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

end BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.restore_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.restore_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.project_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.project_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.related_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.related_world

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.pin_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixMaterial.pin_server
