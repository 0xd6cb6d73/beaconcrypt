-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicMaterialFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeKemPoolFrame
import BeaconcryptCore.Computational.RegistrationNativeKemResourceFootprint
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
/-! Actual Finish preserves every untouched SDK Beacon from the same raw receipt. Private-pool preservation follows from the concrete no-birth bill; other slots follow from actual indexed allocation and the source raw-body frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem counted_create :
    RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create=
      RegistrationNativeKemResourceFootprint.counted .birth := by
  funext query
  cases query with
  | inl effect => rfl
  | inr query => cases query with
    | inl other => simp [RegistrationNativeKemBeaconFootprint.counted,RegistrationNativeKemResourceFootprint.counted]
    | inr request => cases request with
      | inl request => cases request <;> simp [RegistrationNativeKemBeaconFootprint.counted,RegistrationNativeKemResourceFootprint.counted]
      | inr request => simp [RegistrationNativeKemBeaconFootprint.counted,RegistrationNativeKemResourceFootprint.counted]

theorem pool_keys (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (target : Nat) (packet : Option registration.ResponsePacket)
    (before : Native) (result : RustM (Option Pqxdh.Bytes) ×Native)
    (reached : result∈support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire target packet)).run before)) :
    result.2.pool.keys=before.pool.keys := by
  apply RegistrationNativeKemPoolFrame.beacon_keys setup checks representation created _ _ before result reached
  intro owners environment
  exact (isQueryBoundP_congr_pred
    (p := RegistrationNativeKemBeaconFootprint.counted .create)
    (p' := RegistrationNativeKemResourceFootprint.counted .birth)
    (fun query => Iff.of_eq (congrFun counted_create query))).mpr
      (RegistrationNativeKemResourceFootprint.finish_zero setup .birth (by decide) wire target packet owners environment)

private theorem setPhase_other (target index : Nat) (different : index≠target) (phase : RegistrationNativeBeaconFrontend.Phase)
    (owners : List (Owner source)) (owner other : Owner source)
    (selected : owners[target]?=some owner) (otherSelected : owners[index]?=some other) :
    (RegistrationNativeFinishTerminal.setPhase target phase owners)[index]?=some other := by
  simp only [RegistrationNativeFinishTerminal.setPhase,selected,List.getElem?_set_ne (Ne.symm different)]
  exact otherSelected

variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

theorem other_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (wire : RegistrationNativeWire.Wire) (target index : Nat) (different : index≠target)
    (owner other : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (self : beaconcrypt_public_wrapper.beacon.Beacon) (before : Native)
    (selected : before.beacons[target]?=some owner) (phase : owner.phase=.initSent pending scalar)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner)
    (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self other before.server.world.world.1.owners[other.worldOwner]?)
    (result : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source)
    (reached : result∈support (RegistrationNativeFinishLifetime.tree setup checks representation created wire pending packet owner scalar before)) :
    let after := RegistrationNativePlatformExtractedSdkFinish.nativeProjection target owner pending before.beacons result
    after.2.beacons[index]?=some other ∧AdapterPublicWrapperState.Beacon view setup.joint after.2.pool self other
      after.2.server.world.world.1.owners[other.worldOwner]? := by
  let after := (RegistrationNativePlatformExtractedSdkFinish.nativeProjection target owner pending before.beacons result).2
  have called : (RegistrationNativeFinishTerminalTree.bytes result.1.1,after)∈support
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire target packet)).run before) := by
    rw [RegistrationNativeFinishLifetime.complete setup checks representation created wire target owner pending scalar packet before selected phase ready,support_map]
    exact ⟨result,reached,rfl⟩
  have keys := pool_keys setup checks representation created wire target packet before (_,after) called
  have worlds := RegistrationNativeFinishBodySafety.raw_owners setup checks representation created wire pending
    (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) before result reached
  have address : owner.worldOwner≠other.worldOwner := by
    rw [indexed target owner selected,indexed index other otherSelected]
    exact Ne.symm different
  have found : after.beacons[index]?=some other := by
    dsimp only [after,RegistrationNativePlatformExtractedSdkFinish.nativeProjection]
    cases reply : result.1.1 with
    | fail error | div => exact setPhase_other target index different _ before.beacons owner other selected otherSelected
    | ok optional => cases optional <;> exact setPhase_other target index different _ before.beacons owner other selected otherSelected
  refine ⟨found,?_⟩
  have slot : after.server.world.world.1.owners[other.worldOwner]?=before.server.world.world.1.owners[other.worldOwner]? := by
    dsimp only [after,RegistrationNativePlatformExtractedSdkFinish.nativeProjection]
    cases reply : result.1.1 with
    | fail error | div =>
        change (result.2.server.world.world.1.owners.set owner.worldOwner (.inactive .aborted))[other.worldOwner]?=_
        rw [List.getElem?_set_ne address,worlds]
    | ok optional => cases optional with
      | none =>
          change (result.2.server.world.world.1.owners.set owner.worldOwner (.inactive .aborted))[other.worldOwner]?=_
          rw [List.getElem?_set_ne address,worlds]
      | some completed =>
          change (result.2.server.world.world.1.owners.set owner.worldOwner
            (.established ⟨completed.binding.assigned_key_id,completed.control,completed.binding.associated_data⟩ completed.kernel))[other.worldOwner]?=_
          rw [List.getElem?_set_ne address,worlds]
  rw [slot]
  exact AdapterPublicMaterialFrame.pool view setup.joint before.pool after.pool self other _ related keys

theorem other_platform (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (wire : RegistrationNativeWire.Wire) (target index : Nat) (different : index≠target)
    (owner other : Owner source) (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) (self : beaconcrypt_public_wrapper.beacon.Beacon) (before : Native)
    (selected : before.beacons[target]?=some owner) (phase : owner.phase=.initSent pending scalar)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner)
    (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self other before.server.world.world.1.owners[other.worldOwner]?)
    (previous : Platform) (result : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source ×Platform)
    (reached : result∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar before).run previous)) :
    let after := RegistrationNativePlatformExtractedSdkFinish.nativeProjection target owner pending before.beacons result.1
    after.2.beacons[index]?=some other ∧AdapterPublicWrapperState.Beacon view setup.joint after.2.pool self other
      after.2.server.world.world.1.owners[other.worldOwner]? := by
  exact other_material setup checks representation created view wire target index different owner other pending scalar packet self before
    selected phase ready otherSelected indexed related result.1
    (RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 reached)

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.pool_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.pool_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.other_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.other_material
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.other_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame.other_platform
