-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicMaterialFrame
import BeaconcryptCore.Refinement.AdapterPublicBundleReached
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
/-! Untouched SDK Beacons retain their source material in the same publication receipt. Physical addresses come from actual indexed allocation; no public-key uniqueness is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem other_slot (target index : Nat) (different : index≠target)
    (before during : Native) (owner other : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (selected : before.beacons[target]?=some owner) (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (kept : during.server.world.world.1.owners=before.server.world.world.1.owners) :
    (RegistrationNativeBundleLifecycle.after target owner scalar publication during).server.world.world.1.owners[other.worldOwner]?=
      before.server.world.world.1.owners[other.worldOwner]? := by
  have address : owner.worldOwner≠other.worldOwner := by
    rw [indexed target owner selected,indexed index other otherSelected]
    exact Ne.symm different
  cases publication with
  | fail error | div => exact congrArg (fun owners =>owners[other.worldOwner]?) kept
  | ok result => cases result with
    | Err previous => exact congrArg (fun owners =>owners[other.worldOwner]?) kept
    | Ok finished =>
        change (during.server.world.world.1.owners.set owner.worldOwner (.inactive .initSent))[other.worldOwner]?=_
        rw [List.getElem?_set_ne address,kept]

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
def Retained (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (after : Native) (index : Nat) : Prop :=
  ∃current,after.beacons[index]?=some current ∧AdapterPublicWrapperState.Beacon view joint after.pool self current
    after.server.world.world.1.owners[current.worldOwner]?

theorem other_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (target index : Nat) (different : index≠target) (owner other : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (publication : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (before during : Native) (previous next : Platform)
    (selected : before.beacons[target]?=some owner) (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self other before.server.world.world.1.owners[other.worldOwner]?)
    (kept : RegistrationNativeBundleSafety.Snapshot during=RegistrationNativeBundleSafety.Snapshot before)
    (called : ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value publication),
        RegistrationNativeBundleLifecycle.after target owner scalar publication during),next)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer target).run before).run previous)) :
    ∃current,(RegistrationNativeBundleLifecycle.after target owner scalar publication during).beacons[index]?=some current ∧
      AdapterPublicWrapperState.Beacon view setup.joint (RegistrationNativeBundleLifecycle.after target owner scalar publication during).pool self current
        (RegistrationNativeBundleLifecycle.after target owner scalar publication during).server.world.world.1.owners[current.worldOwner]? := by
  let after := RegistrationNativeBundleLifecycle.after target owner scalar publication during
  have metadata := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer target before after previous next _ called
  have shape := RegistrationNativePlatformBundlePhases.native_shape coins setup checks representation created writer target before previous ((_,after),next) called
  obtain ⟨current,found,fields,phase⟩ := AdapterPublicMaterialFrame.other_owner target index different before.beacons after.beacons _ metadata shape other otherSelected
  refine ⟨current,found,?_⟩
  have physical : current.worldOwner=other.worldOwner := congrArg (fun value =>value.worldOwner) fields
  have pool : after.pool.keys=before.pool.keys := by
    have original : during.pool=before.pool := congrArg Prod.snd kept
    cases publication with
    | fail error | div => exact congrArg PqxdhLiveKemBirth.Pool.keys original
    | ok result => cases result <;> exact congrArg PqxdhLiveKemBirth.Pool.keys original
  apply AdapterPublicMaterialFrame.beacon view setup.joint before.pool after.pool self other current _ _ related pool fields phase
  rw [physical]
  exact other_slot target index different before during owner other scalar publication selected otherSelected indexed (congrArg Prod.fst kept)

theorem with_coins (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (target index : Nat) (different : index≠target) (owner other : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (before : Native) (previous : Platform)
    (selected : before.beacons[target]?=some owner) (phase : owner.phase=.freshWithCoins scalar)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner)
    (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self other before.server.world.world.1.owners[other.worldOwner]?)
    (result : (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8)) ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer target owner scalar).run before).run previous)) :
    Retained view setup.joint self (RegistrationNativeBundleLifecycle.after target owner scalar result.1.1 result.1.2) index := by
  have kept := RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup target owner scalar) before previous result reached
  have called : ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1),
      RegistrationNativeBundleLifecycle.after target owner scalar result.1.1 result.1.2),result.2)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer target).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.with_coins coins setup checks representation created writer target owner scalar before previous selected phase ready,support_map]
    exact ⟨result,reached,rfl⟩
  exact other_material coins setup checks representation created writer view target index different owner other scalar result.1.1 self before result.1.2 previous result.2
    selected otherSelected indexed related kept called

theorem fresh (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (target index : Nat) (different : index≠target) (owner other : Owner source)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (before : Native) (previous : Platform)
    (selected : before.beacons[target]?=some owner) (phase : owner.phase=.fresh)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner)
    (otherSelected : before.beacons[index]?=some other)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self other before.server.world.world.1.owners[other.worldOwner]?)
    (result : ((PqxdhJointGapDh.ScalarBytes ×RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) ×Native) ×Platform)
    (reached : result∈support (((RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer target owner).run before).run previous)) :
    Retained view setup.joint self (RegistrationNativeBundleLifecycle.after target owner result.1.1.1 result.1.1.2 result.1.2) index := by
  have kept := AdapterPublicBundleReached.fresh_snapshot coins setup checks representation created writer target owner before previous result reached
  have called : ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1.2),
      RegistrationNativeBundleLifecycle.after target owner result.1.1.1 result.1.1.2 result.1.2),result.2)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer target).run before).run previous) := by
    rw [RegistrationNativeBundleLifetime.fresh coins setup checks representation created writer target owner before previous selected phase ready,support_map]
    exact ⟨result,reached,rfl⟩
  exact other_material coins setup checks representation created writer view target index different owner other result.1.1.1 result.1.1.2 self before result.1.2 previous result.2
    selected otherSelected indexed related kept called

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.other_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.other_material
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.with_coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame.fresh
