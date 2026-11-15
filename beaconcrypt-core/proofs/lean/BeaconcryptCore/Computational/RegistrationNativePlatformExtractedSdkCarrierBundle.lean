-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBundleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects SourceSnapshot TokenTable BeaconTable)
variable {n : Nat} {I KemSK Platform E R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]

omit material platform ed in
private theorem absent (before after : Native)
    (same : after.beacons.map RegistrationNativeOwnerFields.metadata=before.beacons.map RegistrationNativeOwnerFields.metadata)
    (index : Nat) (missing : before.beacons[index]?=none) : after.beacons[index]?=none := by
  have equality:=congrArg (fun owners=>owners[index]?) same
  rw [List.getElem?_map,List.getElem?_map,missing] at equality
  cases found:after.beacons[index]? with
  | none=>rfl
  | some owner=>rw [found] at equality; cases equality

omit material platform ed in
private theorem indexed (before after : Native)
    (same : after.beacons.map RegistrationNativeOwnerFields.metadata=before.beacons.map RegistrationNativeOwnerFields.metadata)
    (initial : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons) :
    RegistrationNativeHiddenAllocationOwners.NativeIndexed after.beacons := by
  intro index owner found
  have old : (before.beacons.map RegistrationNativeOwnerFields.metadata)[index]?=some (RegistrationNativeOwnerFields.metadata owner) := by
    rw [←same,List.getElem?_map,found]
    rfl
  rw [List.getElem?_map] at old
  obtain ⟨previous,selected,fields⟩ := Option.map_eq_some_iff.mp old
  exact (congrArg RegistrationNativeBeaconFrontend.Owner.worldOwner fields).symm.trans (initial index previous selected)

omit material platform ed in
private theorem after_length (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (publication : RegistrationNativePlatformExtractedSdkBundle.Publication)
    (during : Native) :
    (RegistrationNativeBundleLifecycle.after index owner scalar publication during).server.world.world.1.owners.length=
      during.server.world.world.1.owners.length := by
  cases publication with
  | fail error | div=>rfl
  | ok value=>cases value with
    | Err previous=>rfl
    | Ok finished=>
        change (during.server.world.world.1.owners.set owner.worldOwner (.inactive .initSent)).length=_
        exact List.length_set

omit platform in
private theorem active (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (rng : R) (publication : RegistrationNativePlatformExtractedSdkBundle.Publication)
    (during : Native) (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (actual : AdapterPublicBundlePublication.install self prekey oneTime kem rng publication=.ok returned)
    (related : AdapterPublicBundleReached.MaterialResult view joint index self owner prekey oneTime kem scalar publication during) :
    RegistrationNativePlatformSdkBundleFrame.Retained view joint returned.2.1
      (RegistrationNativeBundleLifecycle.after index owner scalar publication during) index := by
  cases publication with
  | fail error | div=>cases actual
  | ok value=>cases value with
    | Err previous=>cases actual; exact related
    | Ok finished=>cases actual; exact related

variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (containers : AdapterPublicWrapperStorage.Views)
variable (credential : RegistrationNativeMldsa.Credential source)


def update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R) (index : Nat)
    (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (sourceAfter : Native ×Platform) : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R :=
  {before with beacons:=Function.update before.beacons index (some returned.2.1),rng:=returned.2.2,snapshot:=.direct sourceAfter}

noncomputable def put (current : Native ×Platform) (before : Carrier (R:=R) view containers setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (_sourceSelected : before.objects.beacons index=some self)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (rng : R) (publication : RegistrationNativePlatformExtractedSdkBundle.Publication)
    (during : Native) (next : Platform)
    (kept : RegistrationNativeBundleSafety.Snapshot during=RegistrationNativeBundleSafety.Snapshot current.1)
    (serverKept : RegistrationNativePlatformSdkServerFrame.image during=RegistrationNativePlatformSdkServerFrame.image current.1)
    (called : ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value publication),
      RegistrationNativeBundleLifecycle.after index owner scalar publication during),next)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run current.1).run current.2))
    (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (actual : AdapterPublicBundlePublication.install self prekey oneTime kem rng publication=.ok returned)
    (related : AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey oneTime kem scalar publication during) :
    Carrier (R:=R) view containers setup.joint created credential
      (RegistrationNativeBundleLifecycle.after index owner scalar publication during,next) := by
  let final:=RegistrationNativeBundleLifecycle.after index owner scalar publication during
  have fields:=RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer index
    current.1 final current.2 next _ called
  have fullImage : RegistrationNativePlatformSdkServerFrame.image final=RegistrationNativePlatformSdkServerFrame.image current.1 :=
    (RegistrationNativePlatformSdkServerFrame.bundle_after index owner scalar publication during).trans serverKept
  have sessions : final.server.sessions=current.1.server.sessions:=congrArg RegistrationNativePlatformSdkServerFrame.ServerImage.sessions fullImage
  have beaconCount:final.beacons.length=current.1.beacons.length := by simpa only [List.length_map] using congrArg List.length fields
  have activeMaterial:=active view setup.joint index owner self prekey oneTime kem scalar rng publication during returned actual related
  refine {
    objects:={before.objects with beacons:=Function.update before.objects.beacons index (some returned.2.1),rng:=returned.2.2,snapshot:=.direct (during,next)}
    server:=RegistrationNativePlatformSdkServerFrame.server_material (created:=created) view containers credential before.objects.server current.1 final before.server fullImage
    beacons:=?_
    tokens:=by
      change TokenTable before.objects.tokens final.server.sessions
      rw [sessions]
      exact before.tokens
    sessionCount:=by
      change before.objects.nextSession=final.server.sessions.length
      rw [sessions]
      exact before.sessionCount
    ownerCount:=before.ownerCount.trans beaconCount.symm
    allocated:=?_
    indexed:=indexed current.1 final fields before.indexed
    backend:=?_ }
  · intro otherIndex
    by_cases same:otherIndex=index
    · subst otherIndex
      obtain ⟨updated,found,material⟩ := activeMaterial
      rw [found]
      exact ⟨returned.2.1,Function.update_self _ _ _,material⟩
    · cases prior:current.1.beacons[otherIndex]? with
      | none=>
          have missing:=absent current.1 final fields otherIndex prior
          rw [missing]
          simpa only [Function.update_of_ne same,prior] using before.beacons otherIndex
      | some other=>
          have old:=before.beacons otherIndex
          simp only [prior] at old
          obtain ⟨oldSelf,oldStored,oldMaterial⟩ := old
          obtain ⟨updated,found,material⟩ := RegistrationNativePlatformSdkBundleFrame.other_material coins setup checks representation created writer view
            index otherIndex same owner other scalar publication oldSelf current.1 during current.2 next selected prior before.indexed oldMaterial kept called
          rw [found]
          exact ⟨oldSelf,(Function.update_of_ne same _ _).trans oldStored,material⟩
  · have count:=congrArg List.length fields
    simp only [List.length_map] at count
    have ownersLength:during.server.world.world.1.owners.length=current.1.server.world.world.1.owners.length := congrArg (fun value=>value.1.length) kept
    rw [after_length,ownersLength,before.allocated]
    exact count.symm
  · exact RegistrationNativePlatformExtractedSdkCarrier.bundle_snapshot index owner scalar ((publication,during),next)
theorem put_objects (current : Native ×Platform) (before : Carrier (R:=R) view containers setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (_sourceSelected : before.objects.beacons index=some self)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes) (rng : R) (publication : RegistrationNativePlatformExtractedSdkBundle.Publication)
    (during : Native) (next : Platform)
    (kept : RegistrationNativeBundleSafety.Snapshot during=RegistrationNativeBundleSafety.Snapshot current.1)
    (serverKept : RegistrationNativePlatformSdkServerFrame.image during=RegistrationNativePlatformSdkServerFrame.image current.1)
    (called : ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value publication),
      RegistrationNativeBundleLifecycle.after index owner scalar publication during),next)∈support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run current.1).run current.2))
    (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (actual : AdapterPublicBundlePublication.install self prekey oneTime kem rng publication=.ok returned)
    (related : AdapterPublicBundleReached.MaterialResult view setup.joint index self owner prekey oneTime kem scalar publication during) :
    (put coins setup checks representation created writer view containers credential current before index owner selected self _sourceSelected
      prekey oneTime kem scalar rng publication during next kept serverKept called returned actual related).objects=
      update before.objects index returned (during,next) := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle.put_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle.put_objects
