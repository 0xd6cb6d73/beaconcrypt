-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects)
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

def snapshot (current : Native×Platform) (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) (invoked : Bool) :
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon n KemSK Platform source :=
  ⟨self,current,worldOwner,[],current.1.server.world.world.1.ownerRaw worldOwner,invoked⟩

omit platform in
theorem snapshot_false (current : Native×Platform) (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) :
    (snapshot current self worldOwner false).committed=current := by
  simp only [snapshot,RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.committed,
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.world,
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.rawAfter,Bool.false_eq_true,ite_false,Nat.add_zero,
    Function.update_eq_self,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
  rfl

omit platform in
theorem snapshot_true (current : Native×Platform) (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) :
    (snapshot current self worldOwner true).committed=
      (RegistrationNativePlatformOrdinaryExperiment.replaceWorld current.1 {current.1.server.world.world.1 with
        ownerRaw:=Function.update current.1.server.world.world.1.ownerRaw worldOwner (current.1.server.world.world.1.ownerRaw worldOwner+1)},current.2) := by
  simp only [snapshot,RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.committed,
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.world,
    RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.rawAfter,ite_true,
    PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]

noncomputable def put (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (current : Native×Platform)
    (before : Carrier (R:=R) view views joint created credential current)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) (invoked : Bool) :
    Carrier (R:=R) view views joint created credential (snapshot current self worldOwner invoked).committed := by
  refine {objects:={before.objects with snapshot:=.direct (snapshot current self worldOwner invoked).committed}
          server:={identity:=before.server.identity, control:=before.server.control, pinIdentity:=before.server.pinIdentity, pinIdentifier:=before.server.pinIdentifier, pinMldsa:=before.server.pinMldsa, replay:=before.server.replay, peers:=before.server.peers}
          beacons:=before.beacons
          tokens:=before.tokens
          sessionCount:=before.sessionCount
          ownerCount:=before.ownerCount
          allocated:=before.allocated
          indexed:=before.indexed
          backend:=rfl}

noncomputable def strong (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) (invoked : Bool) :
    StrongCarrier (R:=R) setup view views created credential (snapshot current self worldOwner invoked).committed :=
  ⟨put view views setup.joint created credential current before.base self worldOwner invoked,before.otkPublic⟩

theorem strong_objects (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (worldOwner : Nat) (invoked : Bool) :
    (strong setup view views created credential current before self worldOwner invoked).base.objects=
      {before.base.objects with snapshot:=.direct (snapshot current self worldOwner invoked).committed} := rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.strong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.strong

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.strong_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.strong_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_false

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconRetain.snapshot_true
