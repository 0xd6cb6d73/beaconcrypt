-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The source observation commit records only the invoked raw entry and actual writer frames. The returned source Beacon carries its updated kernel; the native owner finalizer is not copied into this source snapshot. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
open BeaconcryptCore.Refinement
variable [PublicWrapperPlatform.Material] [AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
structure Beacon (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) where
  returned : beaconcrypt_public_wrapper.beacon.Beacon
  raw : RegistrationNativeExperiment.State n KemSK source ×Platform
  owner : Nat
  frames : PqxdhRecordLiftLoggedAdapters.Frames
  rawBefore : Nat
  rawInvoked : Bool

def Beacon.rawAfter (snapshot : Beacon n KemSK Platform source) : Nat :=
  snapshot.rawBefore+if snapshot.rawInvoked then 1 else 0

def Beacon.world (snapshot : Beacon n KemSK Platform source) : PqxdhRecordLiftWorld.State n :=
  PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag snapshot.owner) snapshot.frames
    { snapshot.raw.1.server.world.world.1 with ownerRaw := Function.update snapshot.raw.1.server.world.world.1.ownerRaw snapshot.owner snapshot.rawAfter }

def Beacon.committed (snapshot : Beacon n KemSK Platform source) :
    RegistrationNativeExperiment.State n KemSK source ×Platform :=
  (RegistrationNativePlatformOrdinaryExperiment.replaceWorld snapshot.raw.1 snapshot.world,snapshot.raw.2)

def Beacon.registrationSnapshot (snapshot : Beacon n KemSK Platform source) :
    RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source :=
  .direct snapshot.committed

def packet {Reply : Type}
    (reached : RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.beacon.Beacon Reply
      (RegistrationNativeExperiment.State n KemSK source) Platform)
    (owner : Nat) (returned : beaconcrypt_public_wrapper.beacon.Beacon) : Beacon n KemSK Platform source :=
  ⟨returned,reached.after,owner,reached.frames,reached.rawBefore,reached.rawInvoked⟩

theorem Beacon.source_update (snapshot : Beacon n KemSK Platform source) :
    snapshot.registrationSnapshot.committed=snapshot.committed := rfl

theorem Beacon.record (snapshot : Beacon n KemSK Platform source) :
    snapshot.committed.1.server.world.world.1.ownerRaw snapshot.owner=snapshot.rawAfter ∧
    snapshot.committed.1.server.world.world.1.produced=snapshot.raw.1.server.world.world.1.produced++
      snapshot.frames.map (fun frame=>(PqxdhDeploymentNative.beaconTag snapshot.owner,frame)) := by
  constructor
  · exact Function.update_self _ _ _
  · rfl

theorem Beacon.physical (snapshot : Beacon n KemSK Platform source) :
    snapshot.committed.2=snapshot.raw.2 ∧
    snapshot.committed.1.pool=snapshot.raw.1.pool ∧
    snapshot.committed.1.beacons=snapshot.raw.1.beacons ∧
    snapshot.committed.1.server.world.auxiliary=snapshot.raw.1.server.world.auxiliary ∧
    snapshot.committed.1.server.world.world.1.primitive=snapshot.raw.1.server.world.world.1.primitive ∧
    snapshot.committed.1.server.world.world.1.server=snapshot.raw.1.server.world.world.1.server ∧
    snapshot.committed.1.server.world.world.1.seeds=snapshot.raw.1.server.world.world.1.seeds ∧
    snapshot.committed.1.server.world.world.1.used=snapshot.raw.1.server.world.world.1.used ∧
    snapshot.committed.1.server.world.world.1.owners=snapshot.raw.1.server.world.world.1.owners :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem Beacon.other_counter (snapshot : Beacon n KemSK Platform source) (other : Nat) (different : other≠snapshot.owner) :
    snapshot.committed.1.server.world.world.1.ownerRaw other=snapshot.raw.1.server.world.world.1.ownerRaw other :=
  Function.update_of_ne different _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.source_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.source_update

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.other_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.Beacon.other_counter
