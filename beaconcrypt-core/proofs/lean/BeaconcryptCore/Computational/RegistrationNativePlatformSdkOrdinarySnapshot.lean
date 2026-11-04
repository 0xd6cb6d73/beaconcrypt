-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! An ordinary returned Server snapshot retains its actual raw source poststate and writer-attempt journal. Its deterministic commit reconstructs peers from that returned source object, charges only the invoked raw entry and appends the actual source frames. Primitive/cache/platform state is never copied from a model finalizer. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot
open BeaconcryptCore.Refinement
variable {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

structure Server (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) where
  returned : beaconcrypt_public_wrapper.server.Server
  raw : RegistrationNativeExperiment.State n KemSK source ×Platform
  tag : PqxdhDeploymentInterface.FrameTag
  frames : PqxdhRecordLiftLoggedAdapters.Frames
  rawBefore : Nat
  rawInvoked : Bool

def Server.rawAfter (snapshot : Server n KemSK Platform source) : Nat :=
  snapshot.rawBefore+if snapshot.rawInvoked then 1 else 0

def Server.world (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) : PqxdhRecordLiftWorld.State n :=
  PqxdhRecordLiftWorld.produce snapshot.tag snapshot.frames
    { snapshot.raw.1.server.world.world.1 with server := some (AdapterPublicOrdinaryServerReifier.server view views snapshot.returned snapshot.rawAfter) }

def Server.committed (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    RegistrationNativeExperiment.State n KemSK source ×Platform :=
  ({ snapshot.raw.1 with server :=
      { snapshot.raw.1.server with world :=
        { snapshot.raw.1.server.world with world :=
          (snapshot.world view views,snapshot.raw.1.server.world.world.2) } } },snapshot.raw.2)

/-- This is the private deterministic source update used after the actual successful SDK return. -/
def Server.registrationSnapshot (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source :=
  .direct (snapshot.committed view views)

theorem Server.source_update (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    (snapshot.registrationSnapshot view views).committed=snapshot.committed view views := rfl

theorem Server.record (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    (snapshot.committed view views).1.server.world.world.1.server=some
      (AdapterPublicOrdinaryServerReifier.server view views snapshot.returned snapshot.rawAfter) ∧
    (snapshot.committed view views).1.server.world.world.1.produced=
      snapshot.raw.1.server.world.world.1.produced++snapshot.frames.map (fun frame=>(snapshot.tag,frame)) := ⟨rfl,rfl⟩

theorem Server.physical (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    (snapshot.committed view views).2=snapshot.raw.2 ∧
    (snapshot.committed view views).1.pool=snapshot.raw.1.pool ∧
    (snapshot.committed view views).1.beacons=snapshot.raw.1.beacons ∧
    (snapshot.committed view views).1.server.world.auxiliary=snapshot.raw.1.server.world.auxiliary ∧
    (snapshot.committed view views).1.server.world.world.1.primitive=snapshot.raw.1.server.world.world.1.primitive ∧
    (snapshot.committed view views).1.server.world.world.1.seeds=snapshot.raw.1.server.world.world.1.seeds ∧
    (snapshot.committed view views).1.server.world.world.1.used=snapshot.raw.1.server.world.world.1.used ∧
    (snapshot.committed view views).1.server.world.world.1.ownerRaw=snapshot.raw.1.server.world.world.1.ownerRaw ∧
    (snapshot.committed view views).1.server.world.world.1.owners=snapshot.raw.1.server.world.world.1.owners :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem Server.counter (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (snapshot : Server n KemSK Platform source) :
    ((snapshot.committed view views).1.server.world.world.1.server.map fun record=>record.records.rawAttempts)=
      some (snapshot.rawBefore+if snapshot.rawInvoked then 1 else 0) := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.source_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.source_update

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot.Server.counter
