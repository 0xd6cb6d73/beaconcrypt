-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryServerReifier
/-! The actual source Server object reifies exactly the Server row already retained in the same physical backend. This includes the reached raw-attempt count and derives from the full Carrier material relation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored
open BeaconcryptCore.Refinement
variable {n : Nat} {KemSK R P : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
theorem stored (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source×P)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current) :
    some (AdapterPublicOrdinaryServerReifier.server view views before.objects.server
      ((((RegistrationNativePlatformPublicAdapterStore.erase before.objects).backend.1.world.server).map
        (fun records=>records.records.rawAttempts)).getD 0))=
      (RegistrationNativePlatformPublicAdapterStore.erase before.objects).backend.1.world.server := by
  have retained:=RegistrationNativePlatformPublicAdapterStore.retained view views joint created credential current before
  obtain ⟨records,found,related⟩:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  have row : (RegistrationNativePlatformPublicAdapterStore.erase before.objects).backend.1.world.server=some records := by
    rw [retained]
    exact found
  rw [row,Option.map_some,Option.getD_some,related]

theorem replace (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source×P)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current) :
    let world:=(RegistrationNativePlatformPublicAdapterStore.erase before.objects).backend.1.world
    {world with server:=some (AdapterPublicOrdinaryServerReifier.server view views before.objects.server
      ((world.server.map (fun records=>records.records.rawAttempts)).getD 0))}=world := by
  dsimp only
  rw [stored view views joint created credential current before]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored.stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored.stored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored.replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerStored.replace
