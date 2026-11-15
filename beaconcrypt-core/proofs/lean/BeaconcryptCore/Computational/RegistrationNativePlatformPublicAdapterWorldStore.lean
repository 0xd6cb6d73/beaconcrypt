-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeWorldMap
/-! A direct source World request updates the actual persistent source snapshot while preserving source objects. Local coordinate equalities suffice; no callback or program correspondence is a field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK R Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
variable (before : StrongCarrier (R:=R) setup view views created credential current)
variable (world : PqxdhRecordLiftWorld.State n) (next : Platform)
variable (sameServer : world.server=current.1.server.world.world.1.server)
variable (sameOwners : world.owners=current.1.server.world.world.1.owners)

def update : StrongCarrier (R:=R) setup view views created credential
    (AdapterPublicAgreementNativeWorldMap.putWorld current.1 world,next) where
  base:={
    objects:={before.base.objects with snapshot:=.direct (AdapterPublicAgreementNativeWorldMap.putWorld current.1 world,next)}
    server:={before.base.server with
      peers:=by
        change ∃ records, world.server=some records ∧ _
        rw [sameServer]
        exact before.base.server.peers}
    beacons:=by
      intro index
      have related:=before.base.beacons index
      change match current.1.beacons[index]? with
        | none=>before.base.objects.beacons index=none
        | some owner=>∃self,before.base.objects.beacons index=some self ∧
          AdapterPublicWrapperState.Beacon view setup.joint current.1.pool self owner world.owners[owner.worldOwner]?
      rw [sameOwners]
      exact related
    tokens:=before.base.tokens
    sessionCount:=before.base.sessionCount
    ownerCount:=before.base.ownerCount
    allocated:=by
      change world.owners.length=current.1.beacons.length
      rw [sameOwners]
      exact before.base.allocated
    indexed:=before.base.indexed
    backend:=rfl }
  otkPublic:=before.otkPublic

theorem objects : (update setup view views created credential current before world next sameServer sameOwners).base.objects=
    {before.base.objects with snapshot:=.direct (AdapterPublicAgreementNativeWorldMap.putWorld current.1 world,next)} := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore.update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore.update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterWorldStore.objects
