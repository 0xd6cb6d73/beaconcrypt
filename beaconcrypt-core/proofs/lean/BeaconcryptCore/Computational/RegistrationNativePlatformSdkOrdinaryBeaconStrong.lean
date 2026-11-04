-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrong
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier update_public)
open RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun (Sample)
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

noncomputable def put (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native ×Platform) (before : StrongCarrier (R:=R) setup view containers created credential current)
    (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (selected : current.1.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.base.objects.beacons logical=some self)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (initial final : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager initial))
    (completed : RegistrationBeaconSeed.PublicCompleted) (phase : owner.phase=.established completed)
    (reply : Option beaconcrypt_record_send.shared.Encrypted) (reached : Sample Platform) (normal : reached.1.1=.ok (final,reply)) :
    StrongCarrier (R:=R) setup view containers created credential
      (RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.next current.1 owner.worldOwner self control binding final reached) := by
  refine ⟨RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put view containers setup.joint created credential current before.base logical owner selected self sourceSelected
    control binding initial final stored completed phase reply reached normal,?_⟩
  rw [RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.put_objects]
  apply update_public view _ before.base.objects.beacons before.otkPublic logical
    (RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon.returned self control binding final)
  intro fresh prekey oneTime kem impossible
  change beaconcrypt_public_wrapper.beacon.BeaconState.Established control binding (AdapterPublicOrdinaryEnvelope.manager final)=.FreshWithCoins fresh prekey oneTime kem at impossible
  cases impossible

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrong
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrong.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconStrong.put
