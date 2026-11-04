-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryBeacon
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMaterial
open BeaconcryptCore.Refinement
variable {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

theorem established (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (manager : beaconcrypt_public_wrapper.ratchet.RatchetManager)
    (stored : self.state=.Established control binding manager) :
    ∃kernel completed,manager=AdapterPublicOrdinaryEnvelope.manager kernel ∧owner.phase=.established completed ∧
      world=some (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel) := by
  have facts:=related.phase
  cases phase:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phase] at facts
  case established completed=>
    obtain ⟨kernel,kernelStored,worldStored⟩:=facts.2.2
    have managerEq : manager=AdapterPublicOrdinaryEnvelope.manager kernel := by
      cases manager with
      | mk refined=>cases refined with
        | mk current=>cases kernelStored;rfl
    have identifier:=related.identifier
    simp only [AdapterPublicWrapperState.currentId,phase] at identifier
    rw [←facts.2.1] at identifier
    rw [←identifier] at worldStored
    exact ⟨kernel,completed,managerEq,rfl,worldStored⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established
