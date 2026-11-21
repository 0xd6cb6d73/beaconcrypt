-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMaterial
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryBeacon
open CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial
open BeaconcryptCore.Refinement
variable {KemSK : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

theorem inactive (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (idle : AdapterPublicOrdinaryBeacon.Inactive self) :
    ∃tag,world=some (.inactive tag) := by
  have facts:=related.phase
  cases stored:self.state <;> cases phase:owner.phase <;>
    simp only [AdapterPublicWrapperState.Phase,stored,phase] at facts
  all_goals first
    | exact ⟨_,facts.2.2.2⟩
    | exact ⟨_,facts.2.2.2.2⟩
    | exact ⟨_,facts.2⟩
    | simp only [AdapterPublicOrdinaryBeacon.Inactive,stored] at idle
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive
