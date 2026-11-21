-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
/-! The same supported source packet yields the same returned public reply and source objects after erasing the passive indexed KEM log. This algebraic identity composes existing concrete query laws with the actual method's proved quotient frame. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterStore (Store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R P N Reply : Type} {Private : N → Type} {model : ProbComp (Reply×N)}

theorem raw (physical : ∀current,Private current → Store n KemSK R P)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private model) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (fun current before=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (physical current before)) call=
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call :=by
  unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  calc
    _=(fun packet=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize
      (RustM.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call packet),
        physical (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)),
        (physical (call.step.native packet.val).2 (RegistrationNativePlatformExtractedSdkPublic.store call packet)).backend)) <$>
      PFunctor.FreeM.attachSupp call.step.sample :=by
      rfl
    _=_:=(Functor.map_map _ _ _).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw.raw
