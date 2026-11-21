-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
/-! Attaching the retained one-time-key invariant and converting the public reply preserve the same actual source objects and raw physical call. No new source sampling, state update or callback law is introduced. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongPhysical
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw basePhysical strongPhysical)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK P R Reply PublicReply : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)

theorem map_of_base {model : ProbComp (Reply×(RegistrationNativeExperiment.State n KemSK mlSource×P))}
    (call : TotalStep (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet,RegistrationNativePlatformSdkStrongCarrier.OtkPublic
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
      (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons)
    (observe : Reply → PublicReply) :
    raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map observe
        (RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call coherent))=
    raw (basePhysical view views setup.joint created credential)
      (RegistrationNativePlatformPublicAdapterReply.map observe call) :=by
  unfold raw
  congr 1
  funext packet
  simp only [strongPhysical,basePhysical,RegistrationNativePlatformPublicAdapterReply.store,
    RegistrationNativePlatformSdkStrongStep.of_base_base]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongPhysical.map_of_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongPhysical.map_of_base
