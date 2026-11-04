-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkStrongCarrier
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
private theorem cast_cancel {A B : Type} (same : A=B) (value : B) : same.mp (same.mpr value)=value := by
  cases same
  rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Platform R Reply : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def of_base {model : ProbComp (Reply×(RegistrationNativeExperiment.State n KemSK source×Platform))} (call : TotalStep (RegistrationNativePlatformExtractedSdkCarrier.Carrier (n:=n) (Platform:=Platform) (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet : {value //value∈support call.step.sample},
      OtkPublic (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
        (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons) : TotalStep (StrongCarrier (n:=n) (Platform:=Platform) (R:=R) setup view views created credential) model := {
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=call.step.sourceState
    sourceCall:=call.step.sourceCall
    source_exact:=call.step.source_exact
    native:=call.step.native
    native_exact:=call.step.native_exact
    store:=fun packet supported=>by
      have marked : call.step.sourceReply packet=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨packet,supported⟩) :=
        RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨packet,supported⟩
      rw [marked]
      exact ⟨RegistrationNativePlatformExtractedSdkPublic.store call ⟨packet,supported⟩,coherent ⟨packet,supported⟩⟩ }
  observe:=call.observe
  normal:=call.normal
  reply:=call.reply }

theorem of_base_base {model : ProbComp (Reply×(RegistrationNativeExperiment.State n KemSK source×Platform))} (call : TotalStep (RegistrationNativePlatformExtractedSdkCarrier.Carrier (n:=n) (Platform:=Platform) (R:=R) view views setup.joint created credential) model)
    (coherent : ∀packet : {value //value∈support call.step.sample},
      OtkPublic (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
        (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects.beacons)
    (packet : {value //value∈support call.step.sample}) :
    (RegistrationNativePlatformExtractedSdkPublic.store (of_base setup view views created credential call coherent) packet).base=
      RegistrationNativePlatformExtractedSdkPublic.store call packet := by
  simp only [RegistrationNativePlatformExtractedSdkPublic.store,of_base,cast_cancel]
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep.of_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep.of_base

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep.of_base_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep.of_base_base
