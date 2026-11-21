-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
/-! A normal native projection of a given SDK receipt forces that same source RustM word to be normal. No material object is fabricated on failure, and no alternate supported execution is selected. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection
open BeaconcryptCore.Refinement
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

theorem accept (view : AdapterPublicWrapperState.MaterialView source KemSK) (before after : Native)
    (receipt : Option (AdapterPublicServerAgreementReceipt.Receipt R))
    (word : RustM (AdapterPublicServerAgreementReceipt.Word R))
    (handle : Option Nat) (reached : Native)
    (normal : AdapterPublicServerReservationNative.project view before ((receipt,word),after)= .ok (.ok handle, reached)) :
    ∃value,word = .ok value := by
  cases word with
  | ok value => exact ⟨value,rfl⟩
  | fail error | div =>
    cases receipt with
    | none => simp [AdapterPublicServerReservationNative.project] at normal
    | some receipt =>
      unfold AdapterPublicServerReservationNative.project AdapterPublicServerAgreementRetention.project at normal
      cases restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before (receipt,after) with
      | fail error | div => simp only [restored, bind_tc_fail, bind_tc_div, reduceCtorEq] at normal
      | ok pair =>
        rcases pair with ⟨effect,current⟩
        simp only [restored, bind_tc_ok] at normal
        cases effect with
        | fail error | div => simp [AdapterPublicServerAgreementRetention.projectEffect] at normal
        | ok effect => cases effect <;>
            simp [AdapterPublicServerAgreementRetention.projectEffect, AdapterPublicServerRetainNative.project] at normal

theorem build (control : pqxdh.ServerState) (publication : Option AdapterPublicServerBuildTrace.Publication)
    (word : RustM AdapterPublicServerBuildBody.Reply)
    (after : RegistrationNativePlatformCutJournal.State Native)
    (reply : Option (U64 ×alloc.vec.Vec U8))
    (normal : (AdapterPublicServerBuildPrefix.project control ((publication,word),after)).1= .ok reply) :
    ∃value,word = .ok value := by
  cases word with
  | ok value => exact ⟨value,rfl⟩
  | fail error | div => cases publication <;>
      simp only [AdapterPublicServerBuildPrefix.project, AdapterPublicServerCompletionLifetime.project,
        AdapterPublicServerPublicationInstall.project, reduceCtorEq] at normal
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection.build
