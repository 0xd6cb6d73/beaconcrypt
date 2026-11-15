-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
/-! Missing and inactive bundle callbacks retain the complete current Native/platform state under the actual extracted source bundle model. These exact pure branches support the total source-object phase dispatcher. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch
private theorem apply_pure {S A : Type} {m : Type→Type} [Monad m] (value : A) (state : S) :
    (pure value :StateT S m A) state=pure (value,state) := rfl
private theorem apply_bind {S A B : Type} {m : Type→Type} [Monad m]
    (work :StateT S m A) (next : A→StateT S m B) (state : S) :
    (work>>=next) state=(work state>>=fun result=>next result.1 result.2) := rfl
private theorem apply_get {S : Type} {m : Type→Type} [Monad m] (state : S) :
    (get :StateT S m S) state=pure (state,state) := rfl
open RegistrationNativePlatformExtractedSdkAdaptive (pack)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformExtractedSdkAdaptiveBundle (bytes bytes_public)
open RegistrationNativePlatformExtractedSdkBundle (Publication withCoinsRunner freshRunner withCoinsNative freshNative)
open BeaconcryptCore.Refinement
open BeaconcryptCore.Computational
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK E Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "M" => StateT Platform ProbComp
local notation "CutM" => StateT (RegistrationNativePlatformCutJournal.State Native) M
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)
variable (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) RegistrationSigningShared.SignReply)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)

omit material platform ed localOps crypto in
theorem idle_model (before : Native) (previous : Platform)
    (selected : before.beacons[index]?=some owner)
    (idle : RegistrationNativePlatformExtractedSdkIdle.NativeBundleIdle owner.phase) :
    ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before).run previous=
      pure ((.ok none,before),previous) := by
  have same:=RegistrationNativePlatformExtractedSdkIdle.bundle_native coins setup checks representation created packetWriter index before owner selected idle
  simp only [StateT.run] at same
  unfold RegistrationNativePlatformExtractedBundle.bundle
  simp only [StateT.run]
  rw [same]
  simp only [apply_pure,apply_bind,pure_bind]
  rw [RegistrationWorldAgreementCompiler.join_erase]
  rfl

omit material platform ed localOps crypto in
theorem missing_model (before : Native) (previous : Platform)
    (missing : before.beacons[index]?=none) :
    ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before).run previous=
      pure ((.ok none,before),previous) := by
  have same : ((RegistrationNativePlatformExtractedBundle.localBody (n:=n) coins setup checks representation created source packetWriter index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world)=pure ((.ok none,before.beacons),RegistrationWorldAgreementCompiler.erase before.server.world) := by
    unfold RegistrationNativePlatformExtractedBundle.localBody RegistrationNativePlatformGenericBundle.bundle
    simp only [StateT.run,apply_bind,apply_get,apply_pure,pure_bind,missing]
  simp only [StateT.run] at same
  unfold RegistrationNativePlatformExtractedBundle.bundle
  simp only [StateT.run]
  rw [same]
  simp only [apply_pure,apply_bind,pure_bind]
  rw [RegistrationWorldAgreementCompiler.join_erase]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch.missing_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch.missing_model
