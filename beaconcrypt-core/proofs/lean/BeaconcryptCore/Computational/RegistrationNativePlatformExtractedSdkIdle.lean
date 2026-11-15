-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Refinement.AdapterPublicFinishBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
/-! Inactive public SDK bundle/finish calls return the exact original object and RNG, and their related current native callbacks retain the same state. These are the literal pure branches, not successful-history restrictions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)] [children : ChildOperations (RustT m)]
def BundleIdle : beaconcrypt_public_wrapper.beacon.BeaconState →Prop
  | .Fresh .. | .FreshWithCoins ..=>False
  | _=>True
def FinishIdle : beaconcrypt_public_wrapper.beacon.BeaconState →Prop
  | .InitSent ..=>False
  | _=>True
omit platform ed localOps crypto children [Monad m] [LawfulMonad m] in
def NativeBundleIdle : RegistrationNativeBeaconFrontend.Phase →Prop
  | .fresh | .freshWithCoins _=>False
  | _=>True
omit platform ed localOps crypto children [Monad m] [LawfulMonad m] in
def NativeFinishIdle : RegistrationNativeBeaconFrontend.Phase →Prop
  | .initSent ..=>False
  | _=>True

omit platform localOps in
theorem bundle_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) (idle : BundleIdle self.state) :
    (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m:=RustT m) generator self rng).run=
      pure (.ok (.None,self,rng)) := by
  rw [AdapterPublicBundleBody.source]
  cases phase : self.state <;> simp only [BundleIdle,phase] at idle
  all_goals simp only [AdapterPublicBundleBody.program,phase]; rfl

variable [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT m)]
theorem finish_source (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) (idle : FinishIdle self.state) :
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m:=RustT m) self input).run=
      pure (.ok (.None,self)) := by
  rw [AdapterPublicFinishBody.source]
  cases phase : self.state <;> simp only [FinishIdle,phase] at idle
  all_goals simp only [AdapterPublicFinishBody.program,phase]; rfl

variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
omit platform localOps crypto children [Monad m] [LawfulMonad m] [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT m)] in
theorem bundle_phase (view : AdapterPublicWrapperState.MaterialView source KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (stored : beaconcrypt_public_wrapper.beacon.BeaconState)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Phase view pool owner stored world)
    (idle : BundleIdle stored) : NativeBundleIdle owner.phase := by
  cases stored <;> cases phase : owner.phase <;> simp_all only [AdapterPublicWrapperState.Phase,BundleIdle,NativeBundleIdle]
omit platform localOps crypto children [Monad m] [LawfulMonad m] [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT m)] in
theorem finish_phase (view : AdapterPublicWrapperState.MaterialView source KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (stored : beaconcrypt_public_wrapper.beacon.BeaconState)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Phase view pool owner stored world)
    (idle : FinishIdle stored) : NativeFinishIdle owner.phase := by
  cases stored <;> cases phase : owner.phase <;> simp_all only [AdapterPublicWrapperState.Phase,FinishIdle,NativeFinishIdle]

omit material platform ed localOps crypto children [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT m)] in
theorem bundle_native (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (selected : before.beacons[index]?=some owner) (idle : NativeBundleIdle owner.phase) :
    ((RegistrationNativePlatformExtractedBundle.localBody (n:=n) coins setup checks representation created source writer index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world) =
      pure ((.ok none,before.beacons),RegistrationWorldAgreementCompiler.erase before.server.world) := by
  unfold RegistrationNativePlatformExtractedBundle.localBody RegistrationNativePlatformGenericBundle.bundle
  simp only [StateT.run_bind,StateT.run_get,pure_bind,selected]
  cases phase : owner.phase <;> simp only [NativeBundleIdle,phase] at idle
  all_goals rfl

omit material platform ed localOps crypto children [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT m)] [Monad m] [LawfulMonad m] in
theorem finish_native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : RegistrationNativeBeaconFrontend.State source)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : owners[index]?=some owner)
    (idle : NativeFinishIdle owner.phase) :
    (RegistrationNativePlatformExtractedFinish.finish (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) setup source wire index packet).run owners=pure (.ok none,owners) := by
  unfold RegistrationNativePlatformExtractedFinish.finish
  simp only [StateT.run_bind,StateT.run_get,pure_bind,selected]
  cases phase : owner.phase <;> simp only [NativeFinishIdle,phase] at idle
  all_goals rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_phase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.bundle_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkIdle.finish_native
