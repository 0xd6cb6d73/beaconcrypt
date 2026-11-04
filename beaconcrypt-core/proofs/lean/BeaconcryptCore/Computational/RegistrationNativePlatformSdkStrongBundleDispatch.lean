-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundleDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundlePublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
/-! Active bundle calls build their complete next private carrier internally from the same actual source result. Only individual opaque-object getter, generation, signing and dictionary contracts remain explicit. The caller supplies neither a continuation carrier nor a complete callback or security law. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleDispatch
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
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (failure : ed.Error)
variable (fallback : registration.MldsaSigningRequest → RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) RegistrationSigningShared.SignReply)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


variable [idleLocal : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCrypto : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleChildren : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]

omit localOps crypto idleLocal idleCrypto idleChildren in
private noncomputable def absent {R : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (current : Native×Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential current) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pure ((.ok none :RustM (Option Pqxdh.Bytes)),current)) := {
  step:={
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option Pqxdh.Bytes
    sourceReply:=fun _=>.ok none
    sourceState:=fun _=>objects.base.objects.snapshot.committed
    sourceCall:=pure (.ok none,objects.base.objects.snapshot.committed)
    source_exact:=rfl
    native:=fun _=>(.ok none,current)
    native_exact:=rfl
    store:=fun _ _=>objects }
  observe:=RustM.ok
  normal:=fun _ _=>⟨none,rfl⟩
  reply:=by
    intro _packet _supported returned actual
    cases actual
    rfl }

noncomputable def step {R Error : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m:=CutM) view)
    (generator : rand_core.TryCryptoRng R Error)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (RegistrationNativePlatformCutErasure.liftWorld (AdapterPublicBundleSourceExecution.sample (n:=n) (source:=source) coins setup checks representation created packetWriter)))
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (leaves : ∀owner self,before.1.beacons[index]?=some owner → objects.base.objects.beacons index=some self →
      AdapterPublicBundleSourceExecution.Leaves coins setup checks representation created packetWriter index owner failure fallback self) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pack <$> ((RegistrationNativePlatformExtractedBundle.bundle coins setup checks representation created source packetWriter index).run before.1).run previous) := by
  cases selected:before.1.beacons[index]? with
  | none=>
    rw [RegistrationNativePlatformExtractedSdkBundleDispatch.missing_model coins setup checks representation created reservePackets index before.1 previous selected,map_pure]
    exact absent setup created containersView credential view (before.1,previous) objects
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected : objects.base.objects.beacons index=some self := (Classical.choose_spec prior).1
    have related : AdapterPublicWrapperState.Beacon view setup.joint before.1.pool self owner
        before.1.server.world.world.1.owners[owner.worldOwner]? := (Classical.choose_spec prior).2
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase : owner.phase=.fresh := by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      exact RegistrationNativePlatformSdkStrongBundleSteps.fresh coins setup checks representation created reservePackets index owner failure fallback other recording containersView credential
        self view getters (leaves owner self selected sourceSelected) control prekey kem generator generation stored phase before previous objects sourceSelected selected
    | FreshWithCoins control prekey oneTime kem=>
      have phase : ∃scalar,owner.phase=.freshWithCoins scalar := by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.freshWithCoins scalar:=Classical.choose_spec phase
      exact RegistrationNativePlatformSdkStrongBundleSteps.withCoins coins setup checks representation created reservePackets index owner failure fallback other recording containersView credential
        self view getters (leaves owner self selected sourceSelected) control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
    | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state := by rw [stored]; trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      rw [RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks representation created reservePackets index owner before.1 previous selected inactive,map_pure]
      exact RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle
        (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
        (before.1,previous) objects.base.objects.snapshot.committed objects generator self objects.base.objects.rng idle
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongBundleDispatch.step
