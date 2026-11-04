-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleDispatchSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleInstrumentation
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps
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
variable [original : CryptoOperations (RustT ProbComp)]
variable (previousLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp))))
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (reservePackets : Usize →StateT Platform ProbComp (core.result.Result Unit E))
local notation "packetWriter" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (index : Nat) (failure : ed.Error)
variable (other : QueryImpl AdapterInitAuthenticationRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT Platform ProbComp)))

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


variable [idleLocal : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCrypto : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleChildren : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]

variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (sealFailure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat→StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actualCoins"=>RegistrationNativePlatformMldsaProgram.coins

noncomputable def model (current : Native×Platform) :=
  pack <$> ((RegistrationNativePlatformPublicAdapterRawModel.raw setup checks representation created credential keyView sealFailure allocation
    reserveRegistration reservePeer reserveFrame erased helper packetWriter (.inr (.bundle index))).run current.1).run current.2

omit original idleLocal idleCrypto idleChildren primitives [FrameDispatchFallback.Operations] in
private noncomputable def cast {N Reply : Type} {Private : N→Type} {left right : ProbComp (Reply×N)}
    (same : left=right) (call : TotalStep Private left) : TotalStep Private right :=same ▸call

omit original idleLocal idleCrypto idleChildren primitives [FrameDispatchFallback.Operations] in
private theorem raw_cast {N Reply R : Type} {Private : N→Type} {left right : ProbComp (Reply×N)}
    (same : left=right) (call : TotalStep Private left) (physical : ∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (cast same call)=RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call :=by cases same;rfl

noncomputable def physical {R : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK) (current : Native×Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential current) :=
  RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects)

noncomputable def step {R Error : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (generator : rand_core.TryCryptoRng R Error)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous)) :
    TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (model setup checks representation created reservePackets index credential keyView sealFailure allocation reserveRegistration reservePeer reserveFrame erased helper (before.1,previous)) :=by
  let call:=RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption
    (RegistrationNativePlatformPublicAdapterStrongBundle.step previousLocal actualCoins setup checks representation created reservePackets index failure other recording containersView credential view generator generation before previous objects)
  refine cast ?_ call
  unfold model
  rw [RegistrationNativePlatformPublicAdapterRawModel.bundle]
  simp only [StateT.run_map,Functor.map_map]
  rfl

omit original idleLocal idleCrypto idleChildren primitives [FrameDispatchFallback.Operations] in
private theorem raw_normalize {N Reply R : Type} {Private : N→Type} {target : ProbComp (Reply×N)}
    (call : TotalStep Private target) (project : ∀current,Private current→RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (fun current before=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize (project current before)) call=
      RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw project call :=by
  unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  conv_rhs=>erw [Functor.map_map]
  rfl

theorem query {R Error : Type}
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (generator : rand_core.TryCryptoRng R Error)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (physicalLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT Platform ProbComp))))
    (physicalChildren : ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT Platform ProbComp)))) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical setup created containersView credential view)
      (step previousLocal setup checks representation created reservePackets index failure other recording containersView credential keyView sealFailure allocation reserveRegistration reservePeer reserveFrame erased helper view generator generation before previous objects)=
      RegistrationNativePlatformPublicAdapterBundlePhysical.run actualCoins setup checks representation created view physicalLocal failure packetWriter physicalChildren generator
        (physical setup created containersView credential view (before.1,previous) objects) index :=by
  unfold step
  rw [raw_cast]
  exact (raw_normalize _ (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view containersView created credential)).trans
    ((congrArg (fun tree=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>tree)
      (RegistrationNativePlatformPublicAdapterBundleDispatchSource.query actualCoins setup checks representation created view physicalLocal failure reservePackets physicalChildren previousLocal other recording containersView credential index generator generation before previous objects)).trans
      (RegistrationNativePlatformPublicAdapterBundleNormalization.run_source actualCoins setup checks representation created view physicalLocal failure packetWriter physicalChildren generator (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects) index))

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleRawSteps.query
