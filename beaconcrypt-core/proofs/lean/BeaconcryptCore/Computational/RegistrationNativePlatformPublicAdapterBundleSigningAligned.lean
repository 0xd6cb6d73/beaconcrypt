-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogged
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLoggedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
/-! The actual full Bundle phase union preserves source/native signing-history alignment on every supported instance of its existing augmented packet. Fresh generation and later publication failure retain the same receipts, and missing/inactive callbacks preserve the exact prior log. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private model physical children other recording packedLocal packedCrypto)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)
local notation "previousLocal"=>RegistrationNativePlatformPublicAdapterLeaves.localOperations
  (S:=RegistrationNativePlatformCutJournal.State Native) originalLocal
noncomputable local instance idleLocal :LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedLocal
noncomputable local instance idleCrypto :CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=packedCrypto
noncomputable local instance idleChildren :ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source×P) ProbComp)):=children

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "auditPrivate"=>RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential
local notation "auditModel"=>RegistrationNativePlatformPublicAdapterAuditModel.model configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable {Log :Type}

open RegistrationNativePlatformPublicAdapterBundleLogged (step augmentation withCoinsAugmentation freshAugmentation)
open RegistrationNativePlatformPublicAdapterSourceSigningHistory (receipts)
open RegistrationNativePlatformPublicAdapterSourceAuthentication (stages)
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

def Preserves {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Events) :Prop :=
  ∀result,result∈support augmented.sample→
    RegistrationNativePlatformPublicAdapterBundleSigningDelta.history (call.step.native result.1).2.1=receipts (stages result.2)

omit [FrameDispatchFallback.Operations] in
private theorem transport {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (left right :TotalStep (Private configuration created credential) target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Events) :
    Preserves configuration created credential left (same.symm ▸augmented) ↔Preserves configuration created credential right augmented :=by
  cases same
  rfl

omit [FrameDispatchFallback.Operations] in
private theorem quiet {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target) (before :Native) (previous :P)
    (reply :RustM (Option Pqxdh.Bytes)) (pureLaw :target=pure (reply,(before,previous)))
    (prior :Events) (aligned :RegistrationNativePlatformPublicAdapterBundleSigningDelta.Aligned (before,prior)) :
    Preserves configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior) :=by
  intro result supported
  simp only [RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged,support_map] at supported
  obtain ⟨packet,called,same⟩:=supported
  cases same
  have mapped :call.step.native packet∈support (call.step.native <$>call.step.sample) :=by
    rw [support_map]
    exact ⟨packet,called,rfl⟩
  have actual:=Eq.mp (congrArg (fun distribution=>call.step.native packet∈support distribution) call.step.native_exact) mapped
  have actualPure:=Eq.mp (congrArg (fun distribution=>call.step.native packet∈support distribution) pureLaw) actual
  simp only [support_pure,Set.mem_singleton_iff] at actualPure
  exact (congrArg (fun result :RustM (Option Pqxdh.Bytes)×(Native×P)=>RegistrationNativePlatformPublicAdapterBundleSigningDelta.history result.2.1) actualPure).trans aligned

omit [FrameDispatchFallback.Operations] in
private theorem with_coins (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh) (scalar :PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.FreshWithCoins control prekey oneTime kem) (phase :owner.phase=.freshWithCoins scalar)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (prior :Events) (aligned :RegistrationNativePlatformPublicAdapterBundleSigningDelta.Aligned (before.1,prior)):
    Preserves configuration created credential (RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
      configuration.reservePackets index owner configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential self configuration.view
      control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected)
      (withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior) :=by
    intro result supported
    change RegistrationNativePlatformPublicAdapterBundleSigningDelta.history
      (RegistrationNativeBundleLifecycle.after index owner scalar result.1.1.1 result.1.1.2)=receipts (stages result.2)
    exact (RegistrationNativePlatformPublicAdapterBundleSigningDelta.lifecycle index owner scalar result.1.1.1 result.1.1.2).trans
      (RegistrationNativePlatformPublicAdapterBundleSigningDelta.runner coins setup checks configuration.agreement.representation created writer index owner scalar before.1 previous prior aligned result supported)

omit [FrameDispatchFallback.Operations] in
private theorem fresh (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner source)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (control :pqxdh.BeaconFresh)
    (prekey :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.Fresh control prekey kem) (phase :owner.phase=.fresh)
    (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (selected :before.1.beacons[index]?=some owner)
    (prior :Events) (aligned :RegistrationNativePlatformPublicAdapterBundleSigningDelta.Aligned (before.1,prior)):
    Preserves configuration created credential (RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
      configuration.reservePackets index owner configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential self configuration.view
      control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration) stored phase before previous objects sourceSelected selected)
      (freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior) :=by
    intro result supported
    change RegistrationNativePlatformPublicAdapterBundleSigningDelta.history
      (RegistrationNativeBundleLifecycle.after index owner result.1.1.1.1 result.1.1.1.2 result.1.1.2)=receipts (stages result.2)
    exact (RegistrationNativePlatformPublicAdapterBundleSigningDelta.lifecycle index owner result.1.1.1.1 result.1.1.1.2 result.1.1.2).trans
      (RegistrationNativePlatformPublicAdapterBundleSigningDelta.freshRunner coins setup checks configuration.agreement.representation created writer index owner before.1 previous prior aligned result supported)

omit [FrameDispatchFallback.Operations] in
theorem preserves (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (prior :Events)
    (aligned :RegistrationNativePlatformPublicAdapterBundleSigningDelta.Aligned (before.1,prior)) :
    Preserves configuration created credential (step configuration created credential index before previous objects)
      (augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior) :=by
  cases selected:before.1.beacons[index]? with
  | none=>
    have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
      (RegistrationNativePlatformExtractedSdkBundleDispatch.missing_model coins setup checks configuration.agreement.representation created configuration.reservePackets index before.1 previous selected)
    simp only [map_pure] at pureLaw
    have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
        RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans (by rfl))
    rw [augEq]
    exact quiet configuration created credential _ before.1 previous (.ok none) pureLaw prior aligned
  | some owner=>
    have found:=objects.base.beacons index
    rw [selected] at found
    let self:=Classical.choose found
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec found).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint before.1.pool self owner
        before.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec found).2
    cases stored:self.state with
    | Fresh control prekey kem=>
      have phase :owner.phase=.fresh :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        rfl
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control prekey kem configuration.generator (RegistrationNativePlatformPublicAdapterConfiguration.generation configuration)
            stored phase before previous objects sourceSelected selected
      let activeAug:=freshAugmentation configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      exact (transport configuration created credential _ _ callEq activeAug).2
        (fresh configuration created credential index owner self control prekey kem stored phase before previous objects sourceSelected selected prior aligned)
    | FreshWithCoins control prekey oneTime kem=>
      have hasScalar :∃scalar,owner.phase=.freshWithCoins scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose hasScalar
      have phase :owner.phase=.freshWithCoins scalar:=Classical.choose_spec hasScalar
      let active:=RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks configuration.agreement.representation created
            configuration.reservePackets index owner configuration.edFailure (other (m:=CutM)) (recording (m:=CutM)) configuration.views credential self configuration.view
            control scalar prekey oneTime kem configuration.generator stored phase before previous objects sourceSelected selected
      let activeAug:=withCoinsAugmentation configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
      have callEq :step configuration created credential index before previous objects=active :=by
        unfold step RegistrationNativePlatformPublicAdapterStrongBundle.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=callEq.symm ▸activeAug :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq]
      exact (transport configuration created credential _ _ callEq activeAug).2
        (with_coins configuration created credential index owner self control scalar prekey oneTime kem stored phase before previous objects sourceSelected selected prior aligned)
    | InitSent pending prekey oneTime kem=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase configuration.view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks configuration.agreement.representation created configuration.reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      rw [augEq]
      exact quiet configuration created credential _ before.1 previous (.ok none) pureLaw prior aligned
    | Established control binding manager=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase configuration.view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks configuration.agreement.representation created configuration.reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      rw [augEq]
      exact quiet configuration created credential _ before.1 previous (.ok none) pureLaw prior aligned
    | Aborted control=>
      have idle :RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state :=by rw [stored];trivial
      have augEq :augmentation configuration created credential index before previous objects RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior=
          RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (step configuration created credential index before previous objects) prior :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.bundle_phase configuration.view before.1.pool owner self.state
        before.1.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      have pureLaw:=congrArg (fun tree=>RegistrationNativePlatformExtractedSdkAdaptive.pack <$>tree)
        (RegistrationNativePlatformExtractedSdkBundleDispatch.idle_model coins setup checks configuration.agreement.representation created configuration.reservePackets index owner before.1 previous selected inactive)
      simp only [map_pure] at pureLaw
      rw [augEq]
      exact quiet configuration created credential _ before.1 previous (.ok none) pureLaw prior aligned

omit [FrameDispatchFallback.Operations] in
theorem aligned (index :Nat) (before :RegistrationNativePlatformCutJournal.State Native) (previous :P)
    (objects :Private configuration created credential (before.1,previous)) (prior :Events)
    (held :RegistrationNativePlatformPublicAdapterBundleSigningDelta.Aligned (before.1,prior))
    (result :(step configuration created credential index before previous objects).step.Packet×Events)
    (supported :result∈support (augmentation configuration created credential index before previous objects
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior).sample) :
    ((step configuration created credential index before previous objects).step.native result.1).2.1.server.world.world.2=
      receipts (stages result.2) :=
  preserves configuration created credential index before previous objects prior held result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned.preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned.preserves
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned.aligned
