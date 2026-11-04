-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable {Value :Type}
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

local notation "Stage"=>RegistrationNativePlatformPublicAdapterSourceTrace.Stage
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages

local notation "CorePrivate"=>RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "children"=>RegistrationNativePlatformPublicAdapterDispatcherCore.children

local notation "NativeP"=>RegistrationNativeExperiment.State n KemSK source×P
open RegistrationNativePlatformPublicAdapterConfiguredBuildLog
local notation "Response"=>Option PqxdhServerRegistrationPublication.Response
def SuffixOf {A :Type} {target :ProbComp (A×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) (prior :Log) :Prop :=
  ∀result,result∈support augmented.sample→∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem suffix_transport {A :Type} {target :ProbComp (A×NativeP)}
    (left right :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Log) (prior :Log) :
    SuffixOf configuration created credential left ((congrArg (fun call=>RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) same).mpr augmented) prior ↔
      SuffixOf configuration created credential right augmented prior :=by
  cases same
  rfl

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem quiet_suffix {A :Type} {target :ProbComp (A×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) (prior :Log) :
    SuffixOf configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior) prior :=by
  intro result supported
  exact ⟨[],by simpa using RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log call prior ⟨result,supported⟩⟩

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem configured_suffix (current :NativeP) (before :CorePrivate current)
    (handle :Nat) (payload :Option (Slice U8)) (prior :Log) :
    SuffixOf configuration created credential (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
      (augmentation configuration created credential current before handle payload prior) prior :=by
  classical
  by_cases missing:before.base.objects.tokens handle=none
  · unfold augmentation
    dsimp only
    erw [dite_eq_left missing]
    exact quiet_suffix configuration created credential _ prior
  · by_cases declined:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=none
    · unfold augmentation
      dsimp only
      erw [dite_eq_right missing,dite_eq_left declined]
      exact quiet_suffix configuration created credential _ prior
    · have has:(before.base.objects.tokens handle).isSome=true:=by
        cases found:before.base.objects.tokens handle with
        | none=>exact (missing found).elim
        | some _=>rfl
      have valid:(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true:=by
        cases found:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice) with
        | none=>exact (declined found).elim
        | some _=>rfl
      obtain ⟨modelEq,sameCall,sameAug⟩:=live_pair configuration created credential current before handle payload prior has valid missing declined
      rw [sameAug]
      apply (suffix_transport configuration created credential _ _ sameCall _ prior).mpr
      exact RegistrationNativePlatformPublicAdapterBuildSigningAligned.delta coins setup codec configuration.keyView configuration.converted configuration.sealFailure
        configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
        configuration.view configuration.views created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
        ((before.base.objects.tokens handle).get has) (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid))
        configuration.pins (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
        (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
        (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey)
        prior

def AlignedOf {A :Type} {target :ProbComp (A×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) :Prop :=
  ∀result,result∈support augmented.sample→(call.step.native result.1).2.1.server.world.world.2=receipts (stages result.2)

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem aligned_transport {A :Type} {target :ProbComp (A×NativeP)}
    (left right :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Log) :
    AlignedOf configuration created credential left ((congrArg (fun call=>RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) same).mpr augmented) ↔
      AlignedOf configuration created credential right augmented :=by
  cases same
  rfl

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem quiet_aligned {A :Type} {target :ProbComp (A×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target)
    (prior :Log) (answer :A) (next :NativeP) (pureLaw :target=pure (answer,next))
    (held :next.1.server.world.world.2=receipts (stages prior)) :
    AlignedOf configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior) :=by
  intro result supported
  simp only [RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged,support_map] at supported
  obtain ⟨packet,called,same⟩:=supported
  cases same
  have mapped:call.step.native packet∈support (call.step.native <$>call.step.sample):=by
    rw [support_map]
    exact ⟨packet,called,rfl⟩
  have actual:=Eq.mp (congrArg (fun computation=>call.step.native packet∈support computation) call.step.native_exact) mapped
  have exactResult:=Eq.mp (congrArg (fun computation=>call.step.native packet∈support computation) pureLaw) actual
  simp only [support_pure,Set.mem_singleton_iff] at exactResult
  exact (congrArg (fun outcome :A×NativeP=>outcome.2.1.server.world.world.2) exactResult).trans held

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem configured_aligned (current :NativeP) (before :CorePrivate current)
    (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    (held :current.1.server.world.world.2=receipts (stages prior)) :
    AlignedOf configuration created credential (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
      (augmentation configuration created credential current before handle payload prior) :=by
  classical
  let pin :StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)):=RegistrationNativePlatformSourceBuild.pin coins
  let reserve:=(AdapterPublicServerBuildPrefix.admitted <$>StateT.lift (configuration.peerAllocate before.base.objects.server.known_ids) :StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool)
  let present :U64→StateT (RegistrationServerFrontendCompiler.State n) (StateT P ProbComp) Bool:=RegistrationNativePlatformCompletionSdk.nativePresent coins
  let finish :RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) (alloc.vec.Vec U8):=RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish (n:=n) coins setup codec configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame) configuration.erased (RegistrationNativeMldsa.owned source credential)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets)
  by_cases missing:before.base.objects.tokens handle=none
  · unfold augmentation
    dsimp only
    erw [dite_eq_left missing]
    have basePure:=RegistrationNativePlatformExtractedSdkBuildDispatch.missing_model configuration.view configuration.views setup.joint created credential current before.base
      pin reserve present finish handle missing (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice))
    have pureLaw:=congrArg (fun tree=>Prod.map RegistrationNativePlatformPublicAdapterBuildRaw.response id <$>tree) basePure
    simp only [map_pure] at pureLaw
    exact quiet_aligned configuration created credential _ prior none current pureLaw held
  · by_cases declined:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=none
    · unfold augmentation
      dsimp only
      erw [dite_eq_right missing,dite_eq_left declined]
      have has:(before.base.objects.tokens handle).isSome=true:=by
        cases found:before.base.objects.tokens handle with
        | none=>exact (missing found).elim
        | some _=>rfl
      have basePure:=RegistrationNativePlatformExtractedSdkBuildDispatch.cancel_model configuration.view configuration.views setup.joint created credential current before.base
        pin reserve present finish handle ((before.base.objects.tokens handle).get has) (Option.some_get has).symm
      have appPure:RegistrationNativePlatformPackedState.pack (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)))) current=
          pure (.ok none,(AdapterPublicServerBuildOwnership.moved handle current.1,current.2)):=by
        rw [declined]
        exact basePure
      have pureLaw:=congrArg (fun tree=>Prod.map RegistrationNativePlatformPublicAdapterBuildRaw.response id <$>tree) appPure
      simp only [map_pure] at pureLaw
      exact quiet_aligned configuration created credential _ prior none (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) pureLaw held
    · have has:(before.base.objects.tokens handle).isSome=true:=by
        cases found:before.base.objects.tokens handle with
        | none=>exact (missing found).elim
        | some _=>rfl
      have valid:(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true:=by
        cases found:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice) with
        | none=>exact (declined found).elim
        | some _=>rfl
      obtain ⟨modelEq,sameCall,sameAug⟩:=live_pair configuration created credential current before handle payload prior has valid missing declined
      rw [sameAug]
      apply (aligned_transport configuration created credential _ _ sameCall _).mpr
      exact RegistrationNativePlatformPublicAdapterBuildSigningAligned.aligned coins setup codec configuration.keyView configuration.converted configuration.sealFailure
        configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
        configuration.view configuration.views created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
        ((before.base.objects.tokens handle).get has) (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid))
        configuration.pins (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
        (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
        (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey)
        prior held

theorem suffix (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation configuration created credential handle payload before prior).sample) :
    ∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  exact configured_suffix configuration created credential before.1.1 before.2 handle payload prior result supported

theorem aligned (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (held :before.1.1.1.server.world.world.2=receipts (stages prior))
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation configuration created credential handle payload before prior).sample) :
    ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.native result.1).2.1.1.server.world.world.2=
      receipts (stages result.2) :=by
  exact configured_aligned configuration created credential before.1.1 before.2 handle payload prior held result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.configured_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.configured_suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.configured_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.configured_aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory.aligned
