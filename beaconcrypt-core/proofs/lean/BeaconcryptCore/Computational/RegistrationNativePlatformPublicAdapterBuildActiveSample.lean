-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample
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
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages

local notation "CorePrivate"=>RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "children"=>RegistrationNativePlatformPublicAdapterDispatcherCore.children

local notation "NativeP"=>RegistrationNativeExperiment.State n KemSK source×P
open RegistrationNativePlatformPublicAdapterConfiguredBuildLog
local notation "Response"=>Option PqxdhServerRegistrationPublication.Response

def Active (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    (after :NativeP) (events :Log) :Prop :=
  ∃(has :(before.base.objects.tokens handle).isSome=true)
    (valid :(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true),
    ∃result :
      (activeCall configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
        ((before.base.objects.tokens handle).get has)
        (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid))).step.Packet×Log,
      result∈support (activeAugmentation configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
        ((before.base.objects.tokens handle).get has)
        (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)) prior).sample ∧
      result.2=events ∧
      ((activeCall configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
        ((before.base.objects.tokens handle).get has)
        (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid))).step.native result.1).2=after

def ActiveOf (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    {Reply :Type} {target :ProbComp (Reply×NativeP)} (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) :Prop :=
  ∀result,result∈support augmented.sample→∀suffix :List Stage,
    result.2=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage→
    ∀request candidate digest signature,Stage.sign request candidate digest signature∈suffix→
    Active configuration created credential current before handle payload prior (call.step.native result.1).2 result.2

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem transport (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    {Reply :Type} {target :ProbComp (Reply×NativeP)}
    (left right :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) (same :left=right)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Log) :
    ActiveOf configuration created credential current before handle payload prior left
      ((congrArg (fun call=>RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) same).mpr augmented) ↔
    ActiveOf configuration created credential current before handle payload prior right augmented :=by
  cases same
  rfl

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem quiet (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    {Reply :Type} {target :ProbComp (Reply×NativeP)} (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) :
    ActiveOf configuration created credential current before handle payload prior call
      (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior) :=by
  intro result supported suffix observed request candidate digest signature present
  have kept:=RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log call prior ⟨result,supported⟩
  have empty :suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage=[]:=
    List.append_cancel_left (observed.symm.trans (kept.trans (List.append_nil _).symm))
  have seen :(RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.sign request candidate digest signature) :RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)∈
      suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage:=List.mem_map.mpr ⟨_,present,rfl⟩
  rw [empty] at seen
  cases seen


omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem live (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    (missing :before.base.objects.tokens handle≠none)
    (declined :RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)≠none)
    (has :(before.base.objects.tokens handle).isSome=true)
    (valid :(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true) :
    ActiveOf configuration created credential current before handle payload prior
      (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
      (augmentation configuration created credential current before handle payload prior) :=by
  obtain ⟨_modelEq,sameCall,sameAug⟩:=live_pair configuration created credential current before handle payload prior has valid missing declined
  rw [sameAug]
  apply (transport configuration created credential current before handle payload prior _ _ sameCall _).mpr
  intro packet.result packet.supported _suffix _observed _request _candidate _digest _signature _present
  exact ⟨has,valid,packet.result,packet.supported,rfl,rfl⟩

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem configured (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log) :
    ActiveOf configuration created credential current before handle payload prior
      (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
      (augmentation configuration created credential current before handle payload prior) :=by
  classical
  by_cases missing:before.base.objects.tokens handle=none
  · unfold augmentation
    dsimp only
    erw [dite_eq_left missing]
    exact quiet configuration created credential current before handle payload prior _
  · by_cases declined:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=none
    · unfold augmentation
      dsimp only
      erw [dite_eq_right missing,dite_eq_left declined]
      exact quiet configuration created credential current before handle payload prior _
    · have has:(before.base.objects.tokens handle).isSome=true:=by
        cases found:before.base.objects.tokens handle with
        | none=>exact (missing found).elim
        | some _=>rfl
      have valid:(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true:=by
        cases found:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice) with
        | none=>exact (declined found).elim
        | some _=>rfl
      exact live configuration created credential current before handle payload prior missing declined has valid

theorem sample (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation configuration created credential handle payload before prior).sample)
    (suffix :List Stage) (observed :result.2=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)
    (request :registration.MldsaSigningRequest) (candidate :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :Stage.sign request candidate digest signature∈suffix) :
    Active configuration created credential before.1.1 before.2 handle payload prior
      ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.native result.1).2.1 result.2 :=by
  exact configured configuration created credential before.1.1 before.2 handle payload prior result supported suffix observed request candidate digest signature present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample.configured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample.configured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample.sample
