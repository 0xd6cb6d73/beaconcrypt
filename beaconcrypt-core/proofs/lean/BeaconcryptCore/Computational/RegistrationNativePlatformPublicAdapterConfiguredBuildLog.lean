-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildLog
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildLoggedPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The same Bundle packet and actual source stages pass through the original result projection, typed audit and concrete LowSpec dispatcher. No packet is resampled and no local source obligation remains as a caller premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog
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

local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "codec"=>RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
local notation "children"=>RegistrationNativePlatformPublicAdapterDispatcherCore.children

local notation "CorePrivate"=>RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential
local notation "corePhysical"=>RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential
local notation "NativeP"=>RegistrationNativeExperiment.State n KemSK source×P
local notation "Response"=>Option PqxdhServerRegistrationPublication.Response

noncomputable def activeCall (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) :=
  RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec configuration.keyView configuration.converted configuration.sealFailure
    configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
    configuration.view configuration.views created credential current before token data configuration.pins
    (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
    (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
    (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey)

noncomputable def activeAugmentation (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation (activeCall configuration created credential current before token data) Log :=
  RegistrationNativePlatformPublicAdapterStrongBuildLog.augment coins setup codec configuration.keyView configuration.converted configuration.sealFailure
    configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
    configuration.view configuration.views created credential current before token data configuration.pins
    (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
    (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
    (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey) RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior

noncomputable def raw {target :ProbComp (Response×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) :
    ProbComp (RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P Response) :=
  (fun packet=>
    let selected:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
    let after:=corePhysical (call.step.native packet.val.1).2 (RegistrationNativePlatformExtractedSdkPublic.store call selected)
    (.ok (call.observe (RegistrationNativePlatformExtractedSdkPublic.returned call selected),RegistrationNativePlatformPublicAdapterSourceRuntime.objects after),
      (after.backend.1,(after.backend.2,packet.val.2)))) <$>PFunctor.FreeM.attachSupp augmented.sample

def assemble (result :RegistrationNativePlatformPublicAdapterPhysicalOrdinary.Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=P) Response) (log :Log) :
    RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P Response :=
  (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects <$>result.1,(result.2.1,(result.2.2,log)))

noncomputable def mappedAugmentation (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response
        (activeCall configuration created credential current before token data)) Log :=
  let selected:=activeAugmentation configuration created credential current before token data prior
  ⟨selected.sample,selected.erase⟩

noncomputable def activeRaw (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) (prior :Log) :=
  raw configuration created credential
    (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response
      (activeCall configuration created credential current before token data))
    (mappedAugmentation configuration created credential current before token data prior)

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem active_packet (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) (prior :Log) :
    activeRaw configuration created credential current before token data prior=
      (fun result=>assemble
        (RegistrationNativePlatformPublicAdapterBuildPhysical.finish configuration.view configuration.views (corePhysical current before)
          ((activeCall configuration created credential current before token data).step.sourceReply result.1,
            RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (RegistrationNativePlatformSdkReification.persistent
              ((activeCall configuration created credential current before token data).step.sourceState result.1)))) result.2) <$>
        (activeAugmentation configuration created credential current before token data prior).sample :=by
  let call:=activeCall configuration created credential current before token data
  let augmented:=activeAugmentation configuration created credential current before token data prior
  let output :call.step.Packet×Log→RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P Response :=fun result=>
    assemble (RegistrationNativePlatformPublicAdapterBuildPhysical.finish configuration.view configuration.views (corePhysical current before)
      (call.step.sourceReply result.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent
        (RegistrationNativePlatformSdkReification.persistent (call.step.sourceState result.1)))) result.2
  have attached:=congrArg (fun computation=>output <$>computation) (PFunctor.FreeM.map_attachSupp augmented.sample)
  simp only [Functor.map_map] at attached
  refine Eq.trans ?_ attached
  unfold activeRaw raw
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp augmented.sample)
  funext packet
  let selected:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
  have kept:=RegistrationNativePlatformPublicAdapterStrongBuildSource.stored coins setup codec configuration.keyView configuration.converted configuration.sealFailure
    configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
    configuration.view configuration.views created credential current before token data configuration.pins
    (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
    (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
    (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey) selected
  have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call selected
  change (RustM.ok
    (RegistrationNativePlatformPublicAdapterBuildRaw.response (AdapterPublicServerPublicationInstall.project (.ok (RegistrationNativePlatformExtractedSdkPublic.returned call selected))),
      RegistrationNativePlatformPublicAdapterSourceRuntime.objects
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
          (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects))),
    ((RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
          (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects)).backend.1,
      ((RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
          (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call selected).base.objects)).backend.2,packet.val.2)))=_
  erw [kept]
  rw [RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_server,RegistrationNativePlatformPublicAdapterBuildNormalization.committed]
  dsimp only [output]
  unfold RegistrationNativePlatformPublicAdapterBuildPhysical.finish
  erw [normal]
  rfl

noncomputable def loggedPhysical (current :NativeP) (before :CorePrivate current) (prior :Log) :
    RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P :=
  let actual:=corePhysical current before
  {actual with backend:=(actual.backend.1,(actual.backend.2,prior))}

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem active_source (current :NativeP) (before :CorePrivate current)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) (prior :Log) :
    activeRaw configuration created credential current before token data prior=
      RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.active coins setup codec configuration.keyView configuration.sealFailure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
        (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame) configuration.erased
        (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) configuration.view configuration.views originalContainers
        token data (loggedPhysical configuration created credential current before prior) :=by
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) :QueryImpl unifSpec (StateT (RegistrationNativePlatformCutJournal.State
      (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp))) originalCrypto
  let fallback (request :registration.MldsaSigningRequest) :StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp) RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned source credential request)))
  have joint:=RegistrationNativePlatformPublicAdapterBuildProgramStages.sample_normalized_source RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage
    coins setup codec configuration.keyView configuration.sealFailure (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame) configuration.erased (RegistrationNativeMldsa.owned source credential)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) configuration.view originalLocal originalContainers previousCrypto children fallback
    before.base.objects.server token data (current.1,none) current.2 prior
  let observe (result :(((AdapterPublicServerBuildTrace.Word×RegistrationNativePlatformSdkReification.Backend n KemSK)×P)×Log)) :
      RegistrationNativePlatformPublicAdapterSourceEvents.Outcome n KemSK R P Response:=
    assemble (RegistrationNativePlatformPublicAdapterBuildPhysical.finish configuration.view configuration.views (corePhysical current before)
      (result.1.1.1.2,(result.1.1.2,result.1.2))) result.2
  have observed:=congrArg (fun computation=>observe <$>computation) joint
  simp only [Functor.map_map] at observed
  rw [active_packet]
  have backendEq : (corePhysical current before).backend=
      RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (RegistrationNativePlatformSdkReification.persistent current):=
    congrArg RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent before.base.backend
  convert observed using 1
  · rfl
  · dsimp only [observe,RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.active,loggedPhysical,
      RegistrationNativePlatformPublicAdapterSourceEvents.store]
    rw [show (corePhysical current before).server=before.base.objects.server from rfl,
      before.base.server.identity.mldsa,backendEq]
    rfl

noncomputable def augmentation (current :RegistrationNativeExperiment.State n KemSK source×P)
    (before :RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential current)
    (handle :Nat) (payload :Option (Slice U8)) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload) Log :=by
  classical
  by_cases missing:before.base.objects.tokens handle=none
  · exact RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged _ prior
  · by_cases declined:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=none
    · exact RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged _ prior
    · have has : (before.base.objects.tokens handle).isSome=true :=by
        cases found:before.base.objects.tokens handle with
        | none=>exact (missing found).elim
        | some _=>rfl
      let token:=(before.base.objects.tokens handle).get has
      have valid : (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true :=by
        cases found:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice) with
        | none=>exact (declined found).elim
        | some _=>rfl
      let app:=(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid
      let moved:=RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle
      let selected:=RegistrationNativePlatformPublicAdapterStrongBuildLog.augment coins setup codec configuration.keyView configuration.converted configuration.sealFailure
        configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets originalLocal originalContainers children
        configuration.view configuration.views created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) moved token (.Some app)
        configuration.pins (configuration.peerAllocate before.base.objects.server.known_ids) (configuration.peerReserve before.base.objects.server.known_ids)
        (configuration.peerFootprint before.base.objects.server.known_ids) (configuration.peerMember before.base.objects.server.known_ids)
        (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.base.objects.server with known_ids:=known} inserting publicKey)
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
      simp only [RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep,RegistrationNativePlatformPublicAdapterBuildRaw.step,
        RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep,missing,declined,↓reduceDIte]
      exact ⟨selected.sample,selected.erase⟩

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem raw_unchanged {target :ProbComp (Response×NativeP)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate target) (prior :Log) :
    raw configuration created credential call (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior)=
      (fun result=>assemble result prior) <$>
        RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw corePhysical call :=by
  unfold raw RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  rw [←RegistrationNativePlatformPublicAdapterLoggedRuntime.project_sample call
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior),Functor.map_map,Functor.map_map]
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged call prior).sample)
  funext packet
  rw [RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem typed_query (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw corePhysical
      (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)=
      RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation configuration (corePhysical current before) handle payload :=by
  have law:=RegistrationNativePlatformPublicAdapterConfiguredBuild.query configuration created credential current before handle payload
  unfold RegistrationNativePlatformPublicAdapterConfiguredBuild.step at law
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast] at law
  exact law

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem raw_cast_mapped {A :Type} {left right :ProbComp (A×NativeP)}
    (same :left=right) (observe :A→Response)
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate left)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterReply.map observe call) Log) :
    raw configuration created credential
      (RegistrationNativePlatformPublicAdapterReply.map observe (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same call))
      ⟨augmented.sample,augmented.erase⟩=
      raw configuration created credential (RegistrationNativePlatformPublicAdapterReply.map observe call) augmented :=by
  rfl



omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem live_call (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8))
    (has :(before.base.objects.tokens handle).isSome=true)
    (valid :(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true)
    (missing :before.base.objects.tokens handle≠none)
    (declined :RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)≠none) :
    ∃same, RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload=
      RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response
        (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same
          (activeCall configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
            (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
            ((before.base.objects.tokens handle).get has)
            (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)))) :=by
  unfold RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep RegistrationNativePlatformPublicAdapterBuildRaw.step
    RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep
  dsimp only
  refine ⟨?_,?_⟩
  · conv_rhs=>rw [(Option.some_get valid).symm]
    exact (RegistrationNativePlatformExtractedSdkBuildDispatch.live_model configuration.view configuration.views setup.joint created credential current before.base
      _ _ _ _ _ handle ((before.base.objects.tokens handle).get has) (Option.some_get has).symm
      ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)).symm
  · exact congrArg (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response)
      ((dite_eq_right missing).trans (dite_eq_right declined))


omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem live_pair (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log)
    (has :(before.base.objects.tokens handle).isSome=true)
    (valid :(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true)
    (missing :before.base.objects.tokens handle≠none)
    (declined :RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)≠none) :
    ∃same, ∃sameCall: RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload=
      RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response
        (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same
          (activeCall configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
            (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
            ((before.base.objects.tokens handle).get has)
            (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)))),
      augmentation configuration created credential current before handle payload prior=
        (congrArg (fun call=>RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) sameCall).mpr
          ⟨(activeAugmentation configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
            (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
            ((before.base.objects.tokens handle).get has)
            (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)) prior).sample,
           (activeAugmentation configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
            (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle)
            ((before.base.objects.tokens handle).get has)
            (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)) prior).erase⟩ :=by
  obtain ⟨same,callEq⟩:=live_call configuration created credential current before handle payload has valid missing declined
  refine ⟨same,callEq,?_⟩
  unfold augmentation
  dsimp only
  exact (dite_eq_right missing).trans (dite_eq_right declined)



omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem raw_transport {model :ProbComp (Response×NativeP)}
    (left right :RegistrationNativePlatformExtractedSdkPublic.TotalStep CorePrivate model)
    (same :left=right) (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation right Log) :
    raw configuration created credential left
      ((congrArg (fun call=>RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call Log) same).mpr augmented)=
      raw configuration created credential right augmented :=by
  cases same
  rfl
omit [PublicWrapperPlatform.CryptoOperations] in
theorem source_joint (current :NativeP) (before :CorePrivate current) (handle :Nat) (payload :Option (Slice U8)) (prior :Log) :
    raw configuration created credential
      (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
      (augmentation configuration created credential current before handle payload prior)=
    RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation configuration
      (loggedPhysical configuration created credential current before prior) handle payload :=by
  classical
  by_cases missing:before.base.objects.tokens handle=none
  · simp only [augmentation,missing,↓reduceDIte]
    rw [raw_unchanged,typed_query]
    unfold RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation RegistrationNativePlatformPublicAdapterBuildPhysical.run
      RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run
    change (fun result=>assemble result prior) <$>
      (match before.base.objects.tokens handle with | none=>_ | some token=>_)=
      (match before.base.objects.tokens handle with | none=>_ | some token=>_)
    rw [missing]
    rfl
  · have has : (before.base.objects.tokens handle).isSome=true :=by
      cases found:before.base.objects.tokens handle with
      | none=>exact (missing found).elim
      | some _=>rfl
    let token:=(before.base.objects.tokens handle).get has
    have stored :before.base.objects.tokens handle=some token:=(Option.some_get has).symm
    let moved:=RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential current before handle
    by_cases declined:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=none
    · simp only [augmentation,missing,declined,↓reduceDIte]
      rw [raw_unchanged,typed_query]
      unfold RegistrationNativePlatformPublicAdapterConfiguredBuild.sourceOperation RegistrationNativePlatformPublicAdapterBuildPhysical.run
        RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run
      change (fun result=>assemble result prior) <$>
        (match before.base.objects.tokens handle with | none=>_ | some token=>_)=
        (match before.base.objects.tokens handle with | none=>_ | some token=>_)
      rw [stored,declined]
      rfl
    · have valid : (RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).isSome=true :=by
        cases found:RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice) with
        | none=>exact (declined found).elim
        | some _=>rfl
      let app:=(RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid
      have applicationEq :RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)=some app:=(Option.some_get valid).symm
      calc
        _=activeRaw configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) moved token (.Some app) prior :=by
          obtain ⟨same,callEq,augEq⟩:=live_pair configuration created credential current before handle payload prior has valid missing declined
          let baseCall:=activeCall configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) moved token (.Some app)
          let baseAug:=mappedAugmentation configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) moved token (.Some app) prior
          have castLaw:=raw_cast_mapped configuration created credential same RegistrationNativePlatformPublicAdapterBuildRaw.response baseCall baseAug
          have transportLaw:=raw_transport configuration created credential
            (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)
            (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response
              (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same baseCall)) callEq
            ⟨baseAug.sample,baseAug.erase⟩
          exact (congrArg (raw configuration created credential
            (RegistrationNativePlatformPublicAdapterConfiguredBuild.typedStep configuration created credential current before handle payload)) augEq).trans
            (transportLaw.trans castLaw)
        _=RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.active coins setup codec configuration.keyView configuration.sealFailure
            (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
            (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame) configuration.erased
            (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) configuration.view configuration.views originalContainers token (.Some app)
            (loggedPhysical configuration created credential (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) moved prior) :=
          active_source configuration created credential _ moved token (.Some app) prior
        _=_ :=by
          unfold RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.run
          conv_rhs=>change match before.base.objects.tokens handle with | none=>_ | some token=>_
          conv_rhs=>rw [stored,applicationEq]
          rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.augmentation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.active_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.active_packet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.active_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.active_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_unchanged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.typed_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.typed_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_cast_mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_cast_mapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.live_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.live_call
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.live_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.live_pair
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw_transport
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog.source_joint
