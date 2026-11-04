-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishCallbackStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementCutSource
import BeaconcryptCore.Computational.RegistrationNativePlatformInitializedAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSuccessStage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLogSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReceiptFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishGivenSourceCut
open BeaconcryptCore.Refinement
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
variable {n :Nat} {I KemSK P E R Error Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
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
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=mlSource) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
open RegistrationNativePlatformExtractedSdkPublic (returned returned_exact store)
open RegistrationNativePlatformSdkReification (backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private physical)

open RegistrationNativePlatformPublicAdapterLoggedRuntime (Augmentation unchanged)
open RegistrationNativePlatformPublicAdapterFinishLoggedJoint (output physicalLog)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential mlSource)

open RegistrationNativePlatformPublicAdapterFinishLoggedDispatch (augmentation transport)



open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
open RegistrationNativeMldsaShared (Local lower)
local notation "Events"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P
local notation "AuditPrivate"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential

theorem cut (before:RegistrationNativePlatformExtractedSdkPublic.State AuditPrivate)
    (index:Nat) (input:Slice U8) (self:beaconcrypt_public_wrapper.beacon.Beacon)
    (pending:registration.BeaconPending) (prekey oneTime:beaconcrypt_crypto.crypto_kx.KeyPair) (kem:beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (sourceSelected:before.2.base.objects.beacons index=some self) (stored:self.state=.InitSent pending prekey oneTime kem)
    (packet:registration.ResponsePacket)
    (decoded:RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)=some packet)
    (past:Events)
    (result:(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.Packet×Events)
    (supported:result∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential
      (.inl (.inr (.finish index input))) before past).sample)
    (application:Pqxdh.Bytes)
    (success:((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.native result.1).1=some application) :
    ∃owner scalar,∃reached:(RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK mlSource×P)×Events,
      ∃initial completed,∃middle agreed recorded:Local n KemSK mlSource,
      before.1.1.1.beacons[index]?=some owner ∧owner.phase=.initSent pending scalar ∧
      reached∈support (RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire Event.stage coins checks
        configuration.agreement.representation created pending (AdapterPublicFinishLifetime.packet input) owner scalar before.1.1.1 before.1.1.2 past) ∧
      HEq result reached ∧result.2=past++[Event.stage (.beaconFirstRecord initial (.ok (.Ok completed)))] ∧
      (.ok (.Ok (⟨pending,packet⟩:registration.AuthenticatedResponse)),middle)∈support
        ((lower setup checks configuration.agreement.representation created
          (simulateQ (RegistrationNativeBeaconFrontend.authentication setup mlSource)
            (RegistrationResponseExecutor.begin pending (.Some packet)))).run
          (RegistrationNativePlatformCompletionReceipt.consumed (RegistrationNativePlatformInitializedAgreement.opened before.1.1.1) index
            (RegistrationResponse.abortedState pending))) ∧
      (.ok (.BeaconComplete initial.agreement),agreed)∈support
        ((lower setup checks configuration.agreement.representation created
          (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar)
            (RegistrationAgreementExecutor.beacon ⟨pending,packet⟩))).run middle) ∧
      (.ok (.Ok completed),recorded)∈support
        ((lower setup checks configuration.agreement.representation created
          (simulateQ (RegistrationNativeBeaconFrontend.record setup wire)
            (RegistrationBeaconRecordExecutor.fromInitial initial))).run agreed) ∧
      registration.begin_beacon_completion initial.agreement=.ok initial ∧
      application=TranscriptAuthParts.absSlice completed.application ∧
      RegistrationNativeWorldCache.cache recorded.2.2≤RegistrationNativeWorldCache.cache
        ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.native result.1).2.1.1:=by
  obtain ⟨owner,scalar,reached,completed,initial,selected,phase,called,samePacket,sameLog,completedEq,appEq,emitted,nativeEq⟩:=
    RegistrationNativePlatformPublicAdapterFinishCallbackStageCut.dispatcher_success configuration created credential before index input self pending prekey oneTime kem
      sourceSelected stored past result supported application success
  have injective:Function.Injective (Event.stage:Stage→RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P):=by
    intro left right same
    exact Event.stage.inj same
  obtain ⟨authenticated,authEnv,authState,agreeEnv,agreeState,authCalled,agreeCalled,started,recordCalled,_answer⟩:=
    RegistrationNativePlatformPublicAdapterFinishEmittedStageCut.emitted_sample_cut setup wire Event.stage coins checks configuration.agreement.representation created
      injective initial completed pending input owner scalar before.1.1.1 before.1.1.2 past
      [Event.stage (.beaconFirstRecord initial (.ok (.Ok completed)))] reached called emitted (List.mem_singleton.mpr rfl)
  rw [decoded] at authCalled
  let owners:=(RegistrationNativePlatformCompletionReceipt.consumed (RegistrationNativePlatformInitializedAgreement.opened before.1.1.1) index
    (RegistrationResponse.abortedState pending)).1
  have authentication:=RegistrationNativePlatformPublicAdapterAgreementCutSource.authentication coins setup checks configuration.agreement.representation created
    (RegistrationResponseExecutor.begin pending (.Some packet)) owners (RegistrationWorldAgreementCompiler.erase before.1.1.1.server.world)
    before.1.1.1 before.1.1.2 (.ok (.Ok authenticated)) authEnv authState.1 authState.2 authCalled
  have fixed:=RegistrationNativePlatformPublicAdapterAgreementCutSource.authenticated setup checks configuration.agreement.representation created
    wire pending packet _ _ authenticated authentication
  subst authenticated
  have agreementRun:=RegistrationNativePlatformPublicAdapterAgreementCutSource.agreement coins setup checks configuration.agreement.representation created
    owner scalar (RegistrationAgreementExecutor.beacon ⟨pending,packet⟩) owners authEnv authState.1 authState.2
    (.ok (.BeaconComplete initial.agreement)) agreeEnv agreeState.1 agreeState.2 agreeCalled
  have recordRun:=RegistrationNativePlatformPublicAdapterAgreementCutSource.record coins setup checks configuration.agreement.representation created
    wire (RegistrationBeaconRecordExecutor.fromInitial initial) owners agreeEnv agreeState.1 agreeState.2
    (.ok (.Ok completed)) reached.1.1.1.2 reached.1.1.2 reached.1.2 recordCalled
  refine ⟨owner,scalar,reached,initial,completed,(owners,(authEnv,authState.1)),(owners,(agreeEnv,agreeState.1)),
    (owners,(reached.1.1.1.2,reached.1.1.2)),selected,phase,called,samePacket,sameLog.trans emitted,authentication,agreementRun,recordRun,started,appEq.symm,?_⟩
  rw [nativeEq]
  change RegistrationNativeWorldCache.cache reached.1.1.2≤RegistrationNativeWorldCache.cache
    (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending before.1.1.1.beacons reached.1.1).2
  rw [show reached.1.1=((.ok (some completed),reached.1.1.1.2),reached.1.1.2) from Prod.ext (Prod.ext completedEq rfl) rfl]
  exact le_refl _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishGivenSourceCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishGivenSourceCut.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishGivenSourceCut.cut
