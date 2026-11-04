-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildActiveSample
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildRecordStage
/-! A given actual server-sign observation in the complete configured Build callback identifies its actual source token, literal moved native capability, source initializer and same final-cache first-record cut. Missing and conversion-cancel branches cannot emit that observation; publication or installation need not succeed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage
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
theorem sample (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation configuration created credential handle payload before prior).sample)
    (suffix :List Stage) (observed :result.2=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)
    (request :registration.MldsaSigningRequest) (candidate :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :Stage.sign request candidate digest signature∈suffix) :
    ∃(token :beaconcrypt_public_wrapper.server.RegistrationOutput) (current :RegistrationServerFrontendCompiler.State n)
        (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
        (pin :session.ServerAuthenticationPin) (availability :pqxdh.KeyIdAvailability) (application :Slice U8),
      before.2.base.objects.tokens handle=some token ∧
      RegistrationServerSdkSource.take handle before.1.1.1.server=(some token.registration,current) ∧
      registration.begin_server_completion current.control pin availability token.registration.agreement application=.ok (.Ok initial) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire) configuration.keyView configuration.sealFailure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin) configuration.erased
        (RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame) (RegistrationNativePlatformConcreteSource.serializer (Platform:=P))
        initial hashed (RegistrationNativeWorldCache.cache
          ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2).step.native result.1).2.1.1) ∧
      Stage.firstRecord initial (.ok (.Ok hashed))∈suffix ∧
      candidate=RegistrationSigningTrace.Command.payload (.server hashed) ∧request.public_key=hashed.binding.server_pin.public_key :=by
  obtain ⟨has,valid,packet.captured,packet.supported,logEq,nativeEq⟩:=RegistrationNativePlatformPublicAdapterBuildActiveSample.sample
    configuration created credential handle payload before prior result supported suffix observed request candidate digest signature present
  let token:=(before.2.base.objects.tokens handle).get has
  have stored:before.2.base.objects.tokens handle=some token:=(Option.some_get has).symm
  let moved:=RegistrationNativePlatformPublicAdapterBuildDispatch.move setup configuration.view configuration.views created credential before.1.1 before.2 handle
  obtain ⟨consumed,live,related⟩:=RegistrationNativePlatformExtractedSdkCarrier.source_token
    configuration.view configuration.views setup.joint created credential before.1.1 before.2.base handle token stored
  have taken:RegistrationServerSdkSource.take handle before.1.1.1.server=(some token.registration,(AdapterPublicServerBuildOwnership.moved handle before.1.1.1).server):=
    (AdapterPublicServerBuildOwnership.move token consumed before.1.1.1 handle related live).1
  obtain ⟨initial,hashed,pin,availability,application,started,path,cut,recorded,payloadEq,key⟩:=
    RegistrationNativePlatformPublicAdapterStrongBuildRecordStage.sample coins setup
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
      configuration.keyView configuration.converted configuration.sealFailure configuration.allocateJoin configuration.reserveFrame configuration.erased configuration.reservePackets
      originalLocal originalContainers children configuration.view configuration.views created credential
      (AdapterPublicServerBuildOwnership.moved handle before.1.1.1,before.1.1.2) moved token
      (.Some ((RegistrationNativeRawAdapter.application (payload.map TranscriptAuthParts.absSlice)).get valid)) configuration.pins
      (configuration.peerAllocate before.2.base.objects.server.known_ids) (configuration.peerReserve before.2.base.objects.server.known_ids)
      (configuration.peerFootprint before.2.base.objects.server.known_ids) (configuration.peerMember before.2.base.objects.server.known_ids)
      (fun known _publication inserting publicKey _began _parsed=>configuration.peerInstall {before.2.base.objects.server with known_ids:=known} inserting publicKey)
      prior packet.captured packet.supported suffix (logEq.trans observed) request candidate digest signature present
  have controlEq:moved.base.objects.server.control=(AdapterPublicServerBuildOwnership.moved handle before.1.1.1).server.control:=moved.base.server.control
  rw [controlEq] at started
  refine ⟨token,_,initial,hashed,pin,availability,application,stored,taken,started,path,?_,recorded,payloadEq,key⟩
  have cacheEq:=congrArg (fun current:NativeP=>RegistrationNativeWorldCache.cache current.1) nativeEq
  exact cacheEq ▸cut

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage.sample
