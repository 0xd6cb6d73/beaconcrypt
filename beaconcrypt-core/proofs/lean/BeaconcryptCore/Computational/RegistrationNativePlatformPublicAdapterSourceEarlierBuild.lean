-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterServerSigning
/-! A given earlier actual source server-sign observation is located in its actual earlier Build callback. Its token, first-record initializer, reply, full source state and native cache anchor come from the same supported packet, with repeated observations and failed later publication retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEarlierBuild
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
local notation "State"=>RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential
local notation "Spec"=>RegistrationNativePlatformPublicAdapterLowSpec.Spec
local notation "implementation"=>RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential
open RegistrationNativeStageTrace (Call Path Executed)

structure Staged (request :registration.MldsaSigningRequest) (candidate :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply) (call :Call Spec State) where
  handle :Nat
  data :Option (Slice U8)
  queryEq :call.query=.inl (.inr (.build handle data))
  middle :List Stage
  block :call.after.2=call.before.2++RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.opened configuration created credential call::
    (middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage++
      [RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed configuration created credential call])
  token :beaconcrypt_public_wrapper.server.RegistrationOutput
  current :RegistrationServerFrontendCompiler.State n
  initial :registration.ServerInitialKdf
  hashed :registration.ServerResponseHash
  pin :session.ServerAuthenticationPin
  availability :pqxdh.KeyIdAvailability
  application :Slice U8
  tokenFound :(physical call.before.1.1 call.before.1.2).tokens handle=some token
  taken :RegistrationServerSdkSource.take handle call.before.1.1.1.1.server=(some token.registration,current)
  started :registration.begin_server_completion current.control pin availability token.registration.agreement application=.ok (.Ok initial)
  recordPath :RegistrationServerRecordExecutor.Path initial hashed
  recordCut :RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire) configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin) configuration.erased
    (RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame) (RegistrationNativePlatformConcreteSource.serializer (Platform:=P))
    initial hashed (RegistrationNativeWorldCache.cache call.after.1.1.1.1)
  recorded :Stage.firstRecord initial (.ok (.Ok hashed))∈middle
  signed :Stage.sign request candidate digest signature∈middle
  payloadEq :candidate=RegistrationSigningTrace.Command.payload (.server hashed)
  key :request.public_key=hashed.binding.server_pin.public_key

private theorem path_log {before after :State} {calls :List (Call Spec State)}
    (path :Path implementation before calls after) :∃suffix,after.2=before.2++suffix :=by
  induction path with
  | nil=>exact ⟨[],(List.append_nil _).symm⟩
  | cons call called rest last following ih=>
    obtain ⟨middle,block⟩:=RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.block configuration created credential call called
    obtain ⟨suffix,later⟩:=ih
    exact ⟨RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.opened configuration created credential call::
      (middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage++
        [RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed configuration created credential call])++suffix,
      by rw [later,block,List.append_assoc]⟩

theorem stage {before after :State} {calls :List (Call Spec State)}
    (actual :Path implementation before calls after) (empty :before.2=[])
    (held :RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential before)
    (request :registration.MldsaSigningRequest) (candidate :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.sign request candidate digest signature)∈after.2)
    (role :candidate.role=.server) :
    ∃(prior later :List (Call Spec State)) (call :Call Spec State),calls=prior++call::later ∧
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later after ∧
      ∃tail,after.2=call.after.2++tail ∧Nonempty (Staged configuration created credential request candidate digest signature call) :=by
  obtain ⟨prior,later,call,middle,split,beforePath,called,suffix,emitted,block⟩:=
    RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.stage configuration created credential actual empty
      (Stage.sign request candidate digest signature) present
  have invariant:=RegistrationNativePlatformPublicAdapterSourceCommonReceipt.invariant_path configuration created credential beforePath held
  obtain ⟨tail,afterLog⟩:=path_log configuration created credential suffix
  refine ⟨prior,later,call,split,beforePath,called,suffix,tail,afterLog,?_⟩
  rcases call with ⟨query,current,value,next⟩
  obtain ⟨packet,output⟩:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut configuration created credential query current (value,next) called
  let incoming:=current.2++[RegistrationNativePlatformPublicAdapterSourceEvents.Event.opened query (physical current.1.1 current.1.2)]
  let selected:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query current.1.1 current.1.2
  let augmented:=RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query current.1 incoming
  let answered:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer selected
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.project selected augmented packet)
  change (value,next)=(answered.1,(answered.2,packet.val.2++[RegistrationNativePlatformPublicAdapterSourceEvents.Event.closed query
    (.ok (answered.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical answered.2.1 answered.2.2)))
    (physical answered.2.1 answered.2.2).backend])) at output
  obtain ⟨fresh,logEq⟩:=RegistrationNativePlatformPublicAdapterSigningHistory.suffix configuration created credential query current.1 incoming packet.val packet.property
  have sameReply:value=answered.1:=congrArg Prod.fst output
  have samePrivate:next.1=answered.2:=congrArg (fun result=>result.2.1) output
  have sameStore:physical answered.2.1 answered.2.2=physical next.1.1 next.1.2:=
    congrArg (fun state:RegistrationNativePlatformExtractedSdkPublic.State Private=>physical state.1 state.2) samePrivate.symm
  have packetBlock:=congrArg (fun result=>result.2.2) output
  rw [logEq,sameStore,←sameReply] at packetBlock
  have listEq :(incoming++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)++
      [RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed configuration created credential
        (⟨query,current,value,next⟩:Call Spec State)]=
      (incoming++fresh.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)++
      [RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed configuration created credential
        (⟨query,current,value,next⟩:Call Spec State)]:=by
    simpa only [incoming,RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.opened,
      RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.closed,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
      using block.symm.trans packetBlock
  have middleEq:middle=fresh:=(List.map_injective_iff.mpr
    (fun _ _ same=>RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage.inj same))
      (List.append_cancel_left (List.append_cancel_right listEq))
  subst middle
  have history:current.1.1.1.1.server.world.world.2=receipts (stages incoming):=by
    simpa only [incoming,RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,List.append_nil] using invariant.1
  obtain ⟨handle,data,queryEq⟩:=RegistrationNativePlatformPublicAdapterServerSigning.server_build configuration created credential query current.1 incoming
    packet.val packet.property history fresh logEq request candidate digest signature emitted role
  subst query
  obtain ⟨token,nativeCurrent,initial,hashed,pin,availability,application,tokenFound,taken,started,recordPath,recordCut,recorded,payloadEq,key⟩:=
    RegistrationNativePlatformPublicAdapterBuildCallbackRecordStage.sample configuration created credential handle data current.1 incoming
      packet.val packet.property fresh logEq request candidate digest signature emitted
  have nativeEq:=congrArg (fun state:RegistrationNativePlatformExtractedSdkPublic.State Private=>state.1) samePrivate.symm
  have cacheEq:=congrArg (fun state:RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source=>RegistrationNativeWorldCache.cache state.1.1) nativeEq
  exact ⟨⟨handle,data,rfl,fresh,block,token,nativeCurrent,initial,hashed,pin,availability,application,
    tokenFound,taken,started,recordPath,cacheEq ▸recordCut,recorded,emitted,payloadEq,key⟩⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEarlierBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEarlierBuild.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEarlierBuild.stage
