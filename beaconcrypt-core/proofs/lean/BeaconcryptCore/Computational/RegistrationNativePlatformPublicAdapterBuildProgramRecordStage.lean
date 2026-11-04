-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor
/-! A given emitted server-sign operation in the same complete Builder callback determines its actual source token initializer and successful first-record stage. The concrete first-record cut is anchored at that callback's final cache, even when later source publication or installation refuses. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildTrace (Publication Word)
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
abbrev Spec := RegistrationNativePlatformPublicAdapterBuildProgram.Spec
variable {Log : Type}
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
local notation "codec"=>RegistrationNativeWire.ledgerCodec wire
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT P ProbComp))
variable (rawAllocation :alloc.vec.Vec U8→Usize→StateT P ProbComp (RustM (core.result.Result Unit E)))
variable (serializer :U64→U64→Std.Array (Slice U8) 3#usize→Slice U8→StateT P ProbComp (RustM (Usize×Slice U8)))
local notation "helper"=>AdapterRecordRawBytes.helper rawAllocation serializer
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT P ProbComp
local notation "SourceM" => StateT Cut Base

variable {R A :Type}
local notation "Events" => RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

variable (originalLocal :LocalOperations (RustT (StateT P ProbComp))) (original :ContainerOperations (RustT (StateT P ProbComp)))
variable (previousCrypto :CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (previousChildren :ChildOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT P ProbComp))))
variable (fallback :registration.MldsaSigningRequest→StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp) RegistrationSigningShared.SignReply)

local notation "actual"=>RegistrationNativePlatformPublicAdapterBuildProgramStageCut.actual
  (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
local notation "interpreter"=>RegistrationNativePlatformPublicAdapterBuildProgramStageCut.interpreter
  (R:=R) coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback

private theorem path_log {before after :(Cut×Events)×P}
    {calls :List (RegistrationNativeStageTrace.Call Spec ((Cut×Events)×P))}
    (path :RegistrationNativeStageTrace.Path actual before calls after) :
    ∃emitted,after.1.2=before.1.2++emitted :=by
  induction path with
  | nil=>exact ⟨[],(List.append_nil _).symm⟩
  | cons call called rest last following ih=>
    have nested :((call.reply,call.after.1),call.after.2)∈support (((interpreter call.query).run call.before.1).run call.before.2):=
      (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp called
    obtain ⟨middle,first⟩:=RegistrationNativePlatformPublicAdapterBuildSigningDelta.query_delta coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
      call.query call.before.1 call.before.2 _ nested
    obtain ⟨suffix,later⟩:=ih
    exact ⟨middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage++suffix,
      later.trans (by rw [first,List.append_assoc])⟩

private theorem path_cache {before after :(Cut×Events)×P}
    {calls :List (RegistrationNativeStageTrace.Call Spec ((Cut×Events)×P))}
    (path :RegistrationNativeStageTrace.Path actual before calls after) :
    RegistrationNativeWorldCache.cache before.1.1.1≤RegistrationNativeWorldCache.cache after.1.1.1 :=by
  induction path with
  | nil=>exact le_refl _
  | cons call called rest last following ih=>
    have nested :((call.reply,call.after.1),call.after.2)∈support (((interpreter call.query).run call.before.1).run call.before.2):=
      (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp called
    have extension:=RegistrationNativePlatformPublicAdapterBuildCacheFrame.query coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage call.query call.before.1 call.before.2 _ nested
    exact extension.trans ih

theorem sample (self :beaconcrypt_public_wrapper.server.Server) (token :beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data :core.option.Option (Slice U8)) (before :Cut) (previous :P) (prior :Events)
    (result :(((Word×Cut)×P)×Events))
    (supported :result∈support (RegistrationNativePlatformPublicAdapterBuildProgramStages.sample
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback self token data before previous prior))
    (suffix :List Stage) (observed :result.2=prior++suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage)
    (request :registration.MldsaSigningRequest) (payload :MldsaTranscriptAuth.Payload)
    (digest :CtxRomAuth.CtxDigest) (signature :RegistrationSigningShared.SignReply)
    (present :Stage.sign request payload digest signature∈suffix) :
    ∃initial hashed pin availability application,
      registration.begin_server_completion self.control pin availability token.registration.agreement application=.ok (.Ok initial) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup wire keyView failure allocation erased rawAllocation serializer
        initial hashed (RegistrationNativeWorldCache.cache result.1.1.2.1) ∧
      Stage.firstRecord initial (.ok (.Ok hashed))∈suffix ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key :=by
  obtain ⟨leading,trailing,call,beforePath,called,afterPath,current,initial,queryEq,controlEq,admitted,emitted,logEq,seen⟩:=
    RegistrationNativePlatformPublicAdapterBuildProgramStageCut.call coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
      self token data before previous prior result supported suffix observed request payload digest signature present
  obtain ⟨query,callBefore,reply,callAfter⟩:=call
  dsimp only at queryEq
  subst query
  have completeCalled :((reply,callAfter.1),callAfter.2)∈support
      (((RegistrationNativePlatformPublicAdapterBuildProgramStages.nativeComplete
        RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer original current initial).run callBefore.1).run callBefore.2):=
    (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp called
  obtain ⟨hashed,firstState,firstPlatform,hashRequest,hashState,hashPlatform,signState,signPlatform,
    _firstCalled,_requested,_hashCalled,_signCalled,payloadEq,key,exactEvents⟩:=
    RegistrationNativePlatformPublicAdapterBuildProgramStageCut.complete_cut coins setup codec keyView failure allocation helper erased sign writer original
      current initial callBefore.1.1 callBefore.2 callBefore.1.2 emitted _ completeCalled logEq request payload digest signature seen
  have firstEvent :RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.firstRecord initial (.ok (.Ok hashed)))∈emitted:=by
    rw [exactEvents]
    exact List.mem_cons_self
  obtain ⟨recordPath,recordCut⟩:=RegistrationNativePlatformPublicAdapterBuildRecordAnchor.complete coins setup wire keyView failure allocation erased rawAllocation serializer sign writer
    RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage
    (fun _ _ same=>RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage.inj same)
    original current initial hashed callBefore.1.1 callBefore.2 callBefore.1.2 emitted _ completeCalled logEq firstEvent
  have extension:=path_cache coins setup wire keyView failure allocation rawAllocation serializer erased sign writer view originalLocal original previousCrypto previousChildren fallback afterPath
  obtain ⟨recordBefore,recordAfter,recorded,anchor⟩:=recordCut
  obtain ⟨beforeEvents,beforeLog⟩:=path_log coins setup wire keyView failure allocation rawAllocation serializer erased sign writer view originalLocal original previousCrypto previousChildren fallback beforePath
  obtain ⟨afterEvents,afterLog⟩:=path_log coins setup wire keyView failure allocation rawAllocation serializer erased sign writer view originalLocal original previousCrypto previousChildren fallback afterPath
  have total :result.2=prior++(beforeEvents++emitted++afterEvents):=by
    rw [afterLog,logEq,beforeLog]
    simp only [List.append_assoc]
  have suffixEq:suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage=beforeEvents++emitted++afterEvents:=
    List.append_cancel_left (observed.symm.trans total)
  have firstIn :(RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage (Stage.firstRecord initial (.ok (.Ok hashed))) :RegistrationNativePlatformPublicAdapterSourceEvents.Event n KemSK R P)∈
      suffix.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage:=by
    rw [suffixEq]
    exact List.mem_append_left _ (List.mem_append_right _ firstEvent)
  obtain ⟨selected,member,same⟩:=List.mem_map.mp firstIn
  have selectedEq:=RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage.inj same
  cases selectedEq
  obtain ⟨pin,availability,application,started⟩:=admitted
  exact ⟨initial,hashed,pin,availability,application,started,recordPath,
    ⟨recordBefore,recordAfter,recorded,anchor.trans extension⟩,member,payloadEq,key⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage.sample
