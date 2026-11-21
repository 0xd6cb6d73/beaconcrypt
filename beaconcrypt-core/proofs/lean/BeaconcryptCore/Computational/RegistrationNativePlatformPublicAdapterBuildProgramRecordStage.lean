-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramStageCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRecordAnchor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildAdCut
import BeaconcryptCore.Refinement.AdapterPublicServerAdHash
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

omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem log_erasure_support {S T Value : Type}
    (left : StateT (S × T) (StateT P ProbComp) Value)
    (right : StateT S (StateT P ProbComp) Value)
    (erases : ∀ before, Prod.map id Prod.fst <$> left.run before = right.run before.1)
    (before : S × T) (previous : P) (result : (Value × (S × T)) × P)
    (supported : result ∈ support ((left.run before).run previous)) :
    ((result.1.1, result.1.2.1), result.2) ∈ support ((right.run before.1).run previous) := by
  have same := congrArg (fun work => work.run previous) (erases before)
  rw [StateT.run_map] at same
  rw [← same, support_map]
  exact ⟨result, supported, rfl⟩

attribute [local irreducible] RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler

/-- Erasure of only the private hash/log cuts retains the actual shared native hash callback and its exact platform support. -/
private theorem physical_ad_cut (self : beaconcrypt_public_wrapper.server.Server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (initial : registration.ServerInitialKdf)
    (first : (Cut×Events)×P)
    (ad : RegistrationNativePlatformPublicAdapterBuildAdProgramCut.HashCut actual token self.control initial first)
    (cache : CtxRomAuth.CtxRO.QueryCache)
    (extension : RegistrationNativeWorldCache.cache ad.afterHash.1.1.1 ≤ cache) :
    Nonempty (RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)
      coins token.registration self.control ad.pin ad.availability ad.application initial cache) := by
  have nested : ((.ok ad.digest, ad.afterHash.1), ad.afterHash.2) ∈ support
      (((interpreter (.inl (.inr ad.request))).run ad.beforeHash.1).run ad.beforeHash.2) :=
    (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp ad.called
  have hashLeaf : ((.ok ad.digest, ad.afterHash.1.1), ad.afterHash.2) ∈ support
      (((RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer
        view originalLocal original previousCrypto previousChildren fallback (.inl (.inr ad.request))).run ad.beforeHash.1.1).run ad.beforeHash.2) := by
    apply log_erasure_support (interpreter (.inl (.inr ad.request)))
      (RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer
        view originalLocal original previousCrypto previousChildren fallback (.inl (.inr ad.request)))
      _ ad.beforeHash.1 ad.beforeHash.2 ((.ok ad.digest, ad.afterHash.1), ad.afterHash.2) nested
    intro current
    exact RegistrationNativePlatformPublicAdapterBuildProgramStages.query_native_erasure
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage coins setup codec keyView failure allocation helper erased sign writer
      view originalLocal original previousCrypto previousChildren fallback (.inl (.inr ad.request)) current
  have hash_eq : RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler coins setup codec keyView failure allocation helper erased sign writer
      view originalLocal original previousCrypto previousChildren fallback (.inl (.inr ad.request)) =
      AdapterPublicServerCutPin.hash coins sign ad.request := by
    unfold RegistrationNativePlatformPublicAdapterBuildSource.nativeHandler RegistrationNativePlatformPublicAdapterBuildProgram.handler
    rfl
  rw [hash_eq, AdapterPublicServerAdHash.hash_run, StateT.run_map, support_map] at hashLeaf
  obtain ⟨raw, called, same⟩ := hashLeaf
  have replySame := RustM.ok.inj (congrArg (fun result => result.1.1) same)
  have rawCache : RegistrationNativeWorldCache.cache raw.1.2 = RegistrationNativeWorldCache.cache ad.afterHash.1.1.1 :=
    congrArg (fun result => RegistrationNativeWorldCache.cache result.1.2.1) same
  rw [AdapterPublicServerCutPin.outgoing, AdapterPublicServerLocalLens.local_run, StateT.run_map, support_map] at called
  obtain ⟨world, hashed, worldSame⟩ := called
  have digestSame : world.1.1 = raw.1.1 := congrArg (fun result => result.1.1) worldSame
  have worldCache : world.1.2.world.1.primitive.2 = RegistrationNativeWorldCache.cache raw.1.2 :=
    congrArg (fun result : (CtxRomAuth.CtxDigest × Native) × P => RegistrationNativeWorldCache.cache result.1.2) worldSame
  rw [AdapterPublicServerAdHash.hash_outgoing] at hashed
  have resumed : ad.pending.resume (.Some (RegistrationAuthenticationShared.digestArray world.1.1)) = .ok (.Ok initial) := by
    rw [digestSame, replySame]
    exact ad.resumed
  have retained : world.1.2.world.1.primitive.2 ≤ cache := by
    rw [worldCache, rawCache]
    exact extension
  exact ⟨RegistrationNativePlatformPublicAdapterBuildAdCut.of_hash coins token.registration self.control ad.pin ad.availability
    ad.application initial cache ad.pending ad.beforeHash.1.1.1.server.world world.1.2 ad.beforeHash.2 world.2
    ad.request world.1.1 ad.selected ad.requested resumed hashed retained⟩

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
      BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission self.control pin availability token.registration.agreement application initial ∧
      Nonempty (RegistrationNativePlatformPublicAdapterBuildAdCut.Cut (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)
        coins token.registration self.control pin availability application initial
        (RegistrationNativeWorldCache.cache result.1.1.2.1)) ∧
      RegistrationServerRecordExecutor.Path initial hashed ∧
      RegistrationNativePlatformSourceFinishContents.RecordCut (n:=n) coins setup wire keyView failure allocation erased rawAllocation serializer
        initial hashed (RegistrationNativeWorldCache.cache result.1.1.2.1) ∧
      Stage.firstRecord initial (.ok (.Ok hashed))∈suffix ∧
      payload=RegistrationSigningTrace.Command.payload (.server hashed) ∧
      request.public_key=hashed.binding.server_pin.public_key :=by
  obtain ⟨leading,trailing,call,beforePath,called,afterPath,current,initial,queryEq,controlEq,_admitted,ad,between,hashPath,emitted,logEq,seen⟩:=
    RegistrationNativePlatformPublicAdapterBuildProgramStageCut.call_with_ad coins setup codec keyView failure allocation helper erased sign writer view originalLocal original previousCrypto previousChildren fallback
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
  have hashToComplete := path_cache coins setup wire keyView failure allocation rawAllocation serializer erased sign writer view originalLocal original previousCrypto previousChildren fallback hashPath
  have completeExtension := RegistrationNativePlatformPublicAdapterBuildCacheFrame.complete coins setup codec keyView failure allocation helper erased sign writer
    RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage original current initial callBefore.1 callBefore.2 _ completeCalled
  have hashToFinal := hashToComplete.trans (completeExtension.trans extension)
  obtain ⟨adCut⟩ := physical_ad_cut coins setup wire keyView failure allocation rawAllocation serializer erased sign writer view originalLocal original previousCrypto previousChildren fallback
    self token initial _ ad (RegistrationNativeWorldCache.cache result.1.1.2.1) hashToFinal
  obtain ⟨selectedDigest,adResumed,_cached⟩ := RegistrationNativePlatformPublicAdapterBuildAdCut.cached
    coins token.registration self.control ad.pin ad.availability ad.application initial _ adCut
  have started : RegistrationAd.ServerAdmission self.control ad.pin ad.availability token.registration.agreement ad.application initial :=
    ⟨adCut.pendingAd,RegistrationAuthenticationShared.digestArray selectedDigest,adCut.selected,adResumed⟩
  exact ⟨initial,hashed,ad.pin,ad.availability,ad.application,started,⟨adCut⟩,recordPath,
    ⟨recordBefore,recordAfter,recorded,anchor.trans extension⟩,member,payloadEq,key⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgramRecordStage.sample
