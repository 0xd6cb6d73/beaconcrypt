-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCallbackSpan
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan
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

local notation "Stage"=>RegistrationNativePlatformPublicAdapterSourceTrace.Stage
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages
local notation "flag"=>RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag configuration.view credential.publicKey
local notation "model"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential
local notation "State"=>RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential

open RegistrationNativeStageTrace (Call Path Executed)
local notation "implementation"=>RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential
local notation "Spec"=>RegistrationNativePlatformPublicAdapterLowSpec.Spec

noncomputable def opened (call :Call Spec State) :Event n KemSK R P :=
  .opened call.query (physical call.before.1.1 call.before.1.2)

noncomputable def closed (call :Call Spec State) :Event n KemSK R P :=
  .closed call.query (.ok (call.reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical call.after.1.1 call.after.1.2)))
    (physical call.after.1.1 call.after.1.2).backend

def tag :Event n KemSK R P→Nat
  | .stage _=>0
  | .opened _ _=>1
  | .closed _ _ _=>2

theorem block (call :Call Spec State) (executed :Executed implementation call) :
    ∃middle :List Stage,call.after.2=call.before.2++opened configuration created credential call::
      (middle.map Event.stage++[closed configuration created credential call]) :=by
  rcases call with ⟨query,before,reply,after⟩
  obtain ⟨packet,output⟩:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut configuration created credential query before (reply,after) executed
  let prior:=before.2++[Event.opened query (physical before.1.1 before.1.2)]
  let selected:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1.1 before.1.2
  let augmented:=RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before.1 prior
  let answer:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer selected (RegistrationNativePlatformPublicAdapterLoggedRuntime.project selected augmented packet)
  change (reply,after)=(answer.1,(answer.2,packet.val.2++[Event.closed query
    (.ok (answer.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical answer.2.1 answer.2.2)))
    (physical answer.2.1 answer.2.2).backend])) at output
  obtain ⟨middle,emitted⟩:=RegistrationNativePlatformPublicAdapterSigningHistory.suffix configuration created credential query before.1 prior packet.val packet.property
  have sameReply:reply=answer.1:=congrArg Prod.fst output
  have samePrivate:after.1=answer.2:=congrArg (fun result=>result.2.1) output
  have sameStore:physical answer.2.1 answer.2.2=physical after.1.1 after.1.2:=
    congrArg (fun current:RegistrationNativePlatformExtractedSdkPublic.State Private=>physical current.1 current.2) samePrivate.symm
  have sameLog:=congrArg (fun result=>result.2.2) output
  rw [emitted,sameStore,←sameReply] at sameLog
  exact ⟨middle,by simpa only [prior,opened,closed,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using sameLog⟩

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem readback (call :Call Spec State) (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (beforeStore :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (reply :RustM (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R))
    (afterBackend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (atOpen :opened configuration created credential call=Event.opened query beforeStore)
    (atClose :closed configuration created credential call=Event.closed query reply afterBackend) :
    call.query=query ∧physical call.before.1.1 call.before.1.2=beforeStore ∧
      HEq (RustM.ok (call.reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical call.after.1.1 call.after.1.2))) reply ∧
      (physical call.after.1.1 call.after.1.2).backend=afterBackend :=by
  rcases call with ⟨actualQuery,current,value,next⟩
  dsimp only [opened] at atOpen
  injection atOpen with sameQuery sameBefore
  subst query
  dsimp only [closed] at atClose
  injection atClose with _sameQuery sameReply sameBackend
  exact ⟨rfl,sameBefore,heq_of_eq sameReply,sameBackend⟩

private theorem tagged_block (call :Call Spec State) (executed :Executed implementation call) :
    ∃middle :Log,(∀item∈middle,tag item=0) ∧call.after.2=call.before.2++opened configuration created credential call::
      (middle++[closed configuration created credential call]) :=by
  obtain ⟨middle,emitted⟩:=block configuration created credential call executed
  refine ⟨middle.map Event.stage,?_,emitted⟩
  intro item present
  obtain ⟨stage,_member,same⟩:=List.mem_map.mp present
  cases same
  rfl

theorem span {before after :State} {calls :List (Call Spec State)} (actual :Path implementation before calls after)
    (leading :Log) (middle :List Stage) (trailing :Log) (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (sourceBefore :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (reply :RustM (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R))
    (sourceBackend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (observed :after.2=before.2++(leading++Event.opened query sourceBefore::(middle.map Event.stage++Event.closed query reply sourceBackend::trailing))) :
    ∃(prior later :List (Call Spec State)) (call :Call Spec State),calls=prior++call::later ∧
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later after ∧
      call.before.2=before.2++leading ∧call.query=query ∧physical call.before.1.1 call.before.1.2=sourceBefore ∧
      HEq (RustM.ok (call.reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical call.after.1.1 call.after.1.2))) reply ∧
      (physical call.after.1.1 call.after.1.2).backend=sourceBackend ∧
      opened configuration created credential call=Event.opened query sourceBefore ∧
      closed configuration created credential call=Event.closed query reply sourceBackend ∧
      call.after.2=before.2++(leading++Event.opened query sourceBefore::(middle.map Event.stage++[Event.closed query reply sourceBackend])) :=by
  have middleTags :∀item∈middle.map (Event.stage (n:=n) (KemSK:=KemSK) (R:=R) (P:=P)),tag item=0:=by
    intro item present
    obtain ⟨stage,_member,same⟩:=List.mem_map.mp present
    cases same
    rfl
  obtain ⟨prior,later,call,callsEq,previousPath,executed,suffix,atBefore,atOpen,atClose,atAfter⟩:=
    RegistrationNativePlatformPublicAdapterCallbackSpan.span tag implementation Prod.snd
      (opened configuration created credential) (closed configuration created credential) (tagged_block configuration created credential)
      (fun _=>rfl) actual leading (middle.map Event.stage) trailing (Event.opened query sourceBefore)
      (Event.closed query reply sourceBackend) rfl rfl middleTags observed
  obtain ⟨sameQuery,sameSource,sameReply,sameBackend⟩:=readback configuration created credential call query sourceBefore reply sourceBackend atOpen atClose
  exact ⟨prior,later,call,callsEq,previousPath,executed,suffix,atBefore,sameQuery,sameSource,sameReply,sameBackend,atOpen,atClose,atAfter⟩

theorem program (work :OracleComp Spec Value) (before :State) (result :Value×State)
    (supported :result∈support ((simulateQ implementation work).run before))
    (leading :Log) (middle :List Stage) (trailing :Log) (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (sourceBefore :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P)
    (reply :RustM (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R))
    (sourceBackend :RegistrationNativePlatformSdkReification.Backend n KemSK×P)
    (observed :result.2.2=before.2++(leading++Event.opened query sourceBefore::(middle.map Event.stage++Event.closed query reply sourceBackend::trailing))) :
    ∃(prior later :List (Call Spec State)) (call :Call Spec State),
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later result.2 ∧
      call.before.2=before.2++leading ∧call.query=query ∧physical call.before.1.1 call.before.1.2=sourceBefore ∧
      HEq (RustM.ok (call.reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical call.after.1.1 call.after.1.2))) reply ∧
      (physical call.after.1.1 call.after.1.2).backend=sourceBackend ∧
      opened configuration created credential call=Event.opened query sourceBefore ∧
      closed configuration created credential call=Event.closed query reply sourceBackend ∧
      call.after.2=before.2++(leading++Event.opened query sourceBefore::(middle.map Event.stage++[Event.closed query reply sourceBackend])) :=by
  obtain ⟨calls,actual⟩:=RegistrationNativePlatformPublicAdapterSourceLogCrossing.path implementation work before result supported
  obtain ⟨prior,later,call,_callsEq,previousPath,executed,suffix,atBefore,readback⟩:=
    span configuration created credential actual leading middle trailing query sourceBefore reply sourceBackend observed
  exact ⟨prior,later,call,previousPath,executed,suffix,atBefore,readback⟩

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
private theorem stage_in_block (call :Call Spec State) (middle :List Stage) (wanted :Stage)
    (present :Event.stage wanted∈opened configuration created credential call::(middle.map Event.stage++[closed configuration created credential call])) :
    wanted∈middle :=by
  simp only [opened,closed,List.mem_cons,List.mem_append,reduceCtorEq,false_or,or_false,List.mem_map,List.not_mem_nil] at present
  obtain ⟨actual,member,same⟩:=present
  cases same
  exact member

private theorem stage_new {before after :State} {calls :List (Call Spec State)} (actual :Path implementation before calls after)
    (emitted :Log) (observed :after.2=before.2++emitted) (wanted :Stage) (present :Event.stage wanted∈emitted) :
    ∃(prior later :List (Call Spec State)) (call :Call Spec State) (middle :List Stage),calls=prior++call::later ∧
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later after ∧
      wanted∈middle ∧call.after.2=call.before.2++opened configuration created credential call::(middle.map Event.stage++[closed configuration created credential call]) :=by
  induction actual generalizing emitted with
  | nil current=>
    have empty:emitted=[]:=List.append_cancel_left (observed.symm.trans (List.append_nil _).symm)
    rw [empty] at present
    cases present
  | cons call called rest last following ih=>
    obtain ⟨middle,blockEq⟩:=block configuration created credential call called
    obtain ⟨followingLog,kept⟩:=RegistrationNativePlatformPublicAdapterCallbackSpan.appends tag implementation Prod.snd
      (opened configuration created credential) (closed configuration created credential) (tagged_block configuration created credential) following
    have combined:last.2=call.before.2++((opened configuration created credential call::(middle.map Event.stage++[closed configuration created credential call]))++followingLog):=by
      rw [kept,blockEq,List.append_assoc]
    have same:emitted=(opened configuration created credential call::(middle.map Event.stage++[closed configuration created credential call]))++followingLog:=
      List.append_cancel_left (observed.symm.trans combined)
    rw [same] at present
    rcases List.mem_append.mp present with now|later
    · exact ⟨[],rest,call,middle,rfl,.nil _,called,following,stage_in_block configuration created credential call middle wanted now,blockEq⟩
    · obtain ⟨prior,laterCalls,found,insideStages,callsEq,previousPath,executed,afterPath,member,blockAt⟩:=ih followingLog kept later
      exact ⟨call::prior,laterCalls,found,insideStages,by rw [callsEq];rfl,.cons call called _ _ previousPath,executed,afterPath,member,blockAt⟩

/- Repeated equal-valued stages still have a genuine actual earlier callback from the same path. -/
theorem stage {before after :State} {calls :List (Call Spec State)} (actual :Path implementation before calls after)
    (empty :before.2=[]) (wanted :Stage) (present :Event.stage wanted∈after.2) :
    ∃(prior later :List (Call Spec State)) (call :Call Spec State) (middle :List Stage),calls=prior++call::later ∧
      Path implementation before prior call.before ∧Executed implementation call ∧Path implementation call.after later after ∧
      wanted∈middle ∧call.after.2=call.before.2++opened configuration created credential call::(middle.map Event.stage++[closed configuration created credential call]) :=by
  exact stage_new configuration created credential actual after.2 (by rw [empty,List.nil_append]) wanted present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.block

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.span

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCallbackSpan.stage
