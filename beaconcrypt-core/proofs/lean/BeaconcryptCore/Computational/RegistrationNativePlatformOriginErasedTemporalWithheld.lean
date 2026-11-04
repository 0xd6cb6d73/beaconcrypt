-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedEncoderRefusal
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget
import BeaconcryptCore.Computational.PqxdhDeploymentCausalCoverage
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedTemporalWithheld
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Reader Response E Failure A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "Runtime" => CborRawRecordFlat.NativeState n E
local notation "Whole" => PqxdhDeploymentSecrecy.Ledger × Runtime
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "native" => RegistrationNativePlatformGatedRecordFlat.native service env reserve codec route
variable (serverKeyId : U64) (bounds : FreshBounds)
local notation "full" => RegistrationNativePlatformGatedRecordFlat.full service env reserve setup.source.crypto codec route serverKeyId bounds

private theorem native_program_step (work : OracleComp Spec A) (before : Runtime)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (result : A × Runtime)
    (supported : result∈support ((simulateQ native work).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 result.2.1.2 := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_program,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ before.1.2 safe before.2 inner called

private theorem native_path {before after : Runtime} {calls : List (Call Spec Runtime)}
    (path : Path native before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) :
    PqxdhRecordLiftProtocolHistory.Step before.1.2 after.1.2 := by
  induction path with
  | nil state => exact PqxdhRecordLiftProtocolHistory.step_refl _ safe
  | cons call called rest last following ih =>
    have step := native_program_step modes replace setup codec route env reserve (Spec.query call.query) call.before safe
      (call.reply,call.after) (by simpa only [simulateQ_spec_query,Executed] using called)
    exact PqxdhRecordFactsOriginControl.step_trans _ _ _ step (ih step.1)

private theorem full_step (query : FullSpec.Domain) (before : Whole)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) (result : FullSpec.Range query × Whole)
    (supported : result∈support ((full query).run before)) :
    PqxdhRecordLiftProtocolHistory.Step before.2.1.2 result.2.2.1.2 := by
  change result∈support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact native_program_step modes replace setup codec route env reserve _ before.2 safe inner called

private theorem full_path {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) :
    PqxdhRecordLiftProtocolHistory.Step before.2.1.2 after.2.1.2 := by
  induction path with
  | nil state => exact PqxdhRecordLiftProtocolHistory.step_refl _ safe
  | cons call called rest last following ih =>
    have step := full_step modes replace setup codec route env reserve serverKeyId bounds call.query call.before safe
      (call.reply,call.after) called
    exact PqxdhRecordFactsOriginControl.step_trans _ _ _ step (ih step.1)

private theorem full_record (query : FullSpec.Domain) (before : Whole) (result : FullSpec.Range query × Whole)
    (supported : result∈support ((full query).run before)) :
    result.2.1.transcript=before.1.transcript++[⟨query,result.1⟩] := by
  change result∈support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  have projected : inner.1∈support ((simulateQ native
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run before.1)).run' before.2) := by
    rw [StateT.run'_eq,support_map]
    exact ⟨inner,called,rfl⟩
  have free := support_simulateQ_run'_subset native _ before.2 projected
  exact PqxdhDeploymentCausalCoverage.ledger_records setup.source.crypto codec serverKeyId bounds query before.1 inner.1 free

private theorem transcript {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) :
    after.1.transcript=before.1.transcript++calls.map (fun call => (⟨call.query,call.reply⟩ : Entry)) := by
  induction path with
  | nil state => exact (List.append_nil _).symm
  | cons call called rest last following ih =>
    have recorded := full_record modes replace setup codec route env reserve serverKeyId bounds call.query call.before (call.reply,call.after) called
    rw [ih,recorded,List.map_cons,List.append_assoc]
    rfl

private theorem first_crossing {Q S : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT S ProbComp)) (present : S → Prop)
    {before after : S} {calls : List (Call spec S)} (path : Path implementation before calls after)
    (absent : ¬present before) (found : present after) :
    ∃ (call : Call spec S),∃leading trailing,calls=leading++call::trailing ∧
      Path implementation before leading call.before ∧ Executed implementation call ∧
      Path implementation call.after trailing after ∧ ¬present call.before ∧ present call.after := by
  classical
  induction path with
  | nil state => exact (absent found).elim
  | cons call called rest last following ih =>
    by_cases entered : present call.after
    · exact ⟨call,[],rest,rfl,.nil _,called,following,absent,entered⟩
    · obtain ⟨target,leading,trailing,split,earlier,reached,later,notYet,inserted⟩ := ih entered found
      exact ⟨target,call::leading,trailing,by rw [split];rfl,.cons call called leading target.before earlier,
        reached,later,notYet,inserted⟩

private theorem outer_sending (query : FullSpec.Domain) (ledger : PqxdhDeploymentSecrecy.Ledger) (before : Runtime)
    (result : (FullSpec.Range query × PqxdhDeploymentSecrecy.Ledger) × (Runtime × List (Call Spec Runtime)))
    (supported : result∈support ((simulateQ (RegistrationNativeStageTrace.handler native)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run ledger)).run (before,[])))
    (inner : Call Spec Runtime) (member : inner∈result.2.2)
    (sending : (∃keyId plaintext,inner.query=.inr (.serverSend keyId plaintext)) ∨
      (∃owner plaintext,inner.query=.inr (.beaconSend owner plaintext))) :
    RegistrationNativePlatformOriginLedgerSendSyntax.Sending query := by
  rcases query with forwarded | (⟨handle,left,right⟩ | ⟨handle,length⟩)
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward,simulateQ_map,simulateQ_spec_query,StateT.run_map] at supported
    simp only [RegistrationNativeStageTrace.handler,StateT.run,Functor.map_map,support_map] at supported
    obtain ⟨actual,_called,same⟩ := supported
    have callsSame := congrArg (fun value => value.2.2) same
    rw [←callsSame] at member
    simp only [List.nil_append,List.mem_singleton] at member
    have queryEq := congrArg (fun call : Call Spec Runtime => call.query) member
    change inner.query=forwarded at queryEq
    rw [←queryEq]
    rcases sending with ⟨keyId,plaintext,eq⟩ | ⟨owner,plaintext,eq⟩
    · rw [eq];exact .server keyId plaintext
    · rw [eq];exact .beacon owner plaintext
  · exact .test handle left right
  · exact .fresh handle length

private theorem sending_budget (query : FullSpec.Domain) (sending : RegistrationNativePlatformOriginLedgerSendSyntax.Sending query) :
    RegistrationNativePlatformOriginSendCallbackBudget.Sending query := by
  cases sending <;> simp [RegistrationNativePlatformOriginSendCallbackBudget.Sending,PqxdhDeploymentInterface.queryClass]

private theorem unpublished_none (query : Spec.Domain) (reply : Spec.Range query)
    (sending : (∃keyId plaintext,query=.inr (.serverSend keyId plaintext)) ∨
      (∃owner plaintext,query=.inr (.beaconSend owner plaintext)))
    (unpublished : (⟨.inl query,reply⟩ : Entry).published=none) :
    RegistrationNativePlatformOriginLedgerSendReply.nativeReply query reply=none := by
  rcases sending with ⟨keyId,plaintext,rfl⟩ | ⟨owner,plaintext,rfl⟩
  all_goals cases reply <;> first | rfl | cases unpublished

include ideal readback in
/-- On the actual erased full-ledger path, a retained seal with no earlier physical counterpart publication was acquired by an earlier send-producing outer callback whose original public reply was absent. The same prefix, suffix and full reached states remain literal. -/
theorem outer_refused (initial : Runtime) (before final : Whole)
    (leading : List (Call FullSpec Whole)) (remaining : List (Call FullSpec Whole))
    (prefixPath : Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) leading before)
    (futurePath : Path full before remaining final)
    (safe : PqxdhRecordLiftProtocolHistory.Safe initial.1.2)
    (label : Label n) (entry : CtxSuccessfulSeal) (receiver : Handle) (frame : RawCtxReceive.DecodedFrame)
    (empty : (initial.2.keys label).1.successfulSeals=[])
    (present : entry∈(before.2.2.keys label).1.successfulSeals)
    (matched : PqxdhRecordFactsOriginReplay.Matches frame entry)
    (direction : label.direction = !PqxdhRecordFactsOriginHandles.handleDirection receiver)
    (unpublished : ∀sender,PqxdhRecordLiftIdeal.Counterpart (handleSlot final.2.1.2) label.slot receiver sender →
      ¬PqxdhRecordLiftIdeal.PublishedBefore codec before.1.transcript sender frame) :
    ∃ (outerCall : Call FullSpec Whole),∃pre post,
      leading=pre++outerCall::post ∧ Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) pre outerCall.before ∧
      Executed full outerCall ∧ Path full outerCall.after post before ∧
      RegistrationNativePlatformOriginSendCallbackBudget.Sending outerCall.query ∧
      entry∉(outerCall.before.2.2.keys label).1.successfulSeals ∧
      entry∈(outerCall.after.2.2.keys label).1.successfulSeals ∧
      RegistrationNativePlatformOriginLedgerSendSyntax.reply outerCall.query outerCall.reply=none := by
  have absent : entry∉(initial.2.keys label).1.successfulSeals := by rw [empty];exact List.not_mem_nil
  obtain ⟨outerCall,pre,post,split,earlier,called,later,notYet,inserted⟩ := first_crossing full
    (fun current : Whole => entry∈(current.2.2.keys label).1.successfulSeals) prefixPath absent present
  have advanced := full_path modes replace setup codec route env reserve serverKeyId bounds earlier safe
  have logged := called
  change (outerCall.reply,outerCall.after)∈support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ native ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds outerCall.query).run outerCall.before.1)).run outerCall.before.2) at logged
  rw [←RegistrationNativeStageTrace.erase native _ (outerCall.before.2,[]),Functor.map_map,support_map] at logged
  obtain ⟨journal,journalCalled,journalSame⟩ := logged
  have runtimeEq : journal.2.1=outerCall.after.2 := congrArg (fun value => value.2.2) journalSame
  have replyEq : journal.1.1=outerCall.reply := congrArg Prod.fst journalSame
  have nativePath := RegistrationNativeStageTrace.path native _ outerCall.before.2 journal journalCalled
  have journalPresent : entry∈(journal.2.1.2.keys label).1.successfulSeals := by rw [runtimeEq];exact inserted
  obtain ⟨inner,nativePre,nativePost,nativeSplit,nativePrefix,nativeCalled,nativeSuffix,innerAbsent,innerPresent⟩ :=
    first_crossing native (fun current : Runtime => entry∈(current.2.keys label).1.successfulSeals) nativePath notYet journalPresent
  have innerSafe := (native_path modes replace setup codec route env reserve nativePrefix advanced.1).1
  obtain ⟨innerSending,sender,sourceFrame,owned,sourceMatched,outcome⟩ :=
    RegistrationNativePlatformOriginErasedAttribution.query modes ideal replace setup codec route readback env reserve
      inner.query inner.before innerSafe (inner.reply,inner.after) nativeCalled label entry innerAbsent innerPresent
  have frameEq := PqxdhRecordFactsOriginAccepted.matches_unique sourceFrame frame entry sourceMatched matched
  subst sourceFrame
  have innerMember : inner∈journal.2.2 := by rw [nativeSplit];exact List.mem_append_right _ List.mem_cons_self
  have outerSending := outer_sending modes replace setup codec route env reserve serverKeyId bounds
    outerCall.query outerCall.before.1 outerCall.before.2 journal journalCalled inner innerMember innerSending
  refine ⟨outerCall,pre,post,split,earlier,called,later,sending_budget outerCall.query outerSending,notYet,inserted,?_⟩
  have innerNone : RegistrationNativePlatformOriginLedgerSendReply.nativeReply inner.query inner.reply=none := by
    rcases outcome with codecNone | publicNone | ⟨encrypted,published,decoded⟩
    · exact RegistrationNativePlatformOriginErasedEncoderRefusal.query modes ideal replace setup codec route env reserve
        inner.query inner.before (inner.reply,inner.after) nativeCalled label entry innerAbsent innerPresent frame matched codecNone
    · exact unpublished_none inner.query inner.reply innerSending publicNone
    · have nativeAdvance := native_path modes replace setup codec route env reserve
        (.cons inner nativeCalled nativePost journal.2.1 nativeSuffix) innerSafe
      have finalAdvance := full_path modes replace setup codec route env reserve serverKeyId bounds (later.append futurePath)
        (full_step modes replace setup codec route env reserve serverKeyId bounds outerCall.query outerCall.before advanced.1
          (outerCall.reply,outerCall.after) called).1
      have ownedEnd := PqxdhRecordFactsOriginHandles.ownsLabel_step _ _ nativeAdvance label sender owned
      rw [runtimeEq] at ownedEnd
      have ownedFinal := PqxdhRecordFactsOriginHandles.ownsLabel_step _ _ finalAdvance label sender ownedEnd
      have excluded := unpublished sender
        (PqxdhRecordFactsOriginHandles.counterpart_of_opposite final.2.1.2 label sender receiver ownedFinal direction)
      apply False.elim
      apply excluded
      have publication := RegistrationNativePlatformOriginLedgerPublication.full native setup.source.crypto codec serverKeyId bounds
        outerCall.query outerCall.before.1 outerCall.before.2 journal journalCalled inner innerMember (sender,encrypted) published
      rw [replyEq] at publication
      refine ⟨encrypted,?_,decoded⟩
      have recorded := transcript modes replace setup codec route env reserve serverKeyId bounds prefixPath
      simp only [PqxdhDeploymentSecrecy.Ledger.empty,List.nil_append] at recorded
      rw [recorded,List.mem_filterMap]
      refine ⟨⟨outerCall.query,outerCall.reply⟩,?_,publication⟩
      rw [List.mem_map]
      exact ⟨outerCall,by rw [split];exact List.mem_append_right _ List.mem_cons_self,rfl⟩
  have literalSending : RegistrationNativePlatformOriginLedgerSendReply.Sending inner.query := by
    rcases innerSending with ⟨keyId,plaintext,eq⟩ | ⟨owner,plaintext,eq⟩
    · rw [eq];exact .server keyId plaintext
    · rw [eq];exact .beacon owner plaintext
  have refused := RegistrationNativePlatformOriginLedgerSendReply.none setup.source.crypto codec serverKeyId bounds
    outerCall.query outerSending outerCall.before.1 native outerCall.before.2 journal journalCalled inner innerMember literalSending innerNone
  simpa only [replyEq] using refused
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedTemporalWithheld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedTemporalWithheld.outer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedTemporalWithheld.outer_refused
