-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginMacroOutcome
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply
/-! Actual new dictionary entries retain the temporal distinction between a failed source encoder, an actual withheld public send and an original outer-ledger publication. No blanket publication-history premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix
open PqxdhRecordLiftIdeal (KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec Entry FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "Runtime" => CborRawRecordFlat.NativeState n E
local notation "native" => RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve
variable (serverKeyId : U64) (bounds : FreshBounds)
local notation "full" => RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKeyId bounds
local notation "Whole" => PqxdhDeploymentSecrecy.Ledger × Runtime

private theorem advance_refl (before : Runtime) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) :
    CborRawRecordBindingControl.Advance before before :=
  ⟨PqxdhRecordLiftProtocolHistory.step_refl _ safe,fun _ prior=>prior,PqxdhRecordFactsOriginMonotone.Grows.refl _,le_rfl⟩
private theorem advance_trans (before middle after : Runtime)
    (first : CborRawRecordBindingControl.Advance before middle) (last : CborRawRecordBindingControl.Advance middle after) :
    CborRawRecordBindingControl.Advance before after :=
  ⟨PqxdhRecordFactsOriginControl.step_trans _ _ _ first.step last.step,
    fun handle prior=>last.known handle (first.known handle prior),
    PqxdhRecordFactsOriginMonotone.Grows.trans _ _ _ first.grows last.grows,first.cache.trans last.cache⟩

include ideal in
/-- Every literal inner native suffix retains its joint control, ownership, cache and seal receipts. -/
theorem native_path {before after : Runtime} {calls : List (Call Spec Runtime)}
    (path : Path native before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) :
    CborRawRecordBindingControl.Advance before after := by
  induction path with
  | nil state => exact advance_refl state safe
  | cons call called rest last following ih =>
    have first := RegistrationNativePlatformGatedRecordBindingControl.native_advance modes ideal replace setup codec route env reserve
      call.query call.before safe (call.reply,call.after) called
    exact advance_trans _ _ _ first (ih first.step.1)

include ideal in
/-- All original full callbacks retain the same joint state receipt through actual test/fresh and public gate failures. -/
theorem full_path {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) :
    CborRawRecordBindingControl.Advance before.2 after.2 := by
  induction path with
  | nil state => exact advance_refl state.2 safe
  | cons call called rest last following ih =>
    have first := RegistrationNativePlatformGatedRecordBindingControl.full_advance modes ideal replace setup codec route env reserve
      serverKeyId bounds call.query call.before safe (call.reply,call.after) called
    exact advance_trans _ _ _ first (ih first.step.1)

include ideal readback in
/-- The literal macro path records precisely its own original ordered replies in the native full ledger. -/
theorem transcript {before after : Whole} {calls : List (Call FullSpec Whole)}
    (path : Path full before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2) :
    after.1.transcript=before.1.transcript++calls.map (fun call=>(⟨call.query,call.reply⟩ : Entry)) := by
  induction path with
  | nil state => exact (List.append_nil _).symm
  | cons call called rest last following ih =>
    have first := RegistrationNativePlatformGatedRecordBindingControl.full_advance modes ideal replace setup codec route env reserve
      serverKeyId bounds call.query call.before safe (call.reply,call.after) called
    have recorded := (RegistrationNativePlatformGatedRecordBindingLedger.full_record modes ideal replace setup codec route readback env reserve
      serverKeyId bounds call.query call.before safe (call.reply,call.after) called).1
    rw [ih first.step.1,recorded,List.map_cons,List.append_assoc]
    rfl

private theorem first_crossing {Q S : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT S ProbComp)) (present : S → Prop)
    {before after : S} {calls : List (Call spec S)} (path : Path implementation before calls after)
    (absent : ¬present before) (found : present after) :
    ∃ (call : Call spec S), ∃ leading trailing,calls=leading++call::trailing ∧
      Path implementation before leading call.before ∧ Executed implementation call ∧
      Path implementation call.after trailing after ∧ ¬present call.before ∧ present call.after ∧
      (∀ prior∈leading,¬present prior.after) := by
  classical
  induction path with
  | nil state => exact (absent found).elim
  | cons call called rest last following ih =>
    by_cases entered : present call.after
    · exact ⟨call,[],rest,rfl,.nil _,called,following,absent,entered,by intro prior impossible;cases impossible⟩
    · obtain ⟨target,leading,trailing,split,earlier,reached,later,notYet,inserted,noneBefore⟩ := ih entered found
      refine ⟨target,call::leading,trailing,by rw [split];rfl,.cons call called leading target.before earlier,
        reached,later,notYet,inserted,?_⟩
      intro prior member
      rcases List.mem_cons.mp member with same | subsequent
      · exact same ▸ entered
      · exact noneBefore prior subsequent

include ideal readback in
/-- A retained hidden seal has its first actual full macro acquisition, exact original prefix, owned sender/frame and all three literal publication alternatives. -/
theorem acquired (initial : Runtime) (final : Whole) (calls : List (Call FullSpec Whole))
    (path : Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) calls final)
    (safe : PqxdhRecordLiftProtocolHistory.Safe initial.1.2)
    (label : Label n) (entry : CtxRomAuth.CtxSuccessfulSeal)
    (empty : (initial.2.keys label).1.successfulSeals=[])
    (found : entry∈(final.2.2.keys label).1.successfulSeals) :
    ∃ (outerCall : Call FullSpec Whole), ∃ pre post, ∃ (inner : Call Spec Runtime), ∃ leading trailing sender frame,
      calls=pre++outerCall::post ∧ Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) pre outerCall.before ∧
      Executed full outerCall ∧ Path full outerCall.after post final ∧
      outerCall.before.1.transcript=pre.map (fun call=>(⟨call.query,call.reply⟩ : Entry)) ∧
      (∀ prior∈pre,entry∉(prior.after.2.2.keys label).1.successfulSeals) ∧
      entry∉(outerCall.before.2.2.keys label).1.successfulSeals ∧ entry∈(outerCall.after.2.2.keys label).1.successfulSeals ∧
      Path native outerCall.before.2 leading inner.before ∧ Executed native inner ∧ Path native inner.after trailing outerCall.after.2 ∧
      PqxdhRecordLiftProtocolHistory.Safe inner.before.1.2 ∧
      entry∉(inner.before.2.keys label).1.successfulSeals ∧ entry∈(inner.after.2.keys label).1.successfulSeals ∧
      PqxdhRecordFactsOriginHandles.OwnsLabel inner.before.1.2 label sender ∧
      PqxdhRecordFactsOriginHandles.OwnsLabel final.2.1.2 label sender ∧
      PqxdhRecordFactsOriginReplay.Matches frame entry ∧
      (codec.frameWrite frame=none ∨ (⟨.inl inner.query,inner.reply⟩ : Entry).published=none ∨
        ∃ encrypted,(⟨outerCall.query,outerCall.reply⟩ : Entry).published=some (sender,encrypted) ∧ codec.frameRead encrypted.ciphertext=some frame) := by
  have absent : entry∉(initial.2.keys label).1.successfulSeals := by rw [empty];simp only [List.not_mem_nil,not_false_eq_true]
  obtain ⟨outerCall,pre,post,split,earlier,called,later,notYet,inserted,noneBefore⟩ := first_crossing full
    (fun current : Whole=>entry∈(current.2.2.keys label).1.successfulSeals) path absent found
  have advanced := full_path modes ideal replace setup codec route env reserve serverKeyId bounds earlier safe
  obtain ⟨inner,leading,trailing,sender,frame,prior,reached,suffix,innerSafe,innerAbsent,innerPresent,owned,matched,outcome⟩ :=
    RegistrationNativePlatformOriginMacroOutcome.full modes ideal replace setup codec route readback env reserve serverKeyId bounds
      outerCall.query outerCall.before.1 outerCall.before.2 advanced.step.1 (outerCall.reply,outerCall.after) called label entry notYet inserted
  have innerAhead := native_path modes ideal replace setup codec route env reserve
    (.cons inner reached trailing outerCall.after.2 suffix) innerSafe
  have macroAhead := RegistrationNativePlatformGatedRecordBindingControl.full_advance modes ideal replace setup codec route env reserve
    serverKeyId bounds outerCall.query outerCall.before advanced.step.1 (outerCall.reply,outerCall.after) called
  have finalAhead := full_path modes ideal replace setup codec route env reserve serverKeyId bounds later macroAhead.step.1
  have ownedAfter := PqxdhRecordFactsOriginHandles.ownsLabel_step inner.before.1.2 outerCall.after.2.1.2 innerAhead.step label sender owned
  have ownedFinal := PqxdhRecordFactsOriginHandles.ownsLabel_step outerCall.after.2.1.2 final.2.1.2 finalAhead.step label sender ownedAfter
  have recorded := transcript modes ideal replace setup codec route readback env reserve serverKeyId bounds earlier safe
  simp only [PqxdhDeploymentSecrecy.Ledger.empty,List.nil_append] at recorded
  exact ⟨outerCall,pre,post,inner,leading,trailing,sender,frame,split,earlier,called,later,recorded,noneBefore,notYet,inserted,
    prior,reached,suffix,innerSafe,innerAbsent,innerPresent,owned,ownedFinal,matched,outcome⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.native_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.native_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.full_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.full_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.transcript

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.acquired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginFullPrefix.acquired
