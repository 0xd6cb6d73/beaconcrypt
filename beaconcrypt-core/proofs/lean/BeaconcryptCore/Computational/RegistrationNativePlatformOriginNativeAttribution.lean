-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
/-! A newly retained hidden seal is attributed to its exact earlier gated send within any actual native/full-ledger program. Both the pre-gate encoder reply and the final public reply remain separate, including test/fresh source programs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec FullSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformGatedRecordFreshCoupling (nativeImpl fullImpl)
variable {n : Nat} {I KemSK Reader Response E Failure V : Type} {base : OracleSpec I}
attribute [local irreducible] ctxInterpreter

private theorem acquired {Q S : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT S ProbComp)) (predicate : S → Prop)
    {before after : S} {calls : List (Call spec S)} (path : Path implementation before calls after)
    (absent : ¬predicate before) (present : predicate after) :
    ∃ call leading trailing,calls=leading++call::trailing ∧ Path implementation before leading call.before ∧
      Executed implementation call ∧ Path implementation call.after trailing after ∧ ¬predicate call.before ∧ predicate call.after := by
  induction path with
  | nil => exact False.elim (absent present)
  | cons call called rest last following ih =>
      by_cases hit : predicate call.after
      · exact ⟨call,[],rest,rfl,.nil _,called,following,absent,hit⟩
      · obtain ⟨chosen,leading,trailing,split,prior,middle,suffix,notYet,inserted⟩ := ih hit present
        exact ⟨chosen,call::leading,trailing,by rw [split];rfl,.cons call called _ _ prior,middle,suffix,notYet,inserted⟩

variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
local notation "impl" => nativeImpl modes replace setup codec route env reserve

include ideal in
private theorem nonsend_seals (query : Spec.Domain) (quiet : PqxdhRecordFactsOriginPublicationNative.NonSending query)
    (before : NativeState n E) (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((impl query).run before)) :
    ∀label,(result.2.2.keys label).1.successfulSeals=(before.2.keys label).1.successfulSeals := by
  change result ∈ support ((RegistrationNativePlatformGatedRecordFlat.native (ctxInterpreter modes replace setup codec) env reserve codec route query).run before) at supported
  rw [RegistrationNativePlatformGatedRecordOriginStage.native_nonSend _ codec route env reserve query quiet] at supported
  have projected : (result.1,CborRawRecordOriginService.project result.2) ∈ support
      ((CborRawRecordOriginService.original (ctxInterpreter modes replace setup codec) env codec route query).run
        (CborRawRecordOriginService.project before)) := by
    rw [←CborRawRecordOriginService.nonrecord_project _ env codec route query before ?_,support_map]
    · exact ⟨result,supported,rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [PqxdhRecordFactsOriginPublicationNative.NonSending,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
  exact PqxdhRecordFactsOriginPublicationNative.native_nonSend_seals modes ideal replace setup codec route env query quiet
    (CborRawRecordOriginService.project before) (result.1,CborRawRecordOriginService.project result.2) projected

include ideal in
/-- Newly retained hidden seals arise only at the two literal ordinary send commands, including sends whose final public reply is absent. -/
theorem query_sending (query : Spec.Domain) (before : NativeState n E) (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((impl query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    (∃keyId plaintext,query=.inr (.serverSend keyId plaintext)) ∨
      (∃owner plaintext,query=.inr (.beaconSend owner plaintext)) := by
  have active : ¬PqxdhRecordFactsOriginPublicationNative.NonSending query := by
    intro quiet
    exact absent ((nonsend_seals modes ideal replace setup codec route env reserve query quiet before result supported label) ▸ present)
  rcases query with coin | command
  · exact False.elim (active (by trivial))
  · cases command
    case serverSend keyId plaintext => exact Or.inl ⟨keyId,plaintext,rfl⟩
    case beaconSend owner plaintext => exact Or.inr ⟨owner,plaintext,rfl⟩
    all_goals exact False.elim (active (by trivial))

include ideal in
private theorem path_safe {before after : NativeState n E} {calls : List (Call Spec (NativeState n E))}
    (path : Path impl before calls after) :
    PqxdhRecordLiftProtocolHistory.Safe before.1.2 → PqxdhRecordLiftProtocolHistory.Safe after.1.2 := by
  induction path with
  | nil => exact id
  | cons call called rest last following ih =>
      intro safe
      exact ih (RegistrationNativePlatformGatedRecordBindingControl.native_advance modes ideal replace setup codec route env reserve
        call.query call.before safe (call.reply,call.after) called).step.1

include ideal readback in
/-- The exact same path supplies a first acquisition callback and its literal pre-gate encoder/public-gate factorization. -/
theorem path_entry {before after : NativeState n E} {calls : List (Call Spec (NativeState n E))}
    (path : Path impl before calls after) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (after.2.keys label).1.successfulSeals) :
    ∃ call leading trailing,calls=leading++call::trailing ∧ Path impl before leading call.before ∧ Executed impl call ∧
      Path impl call.after trailing after ∧ PqxdhRecordLiftProtocolHistory.Safe call.before.1.2 ∧
      entry ∉ (call.before.2.keys label).1.successfulSeals ∧ entry ∈ (call.after.2.keys label).1.successfulSeals ∧
      ∃ original,original ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route call.query).run call.before) ∧
        (call.reply,call.after) ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
          (RegistrationNativePlatformGatedRecordInterface.post reserve call.query original.1)).run original.2) ∧
        PqxdhRecordFactsOriginPublicationNative.CreatedAt codec call.before.1.2 ⟨.inl call.query,original.1⟩ label entry := by
  obtain ⟨call,leading,trailing,split,prior,called,suffix,notYet,inserted⟩ :=
    acquired impl (fun current => entry ∈ (current.2.keys label).1.successfulSeals) path absent present
  have safeBefore := path_safe modes ideal replace setup codec route env reserve prior safe
  have attributed := RegistrationNativePlatformOriginGateEntry.gated_entry modes ideal replace setup codec route readback env reserve
    call.query call.before safeBefore (call.reply,call.after) called label entry inserted
  exact ⟨call,leading,trailing,split,prior,called,suffix,safeBefore,notYet,inserted,attributed.resolve_left notYet⟩

include ideal readback in
/-- Every supported native program derives its own exact full-state journal before selecting the acquisition callback; no caller path invariant is required. -/
theorem program_entry (work : OracleComp Spec V) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2) (result : V × NativeState n E)
    (supported : result ∈ support ((simulateQ impl work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    ∃ calls,Path impl before calls result.2 ∧
      ∃ call leading trailing,calls=leading++call::trailing ∧ Path impl before leading call.before ∧ Executed impl call ∧
        Path impl call.after trailing result.2 ∧ PqxdhRecordLiftProtocolHistory.Safe call.before.1.2 ∧
        entry ∉ (call.before.2.keys label).1.successfulSeals ∧ entry ∈ (call.after.2.keys label).1.successfulSeals ∧
        ∃ original,original ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route call.query).run call.before) ∧
          (call.reply,call.after) ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
            (RegistrationNativePlatformGatedRecordInterface.post reserve call.query original.1)).run original.2) ∧
          PqxdhRecordFactsOriginPublicationNative.CreatedAt codec call.before.1.2 ⟨.inl call.query,original.1⟩ label entry := by
  rw [←RegistrationNativeStageTrace.erase impl work (before,[]),support_map] at supported
  obtain ⟨journal,called,rfl⟩ := supported
  have actual := RegistrationNativeStageTrace.path impl work before journal called
  exact ⟨journal.2.2,actual,path_entry modes ideal replace setup codec route readback env reserve actual safe label entry absent present⟩

include ideal readback in
/-- Literal test/fresh draws and the full ledger callback retain the same acquisition certificate, with both original encoder and final macro reply. -/
theorem full_entry (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((fullImpl modes replace setup codec route env reserve serverKeyId bounds query).run (ledger,before)))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry ∉ (before.2.keys label).1.successfulSeals)
    (present : entry ∈ (result.2.2.2.keys label).1.successfulSeals) :
    ∃ calls,Path impl before calls result.2.2 ∧
      ∃ call leading trailing,calls=leading++call::trailing ∧ Path impl before leading call.before ∧ Executed impl call ∧
        Path impl call.after trailing result.2.2 ∧ PqxdhRecordLiftProtocolHistory.Safe call.before.1.2 ∧
        entry ∉ (call.before.2.keys label).1.successfulSeals ∧ entry ∈ (call.after.2.keys label).1.successfulSeals ∧
        ∃ original,original ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route call.query).run call.before) ∧
          (call.reply,call.after) ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
            (RegistrationNativePlatformGatedRecordInterface.post reserve call.query original.1)).run original.2) ∧
          PqxdhRecordFactsOriginPublicationNative.CreatedAt codec call.before.1.2 ⟨.inl call.query,original.1⟩ label entry := by
  change result ∈ support ((fun actual => (actual.1.1,(actual.1.2,actual.2))) <$>
    (simulateQ impl ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKeyId bounds query).run ledger)).run before) at supported
  rw [support_map] at supported
  obtain ⟨actual,called,rfl⟩ := supported
  exact program_entry modes ideal replace setup codec route readback env reserve _ before safe actual called label entry absent present
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.path_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.path_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.program_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.program_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.full_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.full_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.query_sending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeAttribution.query_sending
