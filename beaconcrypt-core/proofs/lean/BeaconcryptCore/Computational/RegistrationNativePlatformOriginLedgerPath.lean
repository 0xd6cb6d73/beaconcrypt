-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedInitialized
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPath
open RegistrationNativeStageTrace (Call Path Executed)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FullSpec Entry FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Failure Q S L : Type} {base : OracleSpec I} {spec : OracleSpec Q}
private theorem split_map (implementation : QueryImpl spec (StateT S ProbComp)) (observe : Call spec S→L)
    {before after : S} {calls : List (Call spec S)} (actual : Path implementation before calls after)
    (leading : List L) (entry : L) (later : List L) (same : calls.map observe=leading++entry::later) :
    ∃current pre post,calls=pre++current::post ∧leading=pre.map observe ∧observe current=entry ∧
      Path implementation before pre current.before ∧Executed implementation current ∧Path implementation current.after post after := by
  induction actual generalizing leading with
  | nil state=>simp only [List.map_nil,List.nil_eq_append_iff] at same;cases same.2
  | cons current called rest last following ih=>
    cases leading with
    | nil=>
      simp only [List.map_cons,List.nil_append,List.cons.injEq] at same
      exact ⟨current,[],rest,rfl,rfl,same.1,.nil _,called,following⟩
    | cons head tail=>
      simp only [List.map_cons,List.cons_append,List.cons.injEq] at same
      obtain ⟨chosen,pre,post,split,earlier,chosenEntry,prior,reached,future⟩:=ih tail same.2
      refine ⟨chosen,current::pre,post,?_,?_,chosenEntry,.cons current called pre chosen.before prior,reached,future⟩
      · rw [split];rfl
      · simp only [List.map_cons,earlier,same.1]
variable (modes : Label n→KeyMode) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat→StateT E ProbComp (core.result.Result Unit Failure)) (serverKeyId : U64) (bounds : FreshBounds)
local notation "Runtime"=>PqxdhDeploymentSecrecy.Ledger×CborRawRecordFlat.NativeState n E
local notation "implementation"=>RegistrationNativePlatformGatedRecordFlat.full (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
  env reserve setup.source.crypto codec route serverKeyId bounds
/-- An original ledger occurrence has its own exact callback and before-ledger prefix on the supplied erased source path. Repeated entries and every failed callback remain distinct occurrences. -/
theorem entry {before after : Runtime} {calls : List (Call FullSpec Runtime)} (actual : Path implementation before calls after)
    (leading : List Entry) (currentEntry : Entry) (later : List Entry)
    (ledger : after.1.transcript=before.1.transcript++leading++currentEntry::later) :
    ∃current pre post,calls=pre++current::post ∧
      (⟨current.query,current.reply⟩:Entry)=currentEntry ∧current.before.1.transcript=before.1.transcript++leading ∧
      Path implementation before pre current.before ∧Executed implementation current ∧Path implementation current.after post after := by
  let observe : Call FullSpec Runtime→Entry:=fun current=>⟨current.query,current.reply⟩
  have recorded:=RegistrationNativePlatformOriginErasedInitialized.path_transcript modes replace setup codec route env reserve serverKeyId bounds actual
  have mapped : calls.map observe=leading++currentEntry::later := by
    exact List.append_cancel_left (recorded.symm.trans (by simpa only [List.append_assoc] using ledger))
  obtain ⟨current,pre,post,split,leadingEq,currentEq,prior,called,future⟩:=split_map implementation observe actual leading currentEntry later mapped
  refine ⟨current,pre,post,split,currentEq,?_,prior,called,future⟩
  rw [RegistrationNativePlatformOriginErasedInitialized.path_transcript modes replace setup codec route env reserve serverKeyId bounds prior]
  exact congrArg (fun tail=>before.1.transcript++tail) leadingEq.symm
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPath.entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPath.entry
