-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSampleStageCut
/-! An emitted successful first-record observation is the actual first reply of the Builder source tree. Its exact remaining hash/sign/writer continuation reaches the same final state and log, including later refusals and repeated identical observations in earlier callbacks. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
open RegistrationNativePlatformServerPublication
open RegistrationNativePlatformPublicAdapterBuildStages (Spec observation code)
open RegistrationNativePlatformPublicAdapterBuildSampleStageCut (logged outgoing writer)
variable {S Log :Type}
variable (implementation :QueryImpl Spec (StateT S ProbComp)) (note :Stage→Log)
local notation "Publication"=>RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))
noncomputable def tailCode (hashed :registration.ServerResponseHash) :OracleComp Spec Publication:=
  program (fun query=>Spec.query (.inr (.inl query))) (fun signed=>Spec.query (.inr (.inr signed))) hashed

theorem tail_source (hashed :registration.ServerResponseHash) :
    simulateQ (logged implementation note) (tailCode hashed)=
      program (outgoing implementation note) (writer implementation note) hashed :=by
  unfold tailCode
  rw [program_interpret]
  simp only [simulateQ_spec_query]
  rfl

private theorem pure_log (value :Publication) (before :S) (past :List Log)
    (result :Publication×(S×List Log))
    (supported :result∈support ((pure value:StateT (S×List Log) ProbComp Publication).run (before,past))) :
    result.2.2=past :=by
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem failed (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (reply :RustM RegistrationServerRecordExecutor.Result) (different :reply≠.ok (.Ok hashed))
    (past suffix :List Log) (result :Publication×(S×List Log))
    (kept :result.2.2=past++[note (.firstRecord initial reply)])
    (observed :result.2.2=past++suffix)
    (present :note (.firstRecord initial (.ok (.Ok hashed)))∈suffix) :False :=by
  have same :suffix=[note (.firstRecord initial reply)]:=List.append_cancel_left (observed.symm.trans kept)
  rw [same,List.mem_singleton] at present
  have recordEq:=Stage.firstRecord.inj (injective present)
  exact different recordEq.2.symm

theorem first_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (before :S) (past suffix :List Log) (result :Publication×(S×List Log))
    (supported :result∈support ((simulateQ (logged implementation note) (code initial)).run (before,past)))
    (observed :result.2.2=past++suffix)
    (present :note (.firstRecord initial (.ok (.Ok hashed)))∈suffix) :
    ∃firstState,
      ((.ok (.Ok hashed),firstState):RustM RegistrationServerRecordExecutor.Result×S)∈support
        ((implementation (.inl initial)).run before) ∧
      result∈support ((simulateQ (logged implementation note) (tailCode hashed)).run
        (firstState,past++[note (.firstRecord initial (.ok (.Ok hashed)))])) :=by
  rw [RegistrationNativePlatformPublicAdapterBuildStages.interpret] at supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨first,called,later⟩:=supported
  simp only [logged,RegistrationNativePlatformPublicAdapterSourceTrace.recorded,StateT.run,support_map] at called
  obtain ⟨raw,firstCalled,same⟩:=called
  cases same
  cases reply:raw.1 with
  | fail error | div=>
    simp only [reply,continueResult] at later
    have kept:=pure_log _ _ _ _ later
    have actual:result.2.2=past++[note (.firstRecord initial raw.1)]:=by
      simpa only [reply,observation,List.map_cons,List.map_nil] using kept
    exact (failed note injective initial hashed raw.1 (by rw [reply]; intro impossible; cases impossible) past suffix result actual observed present).elim
  | ok status=>cases status with
    | Err old=>
      simp only [reply,continueResult] at later
      have kept:=pure_log _ _ _ _ later
      have actual:result.2.2=past++[note (.firstRecord initial raw.1)]:=by
        simpa only [reply,observation,List.map_cons,List.map_nil] using kept
      exact (failed note injective initial hashed raw.1 (by rw [reply]; intro impossible; cases impossible) past suffix result actual observed present).elim
    | Ok selected=>
      simp only [reply,continueResult,observation,List.map_cons,List.map_nil] at later
      obtain ⟨hashRequest,digest,signature,request,hashState,signState,_requested,_hashCalled,_signCalled,_key,events⟩:=
        RegistrationNativePlatformPublicAdapterBuildSampleStageCut.program_log implementation note selected raw.2
          (past++[note (.firstRecord initial (.ok (.Ok selected)))]) result later
      have exactSuffix:suffix=[note (.firstRecord initial (.ok (.Ok selected))),note (.hash hashRequest digest),note (.sign request (RegistrationSigningTrace.Command.payload (.server selected)) digest signature)]:=by
        apply List.append_cancel_left
        exact observed.symm.trans (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using events)
      rw [exactSuffix] at present
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with first|hash|sign
      · obtain ⟨_,selectedEq⟩:=Stage.firstRecord.inj (injective first)
        have hashedEq:hashed=selected:=by cases selectedEq; rfl
        subst selected
        refine ⟨raw.2,?_,?_⟩
        · exact (show raw=(.ok (.Ok hashed),raw.2) from Prod.ext reply rfl) ▸firstCalled
        · rw [tail_source]
          exact later
      · cases injective hash
      · cases injective sign

section Nested
variable {P :Type}
variable (nested :QueryImpl Spec (StateT S (StateT P ProbComp)))
open RegistrationNativePlatformPublicAdapterBuildSampleStageCut (packed packLog nested_source)

theorem nested_first_cut (injective :Function.Injective note)
    (initial :registration.ServerInitialKdf) (hashed :registration.ServerResponseHash)
    (before :S) (previous :P) (past suffix :List Log)
    (result :(Publication×(S×List Log))×P)
    (supported :result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded nested
      (fun query reply=>(observation query reply).map note)) (code initial)).run (before,past)).run previous))
    (observed :result.1.2.2=past++suffix)
    (present :note (.firstRecord initial (.ok (.Ok hashed)))∈suffix) :
    ∃firstState firstPlatform,
      (((.ok (.Ok hashed),firstState),firstPlatform):(RustM RegistrationServerRecordExecutor.Result×S)×P)∈support
        (((nested (.inl initial)).run before).run previous) ∧
      result∈support (((simulateQ (RegistrationNativePlatformPublicAdapterSourceTrace.recorded nested
        (fun query reply=>(observation query reply).map note)) (tailCode hashed)).run
        (firstState,past++[note (.firstRecord initial (.ok (.Ok hashed)))])).run firstPlatform) :=by
  have mapped :packLog result∈support ((simulateQ (logged (packed nested) note) (code initial)).run ((before,previous),past)):=by
    rw [←nested_source note nested,support_map]
    exact ⟨result,supported,rfl⟩
  obtain ⟨firstState,firstCalled,later⟩:=first_cut (packed nested) note injective initial hashed (before,previous) past suffix
    (packLog result) mapped observed present
  have firstNested :(((.ok (.Ok hashed),firstState.1),firstState.2):(RustM RegistrationServerRecordExecutor.Result×S)×P)∈support
      (((nested (.inl initial)).run before).run previous):=by
    simp only [packed,RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at firstCalled
    obtain ⟨raw,called,same⟩:=firstCalled
    have rawEq:raw=((.ok (.Ok hashed),firstState.1),firstState.2):=by
      exact congrArg (fun value:RustM RegistrationServerRecordExecutor.Result×(S×P)=>((value.1,value.2.1),value.2.2)) same
    exact rawEq ▸called
  refine ⟨firstState.1,firstState.2,firstNested,?_⟩
  rw [←nested_source note nested,support_map] at later
  obtain ⟨raw,called,same⟩:=later
  have rawEq:raw=result:=by
    have unpaired:=congrArg (fun value:Publication×((S×P)×List Log)=>((value.1,(value.2.1.1,value.2.2)),value.2.1.2)) same
    exact unpaired
  exact rawEq ▸called
end Nested

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.tail_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.first_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.first_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.nested_first_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildFirstContinuation.nested_first_cut
