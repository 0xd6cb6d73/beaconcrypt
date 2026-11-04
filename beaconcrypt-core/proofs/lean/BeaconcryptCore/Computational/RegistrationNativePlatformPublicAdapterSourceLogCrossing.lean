-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
/-! A given newly emitted source observation has a genuine first emitting source query. Its actual before/after states and complete source prefix/suffix paths are retained, including repeated observations already present before the program. This is used to locate the actual Builder complete leaf and earlier source callback, not to substitute a compatible native trace. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing
open RegistrationNativeStageTrace (Call Path Executed)
variable {Q S Log A :Type} {spec :OracleSpec Q}
variable (implementation :QueryImpl spec (StateT S ProbComp)) (events :S→List Log)

theorem path (work :OracleComp spec A) (before :S) (result :A×S)
    (supported :result∈support ((simulateQ implementation work).run before)) :
    ∃calls,Path implementation before calls result.2 :=by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨[],.nil _⟩
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,following⟩:=supported
    obtain ⟨rest,actual⟩:=ih middle.1 middle.2 result following
    exact ⟨⟨query,before,middle.1,middle.2⟩::rest,.cons (⟨query,before,middle.1,middle.2⟩ :Call spec S) called _ _ actual⟩

variable (appends :∀query before result,result∈support ((implementation query).run before)→
  ∃suffix,events result.2=events before++suffix)

include appends in
theorem append (work :OracleComp spec A) (before :S) (result :A×S)
    (supported :result∈support ((simulateQ implementation work).run before)) :
    ∃suffix,events result.2=events before++suffix :=by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨[],(List.append_nil _).symm⟩
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,following⟩:=supported
    obtain ⟨fresh,emitted⟩:=appends query before middle called
    obtain ⟨later,kept⟩:=ih middle.1 middle.2 result following
    exact ⟨fresh++later,by rw [kept,emitted,List.append_assoc]⟩

variable (allowed marked :spec.Domain→Prop)
variable (quiet :∀query,¬marked query→∀before result,
  result∈support ((implementation query).run before)→events result.2=events before)

include appends quiet in
theorem crossing (work :OracleComp spec A) (safe :work.AllQueriesSatisfy allowed)
    (before :S) (result :A×S) (supported :result∈support ((simulateQ implementation work).run before))
    (suffix :List Log) (observed :events result.2=events before++suffix) (item :Log) (present :item∈suffix) :
    ∃(leading trailing :List (Call spec S)) (call :Call spec S),Path implementation before leading call.before ∧
      Executed implementation call ∧Path implementation call.after trailing result.2 ∧
      allowed call.query ∧marked call.query ∧
      ∃emitted,events call.after=events call.before++emitted ∧item∈emitted :=by
  classical
  induction work using OracleComp.inductionOn generalizing before result suffix with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
    cases supported
    have empty :suffix=[]:=List.append_cancel_left (observed.symm.trans (List.append_nil _).symm)
    rw [empty] at present
    cases present
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at safe
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,following⟩:=supported
    obtain ⟨fresh,emitted⟩:=appends query before middle called
    obtain ⟨later,kept⟩:=append implementation events appends (next middle.1) middle.2 result following
    have suffixEq :suffix=fresh++later:=List.append_cancel_left (observed.symm.trans (by rw [kept,emitted,List.append_assoc]))
    rw [suffixEq] at present
    rcases List.mem_append.mp present with now|after
    · have isMarked :marked query:=by
        by_contra absent
        have same:=quiet query absent before middle called
        have empty :fresh=[]:=List.append_cancel_left (emitted.symm.trans (same.trans (List.append_nil _).symm))
        rw [empty] at now
        cases now
      obtain ⟨rest,actual⟩:=path implementation (next middle.1) middle.2 result following
      exact ⟨[],rest,⟨query,before,middle.1,middle.2⟩,.nil _,called,actual,safe.1,isMarked,fresh,emitted,now⟩
    · obtain ⟨leading,trailing,call,prior,calledNext,followingNext,permitted,isMarked,observedNext⟩:=
        ih middle.1 (safe.2 middle.1) middle.2 result following later kept after
      exact ⟨⟨query,before,middle.1,middle.2⟩::leading,trailing,call,.cons (⟨query,before,middle.1,middle.2⟩ :Call spec S) called _ _ prior,
        calledNext,followingNext,permitted,isMarked,observedNext⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.path' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.append' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.append

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceLogCrossing.crossing
