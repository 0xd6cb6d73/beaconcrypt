-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackCut
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace
open RegistrationNativeStageTrace (Call)
open RegistrationNativePlatformOriginCallbackCut (scan markedResume)
variable {Q S A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
abbrev Result (spec : OracleSpec Q) (S A : Type) := List (Call spec S) × (A × S)

noncomputable def track (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) : S → ProbComp (Result spec S A) :=
  OracleComp.recOn work
    (fun value state=>pure ([],(value,state)))
    (fun query _next recurse state=>do
      let reply←(implementation query).run state
      let result←recurse reply.1 reply.2
      pure ((if counted query then [⟨query,state,reply.1,reply.2⟩] else [])++result.1,result.2))

theorem track_query (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (query : spec.Domain) (next : spec.Range query → OracleComp spec A) (state : S) :
    track counted implementation (spec.query query >>=next) state =
      (do let reply←(implementation query).run state
          let result←track counted implementation (next reply.1) reply.2
          pure ((if counted query then [⟨query,state,reply.1,reply.2⟩] else [])++result.1,result.2)) := rfl

/-- Forgetting the counted callback journal preserves the complete original value and source poststate. -/
theorem track_drop (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (state : S) :
    Prod.snd <$>track counted implementation work state=(simulateQ implementation work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value=>rfl
  | query_bind query next ih=>
    rw [track_query]
    simp only [map_bind,bind_pure_comp,Functor.map_map,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    apply bind_congr
    intro reply
    exact ih reply.1 reply.2

def selected (index : Nat) (result : Result spec S A) : Option (Call spec S) × (A × S) :=
  (result.1[index]?,result.2)

/-- Selecting one all-attempt ordinal from the same complete trace is exactly prefix scanning followed by the literal current callback and same original future. -/
theorem track_selected (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (index : Nat) (state : S) :
    selected index <$>track counted implementation work state=
      (scan counted implementation work index state >>=markedResume implementation) := by
  induction work using OracleComp.inductionOn generalizing index state with
  | pure value=>rfl
  | query_bind query next ih=>
    rw [track_query,RegistrationNativePlatformOriginCallbackCut.scan_query]
    by_cases hit : counted query
    · cases index with
      | zero=>
        simp only [hit,ite_true,map_bind,map_pure,List.singleton_append,selected,List.getElem?_cons_zero,pure_bind,markedResume]
        apply bind_congr
        intro reply
        have same := congrArg (Functor.map (fun result=>(some (⟨query,state,reply.1,reply.2⟩ : Call spec S),result)))
          (track_drop counted implementation (next reply.1) reply.2)
        simpa only [Functor.map_map,bind_pure_comp] using same
      | succ index=>
        simp only [hit,ite_true,map_bind,map_pure,List.singleton_append,selected,List.getElem?_cons_succ,bind_assoc]
        apply bind_congr
        intro reply
        have same := ih reply.1 index reply.2
        unfold selected at same
        simpa only [bind_pure_comp] using same
    · simp only [hit,ite_false,List.nil_append,map_bind,map_pure,bind_assoc]
      apply bind_congr
      intro reply
      have same := ih reply.1 index reply.2
      unfold selected at same
      simpa only [bind_pure_comp,selected] using same

/-- The original predicate query allowance bounds every supported counted journal, including failed callback replies. -/
theorem track_length (counted : spec.Domain → Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (cap : Nat) (bounded : work.IsQueryBoundP counted cap)
    (state : S) (result : Result spec S A)
    (supported : result∈support (track counted implementation work state)) :result.1.length≤cap := by
  induction work using OracleComp.inductionOn generalizing cap state result with
  | pure value=>
    change result∈support (pure ([],(value,state)) : ProbComp _) at supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact Nat.zero_le _
  | query_bind query next ih=>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [track_query] at supported
    simp only [mem_support_bind_iff,mem_support_pure_iff] at supported
    obtain ⟨reply,_answered,inner,finished,rfl⟩ := supported
    have remaining := ih reply.1 _ (bounded.2 reply.1) reply.2 inner finished
    by_cases hit : counted query
    · have positive : 0<cap := bounded.1.resolve_left (not_not.mpr hit)
      simp only [hit,ite_true,List.singleton_append,List.length_cons] at remaining ⊢
      omega
    · simpa only [hit,ite_false,List.nil_append] using remaining
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_query


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_drop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_drop


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_selected


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace.track_length
