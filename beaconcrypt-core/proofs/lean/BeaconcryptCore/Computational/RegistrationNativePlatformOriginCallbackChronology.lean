-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackTrace
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePlatformOriginCallbackTrace (track Result)
variable {Q S A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p:=Classical.propDecidable p
/-- A supported counted callback trace is the literal filter of one complete same-run source path, preserving every failed and uncounted callback. -/
theorem path (counted : spec.Domain→Prop) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec A) (before : S) (result : Result spec S A)
    (supported : result∈support (track counted implementation work before)) :
    ∃calls : List (Call spec S), Path implementation before calls result.2.2 ∧
      calls.filter (fun current=>decide (counted current.query))=result.1 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    change result∈support (pure ([],(value,before)):ProbComp _) at supported
    rw [mem_support_pure_iff] at supported
    subst result
    exact ⟨[],.nil _,rfl⟩
  | query_bind query next ih=>
    rw [RegistrationNativePlatformOriginCallbackTrace.track_query] at supported
    simp only [mem_support_bind_iff,mem_support_pure_iff] at supported
    obtain ⟨reply,called,inner,continued,rfl⟩:=supported
    obtain ⟨calls,history,filtered⟩:=ih reply.1 reply.2 inner continued
    let current : Call spec S:=⟨query,before,reply.1,reply.2⟩
    refine ⟨current::calls,.cons current called calls inner.2.2 history,?_⟩
    by_cases selected : counted query
    · simp only [List.filter_cons,current,selected,decide_true,ite_true,List.singleton_append,filtered]
    · simp only [List.filter_cons,current,selected,decide_false,Bool.false_eq_true,ite_false,List.nil_append,filtered]
/-- A per-query state projection transports the complete same callback path and its before/after snapshots. -/
theorem project_path {T : Type} (implementation : QueryImpl spec (StateT S ProbComp))
    (target : QueryImpl spec (StateT T ProbComp)) (projection : S→T)
    (leaf : ∀query before,Prod.map id projection <$> (implementation query).run before=(target query).run (projection before))
    {before after : S} {calls : List (Call spec S)} (actual : Path implementation before calls after) :
    Path target (projection before) (calls.map (RegistrationNativeObservedStageTrace.mapCall projection)) (projection after) := by
  induction actual with
  | nil state=>exact .nil _
  | cons current called rest last following ih=>
    apply Path.cons (RegistrationNativeObservedStageTrace.mapCall projection current) _ _ _ ih
    rw [RegistrationNativeStageTrace.Executed] at called ⊢
    change (current.reply,projection current.after)∈support ((target current.query).run (projection current.before))
    rw [←leaf,support_map]
    exact ⟨(current.reply,current.after),called,rfl⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology.project_path' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackChronology.project_path
