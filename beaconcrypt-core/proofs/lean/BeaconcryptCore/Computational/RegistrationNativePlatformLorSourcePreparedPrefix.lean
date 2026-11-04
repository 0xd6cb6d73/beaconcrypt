-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginCallbackPrefix
/-! A reached literal source prefix is either still inside its first monadic action or follows an actual supported completed result of that action. These are structural support facts, with no controller or security premise. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {I S A B : Type} {spec : OracleSpec I}
variable (implementation : QueryImpl spec (StateT S ProbComp))

private inductive Forward : OracleComp spec A → S → OracleComp spec A → S → Prop
  | initial (work : OracleComp spec A) (before : S) : Forward work before work before
  | step {query : spec.Domain} {next : spec.Range query → OracleComp spec A} {before : S}
      {reply : spec.Range query × S} {rest : OracleComp spec A} {after : S}
      (called : reply∈support ((implementation query).run before))
      (later : Forward (next reply.1) reply.2 rest after) :
      Forward (OracleComp.queryBind query next) before rest after

private theorem Forward.trans {first middle rest : OracleComp spec A} {before between after : S}
    (earlier : Forward implementation first before middle between) (later : Forward implementation middle between rest after) :
    Forward implementation first before rest after := by
  induction earlier with
  | initial=>exact later
  | step called tail ih=>exact .step called (ih later)

private theorem from_prefix {work rest : OracleComp spec A} {before after : S}
    (path : Prefix implementation work before rest after) : Forward implementation work before rest after := by
  induction path with
  | initial=>exact .initial _ _
  | step past called ih=>exact Forward.trans implementation ih (.step called (.initial _ _))

private theorem to_prefix {work rest : OracleComp spec A} {before after : S}
    (path : Forward implementation work before rest after) : Prefix implementation work before rest after := by
  induction path with
  | initial=>exact .initial
  | step called later ih=>exact Prefix.trans implementation (.step .initial called) ih

private theorem forward_bind_cases (work : OracleComp spec A) (next : A → OracleComp spec B)
    (before : S) (rest : OracleComp spec B) (after : S)
    (path : Forward implementation (work >>=next) before rest after) :
    (∃remaining : OracleComp spec A,Forward implementation work before remaining after ∧ rest=remaining >>=next) ∨
    (∃value middle,(value,middle)∈support ((simulateQ implementation work).run before) ∧
      Forward implementation (next value) middle rest after) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>
    simp only [pure_bind] at path
    exact Or.inr ⟨value,before,by simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff],path⟩
  | query_bind query tail ih=>
    change Forward implementation (OracleComp.queryBind query (fun reply=>tail reply >>=next)) before rest after at path
    cases path with
    | initial=>exact Or.inl ⟨_,.initial _ _,rfl⟩
    | @step _ _ _ reply _ _ called later=>
      rcases ih reply.1 reply.2 later with during|finished
      · obtain ⟨remaining,past,equal⟩ := during
        exact Or.inl ⟨remaining,.step called past,equal⟩
      · obtain ⟨value,middle,completed,last⟩ := finished
        refine Or.inr ⟨value,middle,?_,last⟩
        rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff]
        exact ⟨reply,called,completed⟩

/-- Every source prefix of a bind is either inside its first action or follows one supported completed result, retaining the same reached state. -/
theorem bind_cases (work : OracleComp spec A) (next : A → OracleComp spec B)
    (before : S) (rest : OracleComp spec B) (after : S)
    (path : Prefix implementation (work >>=next) before rest after) :
    (∃remaining : OracleComp spec A,Prefix implementation work before remaining after ∧ rest=remaining >>=next) ∨
    (∃value middle,(value,middle)∈support ((simulateQ implementation work).run before) ∧
      Prefix implementation (next value) middle rest after) := by
  rcases forward_bind_cases implementation work next before rest after (from_prefix implementation path) with during|finished
  · obtain ⟨remaining,past,equal⟩ := during
    exact Or.inl ⟨remaining,to_prefix implementation past,equal⟩
  · obtain ⟨value,middle,called,later⟩ := finished
    exact Or.inr ⟨value,middle,called,to_prefix implementation later⟩

private theorem Forward.completed {work rest : OracleComp spec A} {before after : S}
    (path : Forward implementation work before rest after) (value : A) (returned : rest=pure value) :
    (value,after)∈support ((simulateQ implementation work).run before) := by
  induction path with
  | initial=>simp only [returned,simulateQ_pure,StateT.run_pure,mem_support_pure_iff]
  | @step query tail before reply rest after called later ih=>
    change (value,after)∈support (do
      let current←(implementation query).run before
      (simulateQ implementation (tail current.1)).run current.2)
    rw [mem_support_bind_iff]
    exact ⟨reply,called,ih returned⟩

omit implementation in
private def head {C : Type} (work : OracleComp spec C) : Option spec.Domain :=
  OracleComp.construct (fun _=>none) (fun query _ _=>some query) work

/-- A reached query of a sequential source action is inside its original first action or follows one supported completed first result. -/
theorem bind_query_cases (work : OracleComp spec A) (next : A → OracleComp spec B)
    (before : S) (query : spec.Domain) (tail : spec.Range query → OracleComp spec B) (after : S)
    (path : Prefix implementation (work >>=next) before ((spec.query query : OracleComp spec (spec.Range query)) >>=tail) after) :
    (∃firstTail : spec.Range query → OracleComp spec A,Prefix implementation work before (spec.query query >>=firstTail) after) ∨
    (∃value middle,(value,middle)∈support ((simulateQ implementation work).run before) ∧
      Prefix implementation (next value) middle ((spec.query query : OracleComp spec (spec.Range query)) >>=tail) after) := by
  rcases bind_cases implementation work next before _ after path with during|finished
  · obtain ⟨remaining,past,equal⟩ := during
    cases remaining with
    | pure value=>
      have called := Forward.completed implementation (from_prefix implementation past) value rfl
      refine Or.inr ⟨value,after,called,?_⟩
      simpa only [pure_bind] using (show Prefix implementation (pure value >>=next) after ((spec.query query : OracleComp spec (spec.Range query)) >>=tail) after from equal ▸ Prefix.initial)
    | queryBind firstQuery firstTail=>
      have heads := congrArg head equal
      change some query=some firstQuery at heads
      cases Option.some.inj heads
      exact Or.inl ⟨firstTail,past⟩
  · exact Or.inr finished

private theorem prefix_allowed (predicate : spec.Domain → Prop) {work rest : OracleComp spec A}
    {before after : S} (path : Prefix implementation work before rest after)
    (quiet : work.AllQueriesSatisfy predicate) : rest.AllQueriesSatisfy predicate := by
  induction path with
  | initial=>exact quiet
  | @step earlierQuery earlierNext state reply past called ih=>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mp ih |>.2 reply.1

/-- Every reached original query obeys the static predicate of its actual source tree. -/
theorem query_allowed (predicate : spec.Domain → Prop) (work : OracleComp spec A)
    (quiet : work.AllQueriesSatisfy predicate) (before : S) (query : spec.Domain)
    (tail : spec.Range query → OracleComp spec A) (after : S)
    (path : Prefix implementation work before ((spec.query query : OracleComp spec (spec.Range query)) >>=tail) after) : predicate query := by
  have remaining := prefix_allowed implementation predicate path quiet
  exact ((allQueriesSatisfy_query_bind_iff _ _ _).mp remaining).1

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.bind_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.bind_cases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.bind_query_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.bind_query_cases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed
