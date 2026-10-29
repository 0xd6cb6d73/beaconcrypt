-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecution

/-! Successful stateful executions retain a concrete primitive poststate at every extracted callback. Cutting their trace therefore produces a reached capability and a supported suffix in the same interpretation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation

open RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)

variable {State : Type}

inductive Trace (implementation : QueryImpl Spec (StateT State ProbComp)) :
    registration.InitAuthentication → State → List Event →
      registration.InitAuthentication → State → Prop where
  | refl (initial) (state) : Trace implementation initial state [] initial state
  | cons {initial before event next middle events final after}
      (first : (.ok (some (event, next)), middle) ∈ support
        ((simulateQ implementation (step initial)).run before))
      (rest : Trace implementation next middle events final after) :
      Trace implementation initial before (event :: events) final after

theorem continueWith_support {Input Result : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) (value : Result) (before after : State)
    (supported : (.ok value, after) ∈ support
      ((simulateQ implementation (continueWith result next)).run before)) :
    ∃ input, result = .ok input ∧ (.ok value, after) ∈ support
      ((simulateQ implementation (next input)).run before) := by
  cases result <;> simp_all [continueWith]

private theorem edge_ne_none (event : Event) (result : RustM registration.InitAuthentication) :
    edge event result ≠ .ok none := by
  cases result <;> simp [edge]

theorem step_none_preserves (implementation : QueryImpl Spec (StateT State ProbComp))
    (initial : registration.InitAuthentication) (before after : State)
    (supported : (.ok none, after) ∈ support
      ((simulateQ implementation (step initial)).run before)) : after = before := by
  cases initial
  case Accepted accepted => simpa [step] using supported
  case Rejected => simpa [step] using supported
  all_goals
    simp only [step] at supported
    obtain ⟨request, _, called⟩ := continueWith_support implementation _ _ _ before after supported
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at called
    obtain ⟨reply, _, finished⟩ := called
    simp only [simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at finished
    exact False.elim ((edge_ne_none _ _) finished.1.symm)

theorem execute_trace (implementation : QueryImpl Spec (StateT State ProbComp))
    (fuel : Nat) (initial : registration.InitAuthentication) (events : List Event)
    (final : registration.InitAuthentication) (before after : State)
    (supported : (.ok (events, final), after) ∈ support
      ((simulateQ implementation (execute fuel initial)).run before)) :
    Trace implementation initial before events final after := by
  induction fuel generalizing initial events final before after with
  | succ fuel ih =>
      simp only [execute, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨result, middle⟩, first, returned⟩ := supported
      obtain ⟨next, resultEq, continued⟩ := continueWith_support implementation result _ _
        middle after returned
      subst result
      cases next with
      | none =>
          have noChange := step_none_preserves implementation initial before middle first
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at continued
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := continued
          cases noChange
          exact Trace.refl _ _
      | some next =>
          obtain ⟨event, next⟩ := next
          simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at continued
          obtain ⟨⟨rest, tailState⟩, restSupported, restReturned⟩ := continued
          obtain ⟨tail, restEq, joined⟩ := continueWith_support implementation rest _ _
            tailState after restReturned
          subst rest
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at joined
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := joined
          exact Trace.cons first (ih next tail.1 tail.2 middle _ restSupported)
  | zero =>
      simp only [execute, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := supported
      exact Trace.refl _ _

theorem trace_split (implementation : QueryImpl Spec (StateT State ProbComp))
    {initial final : registration.InitAuthentication} {before after : State}
    (leading tail : List Event)
    (trace : Trace implementation initial before (leading ++ tail) final after) :
    ∃ middle primitive, Trace implementation initial before leading middle primitive ∧
      Trace implementation middle primitive tail final after := by
  induction leading generalizing initial before with
  | nil => exact ⟨initial, before, Trace.refl _ _, trace⟩
  | cons event leading ih =>
      cases trace with
      | cons first rest =>
          obtain ⟨middle, primitive, left, right⟩ := ih rest
          exact ⟨middle, primitive, Trace.cons first left, right⟩

theorem trace_execute (implementation : QueryImpl Spec (StateT State ProbComp))
    {initial final : registration.InitAuthentication} {before after : State} {events : List Event}
    (trace : Trace implementation initial before events final after) :
    (.ok (events, final), after) ∈ support
      ((simulateQ implementation (execute events.length initial)).run before) := by
  induction trace with
  | refl => simp [execute]
  | @cons initial before event next middle events final after first rest ih =>
      simp only [List.length_cons, execute, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff]
      refine ⟨(.ok (some (event, next)), middle), first, ?_⟩
      simp only [continueWith, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨(.ok (events, final), after), ih, by simp⟩

theorem execute_tail_support (implementation : QueryImpl Spec (StateT State ProbComp))
    (fuel : Nat) (initial : registration.InitAuthentication) (leading tail : List Event)
    (final : registration.InitAuthentication) (before after : State)
    (supported : (.ok (leading ++ tail, final), after) ∈ support
      ((simulateQ implementation (execute fuel initial)).run before)) :
    ∃ middle primitive,
      (.ok (leading, middle), primitive) ∈ support
        ((simulateQ implementation (execute leading.length initial)).run before) ∧
      (.ok (tail, final), after) ∈ support
        ((simulateQ implementation (execute tail.length middle)).run primitive) := by
  obtain ⟨middle, primitive, left, right⟩ := trace_split implementation leading tail
    (execute_trace implementation fuel initial (leading ++ tail) final before after supported)
  exact ⟨middle, primitive, trace_execute implementation left, trace_execute implementation right⟩

end BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.continueWith_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.continueWith_support

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.step_none_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.step_none_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.execute_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.execute_trace

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.trace_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.trace_split

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.trace_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.trace_execute

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.execute_tail_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationInterpretation.execute_tail_support
