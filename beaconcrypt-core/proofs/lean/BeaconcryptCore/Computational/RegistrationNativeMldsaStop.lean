-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate

/-! Online freezing of an adaptive typed client at the first complete callback selected by an executable observer. After selection, later adversary queries receive fixed defaults and issue no primitive call. The selected candidate has exactly its full monitored-execution distribution; its private stopping state remains the actual state at that callback. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaStop
variable {ι State Candidate Value : Type} {spec : OracleSpec ι}

abbrev Observer := (query : spec.Domain) → State → spec.Range query → State → Option Candidate

private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

/-- The unmodified handler with a first-candidate analysis flag. -/
def monitor {m : Type → Type} [Monad m] (handler : QueryImpl spec (StateT State m))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate)) :
    QueryImpl spec (StateT (State × Option Candidate) m) := fun query before => do
  let result ← (handler query).run before.1
  pure (result.1, (result.2, before.2.orElse fun _ => observe query before.1 result.1 result.2))

/-- Once selected, the client receives only fixed replies and retains the exact stopping snapshot. -/
def freeze {m : Type → Type} [Monad m] (handler : QueryImpl spec (StateT State m))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (defaultReply : (query : spec.Domain) → spec.Range query) :
    QueryImpl spec (StateT (State × Option Candidate) m) := fun query before =>
  match before.2 with
  | some _ => pure (defaultReply query, before)
  | none => monitor handler observe query before

/-- A selected frozen continuation issues no handler query and keeps exactly the stopping state. -/
theorem stopped {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl spec (StateT State m))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (defaultReply : (query : spec.Domain) → spec.Range query) (work : OracleComp spec Value)
    (before : State) (candidate : Candidate) :
    ∃ value, (simulateQ (freeze handler observe defaultReply) work).run (before, some candidate) =
      pure (value, (before, some candidate)) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp only [simulateQ_pure, StateT.run_pure]⟩
  | query_bind query next ih =>
      obtain ⟨value, same⟩ := ih (defaultReply query)
      refine ⟨value, ?_⟩
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, freeze, pure_bind]
      exact same

private theorem map_constant {A B : Type} (work : ProbComp A) (function : A → B) (value : B)
    (constant : ∀ result ∈ support work, function result = value) :
    EvalDistEq (function <$> work) (pure value : ProbComp B) := by
  rw [map_eq_bind_pure_comp]
  exact EvalDistEq.trans
    (OracleComp.EvalDistEq.bind_congr_of_support work fun result member => by simp only [Function.comp_apply, constant result member]; rfl)
    (OracleComp.EvalDistEq.bind_const work (pure value))

/-- The full monitor never overwrites an earlier selected candidate. -/
theorem monitor_retains (handler : QueryImpl spec (StateT State ProbComp))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (work : OracleComp spec Value) (before : State) (candidate : Candidate)
    (result : Value × (State × Option Candidate))
    (supported : result ∈ support ((simulateQ (monitor handler observe) work).run (before, some candidate))) :
    result.2.2 = some candidate := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, monitor,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨middle, ⟨queried, _possible, same⟩, continued⟩ := supported
      cases same
      exact ih queried.1 queried.2 result continued

/-- The candidate selected online has exactly the distribution of the full original monitored execution's first candidate. -/
theorem selected (handler : QueryImpl spec (StateT State ProbComp))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (defaultReply : (query : spec.Domain) → spec.Range query) (work : OracleComp spec Value)
    (before : State) (previous : Option Candidate) :
    EvalDistEq ((fun result : Value × (State × Option Candidate) => result.2.2) <$>
        (simulateQ (monitor handler observe) work).run (before, previous))
      ((fun result : Value × (State × Option Candidate) => result.2.2) <$>
        (simulateQ (freeze handler observe defaultReply) work).run (before, previous)) := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      cases previous with
      | some candidate =>
          obtain ⟨value, frozen⟩ := stopped handler observe defaultReply (spec.query query >>= next) before candidate
          rw [frozen, map_pure]
          exact map_constant _ _ _ fun result member => monitor_retains handler observe _ before candidate result member
      | none =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, freeze, monitor,
            map_bind, Option.orElse_none]
          apply EvalDistEq.bind_right
          intro middle
          exact ih middle.1 middle.2.1 middle.2.2

/-- Erasing only the analysis flag preserves the complete original return value and native state. -/
theorem monitor_erase (handler : QueryImpl spec (StateT State ProbComp))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (work : OracleComp spec Value) (before : State) (previous : Option Candidate) :
    (fun result : Value × (State × Option Candidate) => (result.1, result.2.1)) <$>
      (simulateQ (monitor handler observe) work).run (before, previous) =
      (simulateQ handler work).run before := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, monitor,
        map_bind, bind_pure_comp, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 middle.2 (previous.orElse fun _ => observe query before middle.1 middle.2)

/-- A frozen run retains actual state invariants and any selected candidate's same-cut property; after selection there is no later callback with which to invalidate it. -/
theorem freeze_property (handler : QueryImpl spec (StateT State ProbComp))
    (observe : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (defaultReply : (query : spec.Domain) → spec.Range query)
    (safe : State → Prop) (good : State → Candidate → Prop)
    (stepSafe : ∀ query before result, safe before → result ∈ support ((handler query).run before) → safe result.2)
    (captured : ∀ query before result candidate, safe before → result ∈ support ((handler query).run before) →
      observe query before result.1 result.2 = some candidate → good result.2 candidate)
    (work : OracleComp spec Value) (before : State) (previous : Option Candidate)
    (initialSafe : safe before) (initialGood : ∀ candidate, previous = some candidate → good before candidate)
    (result : Value × (State × Option Candidate))
    (supported : result ∈ support ((simulateQ (freeze handler observe defaultReply) work).run (before, previous))) :
    safe result.2.1 ∧ ∀ candidate, result.2.2 = some candidate → good result.2.1 candidate := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨initialSafe, initialGood⟩
  | query_bind query next ih =>
      cases previous with
      | some candidate =>
          obtain ⟨value, same⟩ := stopped handler observe defaultReply (spec.query query >>= next) before candidate
          rw [same] at supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact ⟨initialSafe, initialGood⟩
      | none =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, bind_apply, freeze, monitor,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨middle, ⟨queried, possible, same⟩, continued⟩ := supported
          cases same
          apply ih queried.1 queried.2 _ (stepSafe query before queried initialSafe possible) ?_ result continued
          intro candidate selected
          exact captured query before queried candidate initialSafe possible selected

end BeaconcryptCore.Computational.RegistrationNativeMldsaStop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStop.stopped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStop.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStop.monitor_retains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStop.monitor_retains

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStop.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStop.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStop.monitor_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStop.monitor_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaStop.freeze_property' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaStop.freeze_property
