-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop

/-! Two public analysis monitors run the same underlying callback once. A source-supported invariant and pointwise observer implication compare their first-candidate probabilities without conditioning on future generated keys. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder
open RegistrationNativeMldsaStop (Observer monitor)
variable {Query State Candidate Value : Type} {spec : OracleSpec Query}
private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

abbrev PairState := State × (Option Candidate × Option Candidate)

def pair {m : Type → Type} [Monad m] (handler : QueryImpl spec (StateT State m))
    (left right : Observer (spec := spec) (State := State) (Candidate := Candidate)) :
    QueryImpl spec (StateT (PairState (State := State) (Candidate := Candidate)) m) := fun query before => do
  let result ← (handler query).run before.1
  pure (result.1, (result.2, (before.2.1.orElse fun _ => left query before.1 result.1 result.2,
    before.2.2.orElse fun _ => right query before.1 result.1 result.2)))

def first (result : Value × PairState (State := State) (Candidate := Candidate)) : Value × (State × Option Candidate) :=
  (result.1, (result.2.1, result.2.2.1))

def second (result : Value × PairState (State := State) (Candidate := Candidate)) : Value × (State × Option Candidate) :=
  (result.1, (result.2.1, result.2.2.2))

/-- The first paired monitor is exactly its standalone source execution. -/
theorem first_program (handler : QueryImpl spec (StateT State ProbComp))
    (left right : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (work : OracleComp spec Value) (before : PairState (State := State) (Candidate := Candidate)) :
    first <$> (simulateQ (pair handler left right) work).run before =
      (simulateQ (monitor handler left) work).run (before.1, before.2.1) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, first]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, pair, monitor,
        StateT.run, map_bind, bind_pure_comp, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 _

/-- The second paired monitor is exactly its standalone source execution. -/
theorem second_program (handler : QueryImpl spec (StateT State ProbComp))
    (left right : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (work : OracleComp spec Value) (before : PairState (State := State) (Candidate := Candidate)) :
    second <$> (simulateQ (pair handler left right) work).run before =
      (simulateQ (monitor handler right) work).run (before.1, before.2.2) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, second]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, pair, monitor,
        StateT.run, map_bind, bind_pure_comp, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 _

private def Good (safe : State → Prop) (before : PairState (State := State) (Candidate := Candidate)) : Prop :=
  safe before.1 ∧ (before.2.1.isSome = true → before.2.2.isSome = true)

private theorem orElse_mono (left right addedLeft addedRight : Option Candidate)
    (previous : left.isSome = true → right.isSome = true)
    (current : addedLeft.isSome = true → addedRight.isSome = true) :
    (left.orElse fun _ => addedLeft).isSome = true → (right.orElse fun _ => addedRight).isSome = true := by
  cases left <;> cases right <;> cases addedLeft <;> cases addedRight <;>
    simp only [Option.orElse_none, Option.orElse_some, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, true_implies, false_implies] at previous current ⊢

private theorem good_program (handler : QueryImpl spec (StateT State ProbComp))
    (left right : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (safe : State → Prop)
    (preserves : ∀ query before result, safe before → result ∈ support ((handler query).run before) → safe result.2)
    (ordered : ∀ query before result, safe before → result ∈ support ((handler query).run before) →
      (left query before result.1 result.2).isSome = true → (right query before result.1 result.2).isSome = true)
    (work : OracleComp spec Value) (before : PairState (State := State) (Candidate := Candidate))
    (initial : Good safe before) (result : Value × PairState (State := State) (Candidate := Candidate))
    (supported : result ∈ support ((simulateQ (pair handler left right) work).run before)) :
    Good safe result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact initial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, pair,
        StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨middle, ⟨queried, possible, same⟩, continued⟩ := supported
      cases same
      refine ih queried.1 _ ?_ continued
      exact ⟨preserves query before.1 queried initial.1 possible,
        orElse_mono _ _ _ _ initial.2 (ordered query before.1 queried initial.1 possible)⟩

/-- Source-supported observer implication compares the full adaptive monitors' first-candidate probabilities. -/
theorem bound (handler : QueryImpl spec (StateT State ProbComp))
    (left right : Observer (spec := spec) (State := State) (Candidate := Candidate))
    (safe : State → Prop)
    (preserves : ∀ query before result, safe before → result ∈ support ((handler query).run before) → safe result.2)
    (ordered : ∀ query before result, safe before → result ∈ support ((handler query).run before) →
      (left query before result.1 result.2).isSome = true → (right query before result.1 result.2).isSome = true)
    (work : OracleComp spec Value) (before : State) (initial : safe before) :
    Pr{let result ← (simulateQ (monitor handler left) work).run (before, none)}[result.2.2.isSome = true] ≤
      Pr{let result ← (simulateQ (monitor handler right) work).run (before, none)}[result.2.2.isSome = true] := by
  rw [← first_program handler left right work (before, none, none),
    ← second_program handler left right work (before, none, none), prEvent_map, prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun result supported selected =>
    (good_program handler left right safe preserves ordered work (before, none, none)
      ⟨initial, by intro impossible; cases impossible⟩ result supported).2 selected
end BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.first_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.first_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.second_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.second_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder.bound
