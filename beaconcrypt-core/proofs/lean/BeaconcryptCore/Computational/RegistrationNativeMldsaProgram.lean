-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCapability

/-! Ordinary source randomness and private ML leaves form an additive program language. Its evaluator preserves complete stateful continuations, maps and failure branches; only the actual generate/sign leaves are named capabilities. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
open RegistrationNativeMldsaCapability (Request Reply Accounting advance)
variable {source : RegistrationNativeMldsa.Source} {State Value Next : Type} {n : Nat}

abbrev Spec (source : RegistrationNativeMldsa.Source) := unifSpec + RegistrationNativeMldsaCapability.Spec source

def ordinary : QueryImpl unifSpec (OracleComp (Spec source)) :=
  fun query => (Spec source).query (.inl query)

noncomputable def actual : QueryImpl (Spec source) ProbComp
  | .inl query => unifSpec.query query
  | .inr query => RegistrationNativeMldsaCapability.actual source query

def lift (work : ProbComp Value) : OracleComp (Spec source) Value := simulateQ ordinary work

noncomputable def evaluate (work : OracleComp (Spec source) Value) : ProbComp Value := simulateQ actual work

/-- Ordinary probabilistic source work is retained literally by the additive ML evaluator. -/
theorem evaluate_lift (work : ProbComp Value) : evaluate (source := source) (lift work) = work := by
  have restriction : actual (source := source) ∘ₛ ordinary = QueryImpl.id' unifSpec := by
    funext query
    simp only [QueryImpl.apply_compose, ordinary, simulateQ_spec_query, actual, QueryImpl.id'_apply]
  rw [evaluate, lift, ← QueryImpl.simulateQ_compose, restriction, simulateQ_id']

noncomputable def evalState (work : StateT State (OracleComp (Spec source)) Value) : StateT State ProbComp Value :=
  fun before => evaluate (work.run before)

def liftState (work : StateT State ProbComp Value) : StateT State (OracleComp (Spec source)) Value :=
  fun before => lift (work.run before)

/-- Stateful ordinary source components keep their complete original poststate. -/
theorem eval_liftState (work : StateT State ProbComp Value) : evalState (source := source) (liftState work) = work := by
  funext before
  exact evaluate_lift (work.run before)

/-- Evaluation retains the actual state threaded between private ML and ordinary source work. -/
theorem eval_bind (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next) :
    evalState (work >>= next) = (evalState work >>= fun value => evalState (next value)) := by
  funext before
  simp only [evalState, evaluate, StateT.run_bind, simulateQ_bind]
  rfl

/-- Evaluation retains a literal source return value and state. -/
theorem eval_pure (value : Value) : evalState (source := source) (pure value : StateT State _ Value) = pure value := by
  funext before
  simp only [evalState, evaluate, StateT.run_pure, simulateQ_pure]
  rfl

/-- Adaptive private primitive programs retain every reached callback under evaluation. -/
theorem eval_simulate {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (StateT State (OracleComp (Spec source)))) (work : OracleComp spec Value) :
    evalState (simulateQ implementation work) = simulateQ (fun query => evalState (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, eval_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, eval_bind, ih]

noncomputable def call (accounting : Accounting) (query : Request source) :
    StateT (PqxdhRecordLiftWorld.State n) (OracleComp (Spec source)) (Reply query) := fun before => do
  let reply ← (Spec source).query (.inr query)
  pure (reply.1, advance accounting before reply.2)

/-- Reified actual ML leaf evaluation preserves native-only or Env accounting and the complete existing World. -/
theorem eval_call (accounting : Accounting) (query : Request source) :
    evalState (call (n := n) accounting query) =
      match accounting with
      | .native => PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsaCapability.draw query)
      | .environment => simulateQ PqxdhRecordLiftWorld.effects
          (simulateQ RegistrationWorldCoinCompiler.envCoin (RegistrationNativeMldsaCapability.draw query)) := by
  funext before
  simp only [evalState, evaluate, call, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query, actual]
  cases accounting with
  | native => exact RegistrationNativeMldsaCapability.native_count (RegistrationNativeMldsaCapability.draw query) before
  | environment => exact RegistrationNativeMldsaCapability.environment_count (RegistrationNativeMldsaCapability.draw query) before

end BeaconcryptCore.Computational.RegistrationNativeMldsaProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.evaluate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.evaluate_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_liftState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_liftState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_simulate
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaProgram.eval_call
