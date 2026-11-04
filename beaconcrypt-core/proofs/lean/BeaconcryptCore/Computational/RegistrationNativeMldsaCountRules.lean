-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountMap

/-! Count-normalized source programs compose only after proving both ordinary input independence and the normalized continuation equation. These checked rules preserve complete stateful control flow for arbitrary named ML optional replies, rather than assuming that count erasure is invisible to a whole protocol. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountMap (Natural transform)
variable {source : RegistrationNativeMldsa.Source} {State Value Next : Type} {n : Nat}

def Correct (projection : State → State) (work : StateT State (OracleComp (Spec source)) Value) : Prop :=
  RegistrationStateView.Stable projection work ∧ Natural projection work

/-- Pure source returns preserve both original and normalized projected poststate. -/
theorem pure (projection : State → State) (idempotent : ∀ before, projection (projection before) = projection before)
    (value : Value) : Correct projection (pure value : StateT State (OracleComp (Spec source)) Value) := by
  refine ⟨RegistrationStateView.pure_stable projection idempotent value, ?_⟩
  intro before
  simp only [StateT.run_pure, transform, simulateQ_pure, map_pure, Prod.map, id_eq, idempotent]

/-- Complete adaptive sequencing preserves normalized source behavior with each reached native state threaded literally. -/
theorem bind (projection : State → State) (work : StateT State (OracleComp (Spec source)) Value)
    (next : Value → StateT State (OracleComp (Spec source)) Next)
    (first : Correct projection work) (rest : ∀ value, Correct projection (next value)) :
    Correct projection (work >>= next) := by
  refine ⟨RegistrationStateView.bind_stable projection work next first.1 (fun value => (rest value).1), ?_⟩
  intro before
  simp only [StateT.run_bind, transform, simulateQ_bind, map_bind]
  change (simulateQ RegistrationNativeMldsaCountMap.translation (work.run before) >>= fun result =>
    Prod.map id projection <$> transform ((next result.1).run result.2)) = _
  calc
    _ = transform (work.run before) >>= fun result =>
        Prod.map id projection <$> (next result.1).run (projection result.2) := by
      apply bind_congr
      intro result
      exact (rest result.1).2 result.2
    _ = (Prod.map id projection <$> transform (work.run before)) >>= fun result =>
        Prod.map id projection <$> (next result.1).run result.2 := by rw [bind_map_left]; rfl
    _ = (Prod.map id projection <$> work.run (projection before)) >>= fun result =>
        Prod.map id projection <$> (next result.1).run result.2 := by rw [first.2 before]
    _ = work.run (projection before) >>= fun result =>
        Prod.map id projection <$> (next result.1).run (projection result.2) := by rw [bind_map_left]; rfl
    _ = _ := by
      apply bind_congr
      intro result
      exact ((rest result.1).1 result.2).symm

/-- Every adaptive source-oracle program inherits the checked two-part laws of its actual callbacks. -/
theorem simulate {Query : Type} {queries : OracleSpec Query}
    (projection : State → State) (idempotent : ∀ before, projection (projection before) = projection before)
    (implementation : QueryImpl queries (StateT State (OracleComp (Spec source))))
    (law : ∀ query, Correct projection (implementation query)) (work : OracleComp queries Value) :
    Correct projection (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure projection idempotent value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind projection _ _ (law query) ih

/-- Actual closed ordinary source work lifts into both sides of the normalized free-language law. -/
theorem closed (projection : State → State) (work : StateT State ProbComp Value)
    (stable : RegistrationNativeKemCounterIndependence.Stable projection work) :
    Correct projection (RegistrationNativeMldsaProgram.liftState (source := source) work) := by
  refine ⟨?_, RegistrationNativeMldsaCountMap.closed projection work stable⟩
  intro before
  have same := congrArg (RegistrationNativeMldsaProgram.lift (source := source)) (stable before)
  simp only [RegistrationNativeMldsaProgram.lift, simulateQ_map] at same
  exact same

/-- The actual named ML callback satisfies both free continuation laws for every reply and draw count. -/
theorem call (accounting : RegistrationNativeMldsaCapability.Accounting)
    (query : RegistrationNativeMldsaCapability.Request source) :
    Correct RegistrationNativeMldsaWorldView.project (RegistrationNativeMldsaProgram.call (n := n) accounting query) := by
  refine ⟨?_, RegistrationNativeMldsaCountMap.call accounting query⟩
  intro before
  rw [RegistrationNativeMldsaWorldView.call, RegistrationNativeMldsaWorldView.call,
    RegistrationNativeMldsaWorldView.idempotent]
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRules.call
