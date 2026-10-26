-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryProgram

/-! Early CBOR admission composes with adaptive source execution. Rejection
retains its complete specified state effect, including consumption of a moved
registration token. This is an operational equality, not a cryptographic bound
for the filtered experiment. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborCommandFilter
open PqxdhBoundaryProgram
variable {ι State X : Type} {spec : OracleSpec ι}

/-- Select a native operation from the current state and execute it at that same state. -/
def atState (implementation : State → StateT State ProbComp X) : StateT State ProbComp X :=
  fun state => (implementation state).run state

theorem atState_run (implementation : State → StateT State ProbComp X) (state : State) :
    (atState implementation).run state = (implementation state).run state := rfl

/-- Native commands with an early guard and an explicit complete rejection result. -/
def handler (allowed : spec.Domain → State → Bool)
    (reject : (query : spec.Domain) → State → spec.Range query × State)
    (implementation : QueryImpl spec (StateT State ProbComp)) :
    QueryImpl spec (StateT State ProbComp) :=
  fun query state => if allowed query state then (implementation query).run state
    else pure (reject query state)

/-- An admitted operation runs the original implementation at the same complete state. -/
theorem admitted_run (allowed : spec.Domain → State → Bool)
    (reject : (query : spec.Domain) → State → spec.Range query × State)
    (implementation : QueryImpl spec (StateT State ProbComp))
    (query : spec.Domain) (state : State) (admitted : allowed query state = true) :
    (handler allowed reject implementation query).run state = (implementation query).run state := by
  simp only [handler, StateT.run, admitted, ite_true]

/-- The same guard at the source boundary; rejection is an ordinary Rust return. -/
def source (allowed : spec.Domain → State → Bool)
    (reject : (query : spec.Domain) → State → spec.Range query × State)
    (step : Step spec State) : Step spec State :=
  fun query state => if allowed query state then step query state
    else pure (.ok (reject query state).1, (reject query state).2)

/-- The guard preserves exact per-command correspondence, including rejected poststates. -/
theorem step_exact (allowed : spec.Domain → State → Bool)
    (reject : (query : spec.Domain) → State → spec.Range query × State)
    (step : Step spec State) (implementation : QueryImpl spec (StateT State ProbComp))
    (operational : ∀ query state, step query state = liftStep implementation query state)
    (query : spec.Domain) (state : State) :
    source allowed reject step query state = liftStep (handler allowed reject implementation) query state := by
  cases admitted : allowed query state <;> simp [source, handler, liftStep, StateT.run, admitted, operational]

/-- Arbitrary adaptive clients see the same replies and complete states after early rejection. -/
theorem execute_exact (allowed : spec.Domain → State → Bool)
    (reject : (query : spec.Domain) → State → spec.Range query × State)
    (step : Step spec State) (implementation : QueryImpl spec (StateT State ProbComp))
    (operational : ∀ query state, step query state = liftStep implementation query state)
    (work : OracleComp spec X) (state : State) :
    execute (source allowed reject step) work state =
      (fun result => (.ok result.1, result.2)) <$>
        (simulateQ (handler allowed reject implementation) work).run state :=
  PqxdhBoundaryProgram.source_exact _ _ (step_exact allowed reject step implementation operational) work state

end BeaconcryptCore.Computational.CborCommandFilter

/-- info: 'BeaconcryptCore.Computational.CborCommandFilter.atState_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborCommandFilter.atState_run

/-- info: 'BeaconcryptCore.Computational.CborCommandFilter.admitted_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborCommandFilter.admitted_run

/-- info: 'BeaconcryptCore.Computational.CborCommandFilter.step_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborCommandFilter.step_exact

/-- info: 'BeaconcryptCore.Computational.CborCommandFilter.execute_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborCommandFilter.execute_exact
