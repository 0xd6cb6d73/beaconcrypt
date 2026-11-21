-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram

/-! A stopped stateful source program interprets all of its primitive requests through one arbitrary shared interpreter. Reassociation retains the native state, shared private interpreter state, first candidate and every reached failure prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop
open RegistrationNativeMldsaStop (Observer freeze)
variable {Index State Candidate Value Private : Type} {queries : OracleSpec Index}
variable (source : RegistrationNativeMldsa.Source)
variable (backend : QueryImpl (RegistrationNativeMldsaProgram.Spec source) (StateT Private ProbComp))

noncomputable def runState (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source)) Value)
    (current : State) (privateState : Private) : ProbComp ((Value × State) × Private) :=
  (simulateQ backend (work.run current)).run privateState

private theorem run_pure (value : Value) (current : State) (privateState : Private) :
    runState source backend (pure value) current privateState = pure ((value, current), privateState) := by
  simp only [runState, StateT.run_pure, simulateQ_pure, StateT.run_pure]

private theorem run_bind {Next : Type}
    (work : StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source)) Value)
    (next : Value → StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source)) Next)
    (current : State) (privateState : Private) :
    runState source backend (work >>= next) current privateState = (do
      let result ← runState source backend work current privateState
      runState source backend (next result.1.1) result.1.2 result.2) := by
  simp only [runState, StateT.run_bind, simulateQ_bind, StateT.run_bind]

/-- Reassociate the actual table state; no field is erased. -/
def arrange (result : (Value × (State × Option Candidate)) × Private) :
    Value × ((State × Private) × Option Candidate) :=
  (result.1.1, ((result.1.2.1, result.2), result.1.2.2))

noncomputable def callback (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source)))) :
    QueryImpl queries (StateT (State × Private) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> runState source backend (handler query) before.1 before.2

def observer (observe : Observer (spec := queries) (State := State) (Candidate := Candidate)) :
    Observer (spec := queries) (State := State × Private) (Candidate := Candidate) :=
  fun query before reply after => observe query before.1 reply after.1

private theorem map_apply {S A B : Type} (function : A → B) (work : StateT S ProbComp A) (before : S) :
    (function <$> work) before = (fun pair => (function pair.1, pair.2)) <$> work before :=
  StateT.run_map function work before

/-- One actual stopped capability callback is exactly its stopped table interpretation, including the no-query branch after selection. -/
theorem query (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source))))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query)
    (query : queries.Domain) (current : State) (previous : Option Candidate) (pool : Private) :
    arrange <$> runState source backend (freeze handler observe defaultReply query) (current, previous) pool =
      (freeze (callback source backend handler) (observer observe) defaultReply query).run ((current, pool), previous) := by
  cases previous with
  | none =>
    simp only [freeze, RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp,
      runState,
      simulateQ_map, Functor.map_map, callback, observer]
    rw [map_apply, Functor.map_map]
    rfl
  | some candidate =>
    change arrange <$> runState source backend (pure (defaultReply query)) (current, some candidate) pool =
      pure (defaultReply query, ((current, pool), some candidate))
    rw [run_pure, map_pure]
    rfl

/-- Every adaptive free stopped program equals its actual same-cut table callback execution, jointly in native state, pool and candidate. -/
theorem program (handler : QueryImpl queries (StateT State (OracleComp (RegistrationNativeMldsaProgram.Spec source))))
    (observe : Observer (spec := queries) (State := State) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries Value)
    (current : State) (previous : Option Candidate) (pool : Private) :
    arrange <$> runState source backend (simulateQ (freeze handler observe defaultReply) work) (current, previous) pool =
      (simulateQ (freeze (callback source backend handler) (observer observe) defaultReply) work).run ((current, pool), previous) := by
  induction work using OracleComp.inductionOn generalizing current previous pool with
  | pure value => simp only [simulateQ_pure, run_pure, map_pure, StateT.run_pure]; rfl
  | query_bind asked next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, run_bind, map_bind,
      StateT.run_bind]
    rw [← query source backend handler observe defaultReply asked current previous pool, bind_map_left]
    apply bind_congr
    intro middle
    exact ih middle.1.1 middle.1.2.1 middle.1.2.2 middle.2

end BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop.program
