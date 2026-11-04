-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState

/-! Interpreting a free client keeps the complete private service state separate. Private projected journals commute with this interpretation and preserve their actual chronology; only the representation of the live client/service/journal product changes. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStateInterpreter
open RegistrationNativeStageTrace (Call)
variable {K Q S Private View Value Next : Type} {spec : OracleSpec K} {queries : OracleSpec Q}

def interpret (implementation : QueryImpl spec (StateT Private ProbComp))
    (work : StateT S (OracleComp spec) Value) : StateT (S × Private) ProbComp Value :=
  RegistrationNativePlatformPackedState.pack (RegistrationNativePlatformInterpret.state implementation work)

/-- A source return changes neither live client nor private service state. -/
theorem pure_interpret (implementation : QueryImpl spec (StateT Private ProbComp)) (value : Value) :
    interpret implementation (pure value : StateT S (OracleComp spec) Value) = pure value := by
  unfold interpret
  rw [RegistrationNativePlatformInterpret.state_pure, RegistrationNativePlatformPackedState.pure_pack]

/-- Every adaptive source continuation receives its exact reached client and private service states. -/
theorem bind_interpret (implementation : QueryImpl spec (StateT Private ProbComp))
    (work : StateT S (OracleComp spec) Value) (next : Value → StateT S (OracleComp spec) Next) :
    interpret implementation (work >>= next) = (interpret implementation work >>= fun value => interpret implementation (next value)) := by
  unfold interpret
  rw [RegistrationNativePlatformInterpret.state_bind, RegistrationNativePlatformPackedState.bind_pack]

/-- Typed source simulation commutes with the complete private interpretation. -/
theorem simulate_interpret (implementation : QueryImpl spec (StateT Private ProbComp))
    (compiler : QueryImpl queries (StateT S (OracleComp spec))) (work : OracleComp queries Value) :
    interpret implementation (simulateQ compiler work) = simulateQ (fun query => interpret implementation (compiler query)) work := by
  unfold interpret
  rw [RegistrationNativePlatformInterpret.state_simulate, RegistrationNativePlatformPackedState.simulate_pack]

def arrange (current : (S × List (Call queries View)) × Private) : (S × Private) × List (Call queries View) :=
  ((current.1.1, current.2), current.1.2)

private theorem map_apply {State A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT State m A) (before : State) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

/-- Each actually interpreted callback records exactly its client observations while retaining the whole private service poststate. -/
theorem observed_query (implementation : QueryImpl spec (StateT Private ProbComp)) (observe : S → View)
    (compiler : QueryImpl queries (StateT S (OracleComp spec))) (query : queries.Domain)
    (before : S) (journal : List (Call queries View)) (privateBefore : Private) :
    Prod.map id arrange <$>
        (interpret implementation (RegistrationNativeObservedStageTrace.handler observe compiler query)).run ((before, journal), privateBefore) =
      (RegistrationNativeObservedStageTrace.handler (fun current : S × Private => observe current.1)
        (fun query => interpret implementation (compiler query)) query).run ((before, privateBefore), journal) := by
  simp only [interpret, RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformInterpret.state,
    RegistrationNativeObservedStageTrace.handler, StateT.run, simulateQ_map, map_apply, Functor.map_map, arrange,
    Prod.map, id_eq]

/-- The complete adaptive typed journal has the same chronology and full state under private interpretation. -/
theorem observed_program (implementation : QueryImpl spec (StateT Private ProbComp)) (observe : S → View)
    (compiler : QueryImpl queries (StateT S (OracleComp spec))) (work : OracleComp queries Value)
    (before : (S × List (Call queries View)) × Private) :
    Prod.map id arrange <$>
        (interpret implementation (simulateQ (RegistrationNativeObservedStageTrace.handler observe compiler) work)).run before =
      (simulateQ (RegistrationNativeObservedStageTrace.handler (fun current : S × Private => observe current.1)
        (fun query => interpret implementation (compiler query))) work).run (arrange before) := by
  rw [simulate_interpret]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  exact observed_query implementation observe compiler query current.1.1 current.1.2 current.2
end BeaconcryptCore.Computational.RegistrationNativeStateInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.pure_interpret' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.pure_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.bind_interpret' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.bind_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.simulate_interpret' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.simulate_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.observed_query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.observed_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.observed_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStateInterpreter.observed_program
