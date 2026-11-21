-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace

/-! A private chronological journal may retain a proved analysis projection of each actual pre/post state. The live execution state remains complete. Erasure and state-interpretation transport preserve the same adaptive source tree; a projected journal is never exposed as an adversary interface. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace
open RegistrationNativeStageTrace (Call)
variable {Q S T View Value : Type} {spec : OracleSpec Q}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def mapCall (observe : S → View) (current : Call spec S) : Call spec View :=
  ⟨current.query, observe current.before, current.reply, observe current.after⟩

def handler (observe : S → View) (implementation : QueryImpl spec (StateT S m)) :
    QueryImpl spec (StateT (S × List (Call spec View)) m) := fun query before =>
  (fun result => (result.1, (result.2, before.2 ++ [⟨query, observe before.1, result.1, observe result.2⟩]))) <$>
    (implementation query).run before.1

/-- Forgetting only the private projected journal retains the complete actual state and adaptive value. -/
theorem erase (observe : S → View) (implementation : QueryImpl spec (StateT S m))
    (work : OracleComp spec Value) (before : S × List (Call spec View)) :
    Prod.map id Prod.fst <$> (simulateQ (handler observe implementation) work).run before =
      (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [handler, StateT.run, Functor.map_map, Prod.map, id_eq]
  exact id_map _

/-- An exact source-state interpretation also transports the same chronological journal when its retained observations factor through that interpretation. -/
theorem project (left : QueryImpl spec (StateT S m)) (right : QueryImpl spec (StateT T m))
    (projection : S → T) (observeLeft : S → View) (observeRight : T → View)
    (step : ∀ query before, Prod.map id projection <$> (left query).run before = (right query).run (projection before))
    (observations : ∀ before, observeLeft before = observeRight (projection before))
    (work : OracleComp spec Value) (before : S × List (Call spec View)) :
    Prod.map id (Prod.map projection id) <$> (simulateQ (handler observeLeft left) work).run before =
      (simulateQ (handler observeRight right) work).run (projection before.1, before.2) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [handler, StateT.run, Functor.map_map, Prod.map, id_eq]
  have law := congrArg (fun distribution =>
      (fun result : spec.Range query × T => (result.1, (result.2, current.2 ++
        [⟨query, observeRight (projection current.1), result.1, observeRight result.2⟩]))) <$> distribution)
    (step query current.1)
  simp only [StateT.run, Functor.map_map, Prod.map, id_eq] at law
  simpa only [observations] using law

/-- Projecting only the snapshots of the actual full-state source journal is exactly this private observed journal. -/
theorem full_project (observe : S → View) (implementation : QueryImpl spec (StateT S ProbComp))
    (work : OracleComp spec Value) (before : S × List (Call spec S)) :
    Prod.map id (fun current => (current.1, current.2.map (mapCall observe))) <$>
        (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run before =
      (simulateQ (handler observe implementation) work).run (before.1, before.2.map (mapCall observe)) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeStageTrace.handler, handler, StateT.run, Functor.map_map, Prod.map, id_eq,
    List.map_append, List.map_cons, List.map_nil, mapCall]
end BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.full_project' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservedStageTrace.full_project
