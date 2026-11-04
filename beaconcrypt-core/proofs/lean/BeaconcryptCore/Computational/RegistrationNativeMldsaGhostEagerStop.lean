-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution

/-! The dynamic free tracked stopping program is interpreted by the same complete eager callbacks used in the learned-key monitor comparison. Only state association changes; source replies, primitive order, native state, public ghost and private signing prefix all remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerStop
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGhostState (track)
open RegistrationNativeMldsaStop (Observer freeze monitor)
variable {S V Query Candidate : Type} {queries : OracleSpec Query} (source : Source)

private theorem map_apply {T A B : Type} (observer : A → B) (work : StateT T ProbComp A) (before : T) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

def observe (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate)) :
    Observer (spec := queries) (State := S × RegistrationNativeMldsaGenerationGhost.State) (Candidate := Candidate) :=
  fun query before reply after => after.2.publicKey.bind (fun publicKey => observer publicKey query before.1 reply after.1)

def arrange (result : (V × ((S × RegistrationNativeMldsaGenerationGhost.State) × Option Candidate)) × Pool source) :=
  (result.1.1, ((result.1.2.1.1, (result.1.2.1.2, result.2)), result.1.2.2))

private theorem query (selected : Nat) (tape : List (Option (Credential source)))
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (query : queries.Domain)
    (before : S × RegistrationNativeMldsaGenerationGhost.State) (previous : Option Candidate) (pool : Pool source) :
    arrange source <$> RegistrationNativeMldsaSharedStop.runState (handleSource source)
      (RegistrationNativeMldsaEager.handler source tape)
      (freeze (fun query => track source selected (handler query)) (observe observer) defaultReply query) (before, previous) pool =
      (freeze (fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (handler query))
        (RegistrationNativeMldsaGhostEagerExecution.dynamic source observer) defaultReply query).run
          ((before.1, (before.2, pool)), previous) := by
  cases previous with
  | none =>
      simp only [freeze, monitor, StateT.run, bind_pure_comp, RegistrationNativeMldsaSharedStop.runState,
        simulateQ_map, Functor.map_map, RegistrationNativeMldsaGhostEagerExecution.execute,
        RegistrationNativeMldsaGhostEagerExecution.dynamic, observe]
      rw [map_apply, Functor.map_map]
      rfl
  | some candidate =>
      simp only [freeze, StateT.run, RegistrationNativeMldsaSharedStop.runState, simulateQ_pure]
      rfl

/-- Complete dynamic free execution and the shared eager tracked stopping callbacks have exactly the same full stopping state and private source history. -/
theorem program (selected : Nat) (tape : List (Option (Credential source)))
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries V)
    (before : S × RegistrationNativeMldsaGenerationGhost.State) (previous : Option Candidate) (pool : Pool source) :
    arrange source <$> RegistrationNativeMldsaSharedStop.runState (handleSource source)
      (RegistrationNativeMldsaEager.handler source tape)
      (simulateQ (freeze (fun query => track source selected (handler query)) (observe observer) defaultReply) work) (before, previous) pool =
      (simulateQ (freeze (fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (handler query))
        (RegistrationNativeMldsaGhostEagerExecution.dynamic source observer) defaultReply) work).run
          ((before.1, (before.2, pool)), previous) := by
  induction work using OracleComp.inductionOn generalizing before previous pool with
  | pure value =>
      simp only [simulateQ_pure, RegistrationNativeMldsaSharedStop.runState, StateT.run_pure, map_pure, arrange]
  | query_bind asked next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaSharedStop.runState,
        StateT.run_bind, simulateQ_bind, map_bind]
      rw [← query source selected tape handler observer defaultReply asked before previous pool, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1.1 middle.1.2.1 middle.1.2.2 middle.2
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerStop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerStop.program
