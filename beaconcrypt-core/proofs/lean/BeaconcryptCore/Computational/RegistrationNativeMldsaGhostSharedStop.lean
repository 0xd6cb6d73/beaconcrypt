-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSharedStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostState

/-! The dynamic free tracked stopping program interprets all requests through one arbitrary shared stateful source backend. Only state association changes; source replies, primitive order, native state, public ghost and private backend state all remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostSharedStop
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGhostState (track)
open RegistrationNativeMldsaStop (Observer freeze monitor)
variable {S V Query Candidate Private : Type} {queries : OracleSpec Query} (source : Source)
variable (backend : QueryImpl (Spec (handleSource source)) (StateT Private ProbComp))

noncomputable def execute (selected : Nat)
    (work : StateT S (OracleComp (Spec (handleSource source))) V) :
    StateT (S × (RegistrationNativeMldsaGenerationGhost.State × Private)) ProbComp V := fun before =>
  (fun result => (result.1.1, (result.1.2.1, (result.1.2.2, result.2)))) <$>
    (simulateQ backend ((track source selected work).run (before.1, before.2.1))).run before.2.2

def dynamic (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate)) :
    Observer (spec := queries) (State := S × (RegistrationNativeMldsaGenerationGhost.State × Private)) (Candidate := Candidate) :=
  fun query before reply after => after.2.1.publicKey.bind (fun publicKey => observer publicKey query before.1 reply after.1)

private theorem map_apply {T A B : Type} (observer : A → B) (work : StateT T ProbComp A) (before : T) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

def observe (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate)) :
    Observer (spec := queries) (State := S × RegistrationNativeMldsaGenerationGhost.State) (Candidate := Candidate) :=
  fun query before reply after => after.2.publicKey.bind (fun publicKey => observer publicKey query before.1 reply after.1)

def arrange (result : (V × ((S × RegistrationNativeMldsaGenerationGhost.State) × Option Candidate)) × Private) :=
  (result.1.1, ((result.1.2.1.1, (result.1.2.1.2, result.2)), result.1.2.2))

private theorem query (selected : Nat)
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (query : queries.Domain)
    (before : S × RegistrationNativeMldsaGenerationGhost.State) (previous : Option Candidate) (pool : Private) :
    arrange <$> RegistrationNativeMldsaSharedStop.runState (handleSource source)
      (backend)
      (freeze (fun query => track source selected (handler query)) (observe observer) defaultReply query) (before, previous) pool =
      (freeze (fun query => execute source backend selected (handler query))
        (dynamic observer) defaultReply query).run
          ((before.1, (before.2, pool)), previous) := by
  cases previous with
  | none =>
      simp only [freeze, monitor, StateT.run, bind_pure_comp, RegistrationNativeMldsaSharedStop.runState,
        simulateQ_map, Functor.map_map, execute, dynamic, observe]
      rw [map_apply, Functor.map_map]
      rfl
  | some candidate =>
      simp only [freeze, StateT.run, RegistrationNativeMldsaSharedStop.runState, simulateQ_pure]
      rfl

/-- Complete dynamic free execution and the shared tracked stopping callbacks have exactly the same full stopping state and private source history. -/
theorem program (selected : Nat)
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries V)
    (before : S × RegistrationNativeMldsaGenerationGhost.State) (previous : Option Candidate) (pool : Private) :
    arrange <$> RegistrationNativeMldsaSharedStop.runState (handleSource source)
      (backend)
      (simulateQ (freeze (fun query => track source selected (handler query)) (observe observer) defaultReply) work) (before, previous) pool =
      (simulateQ (freeze (fun query => execute source backend selected (handler query))
        (dynamic observer) defaultReply) work).run
          ((before.1, (before.2, pool)), previous) := by
  induction work using OracleComp.inductionOn generalizing before previous pool with
  | pure value =>
      simp only [simulateQ_pure, RegistrationNativeMldsaSharedStop.runState, StateT.run_pure, map_pure, arrange]
  | query_bind asked next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaSharedStop.runState,
        StateT.run_bind, simulateQ_bind, map_bind]
      rw [← query source backend selected handler observer defaultReply asked before previous pool, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1.1 middle.1.2.1 middle.1.2.2 middle.2
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostSharedStop


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostSharedStop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostSharedStop.program
