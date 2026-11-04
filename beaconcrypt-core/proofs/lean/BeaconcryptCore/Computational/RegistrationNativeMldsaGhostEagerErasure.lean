-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerExecution

/-! Erasing public generation tracking preserves the complete native value, private source table and fixed-key stopping candidate. This retains all source failures and the ordinary signing prefix while removing only analysis metadata. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaGhostEagerExecution (State execute constant)
open RegistrationNativeMldsaStop (Observer freeze monitor)
variable {S V Query Candidate : Type} {queries : OracleSpec Query} (source : Source)

private theorem bind_apply {m : Type → Type} [Monad m] {T A B : Type}
    (work : StateT T m A) (next : A → StateT T m B) (before : T) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private theorem map_apply {T A B : Type} (observer : A → B) (work : StateT T ProbComp A) (before : T) :
    (observer <$> work) before = Prod.map observer id <$> work before := StateT.run_map observer work before

def view (before : State (S := S) source) := (before.1, before.2.2)

noncomputable def plain (tape : List (Option (Credential source)))
    (work : StateT S (OracleComp (Spec (handleSource source))) V) : StateT (S × Pool source) ProbComp V :=
  fun before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeMldsaEager.handler source tape) (work.run before.1)).run before.2

/-- Erasing only tracking retains the exact joint native continuation and complete private eager table. -/
theorem execute (selected : Nat) (tape : List (Option (Credential source)))
    (work : StateT S (OracleComp (Spec (handleSource source))) V) (before : State (S := S) source) :
    Prod.map id (view source) <$> (RegistrationNativeMldsaGhostEagerExecution.execute source selected tape work).run before =
      (plain source tape work).run (view source before) := by
  have same := congrArg (fun program => (simulateQ (RegistrationNativeMldsaEager.handler source tape) program).run before.2.2)
    (RegistrationNativeMldsaGhostState.erase source selected work before.1 before.2.1)
  simp only [simulateQ_map, StateT.run_map] at same
  have mapped := congrArg (fun program => (fun result => (result.1.1, (result.1.2, result.2))) <$> program) same
  simp only [Functor.map_map] at mapped
  simpa only [RegistrationNativeMldsaGhostEagerExecution.execute, plain, StateT.run,
    view, Functor.map_map, Prod.map, id_eq] using mapped

def observe (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) : Observer (spec := queries) (State := S × Pool source) (Candidate := Candidate) :=
  fun query before reply after => observer publicKey query before.1 reply after.1

def arrange (result : V × (State (S := S) source × Option Candidate)) :=
  (result.1, (view source result.2.1, result.2.2))

private theorem query (selected : Nat) (tape : List (Option (Credential source)))
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : queries.Domain) → queries.Range query) (query : queries.Domain)
    (before : State (S := S) source) (previous : Option Candidate) :
    arrange source <$> (freeze (fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (handler query))
      (constant source observer publicKey) defaultReply query).run (before, previous) =
      (freeze (fun query => plain source tape (handler query)) (observe source observer publicKey) defaultReply query).run
        (view source before, previous) := by
  cases previous with
  | some candidate =>
      simp only [freeze, StateT.run, map_pure, arrange]
  | none =>
      have same := congrArg (fun program => (fun result => (result.1,
          (result.2, observe source observer publicKey query (view source before) result.1 result.2))) <$> program)
        (execute source selected tape (handler query) before)
      simp only [Functor.map_map] at same
      simpa only [freeze, monitor, StateT.run, bind_pure_comp, Functor.map_map,
        arrange, constant, observe, view, Prod.map, id_eq, Option.orElse_none] using same

/-- Complete fixed-key stopped eager execution preserves the candidate, native state and raw private signing prefix after tracking erasure. -/
theorem program (selected : Nat) (tape : List (Option (Credential source)))
    (handler : QueryImpl queries (StateT S (OracleComp (Spec (handleSource source)))))
    (observer : RegistrationNativeMldsaEuf.PublicKey → Observer (spec := queries) (State := S) (Candidate := Candidate))
    (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (defaultReply : (query : queries.Domain) → queries.Range query) (work : OracleComp queries V)
    (before : State (S := S) source) (previous : Option Candidate) :
    arrange source <$> (simulateQ (freeze (fun query => RegistrationNativeMldsaGhostEagerExecution.execute source selected tape (handler query))
      (constant source observer publicKey) defaultReply) work).run (before, previous) =
      (simulateQ (freeze (fun query => plain source tape (handler query)) (observe source observer publicKey) defaultReply) work).run
        (view source before, previous) := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, arrange]
  | query_bind asked next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query source selected tape handler observer publicKey defaultReply asked before previous, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 middle.2.1 middle.2.2
end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure.execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure.execute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostEagerErasure.program
