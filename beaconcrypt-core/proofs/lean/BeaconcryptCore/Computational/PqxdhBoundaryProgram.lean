-- SPDX-License-Identifier: 0BSD
import Aeneas
import CoreModels
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! Generic adaptive source execution. Every Rust result keeps the complete poststate; fail/div stop without running the client's later commands. Concrete protocol steps are separate consumers. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryProgram
variable {ι State X Y Z : Type} {spec : OracleSpec ι}

/-- A source command returns its literal Rust outcome and full state, including effects before failure. -/
abbrev Step (spec : OracleSpec ι) (State : Type) :=
  (query : spec.Domain) → State → ProbComp (RustM (spec.Range query) × State)

/-- Only an actual successful reply enters the original adaptive continuation. -/
def resume (next : X → State → ProbComp (RustM Y × State))
    (result : RustM X × State) : ProbComp (RustM Y × State) :=
  match result.1 with
  | .ok value => next value result.2
  | .fail error => pure (.fail error, result.2)
  | .div => pure (.div, result.2)

/-- Structural execution follows every actual query, reply and complete state; it adds no primitive call. -/
def execute (step : Step spec State) (work : OracleComp spec X) (state : State) :
    ProbComp (RustM X × State) :=
  OracleComp.construct (C := fun _ => State → ProbComp (RustM X × State))
    (fun value before => pure (.ok value, before))
    (fun query _ recurse before => step query before >>= resume recurse) work state

theorem execute_pure (step : Step spec State) (value : X) (state : State) :
    execute step (pure value) state = pure (.ok value, state) := by
  simp only [execute, OracleComp.construct_pure]

/-- One command's literal Rust outcome decides whether the unchanged adaptive continuation runs. -/
theorem execute_query (step : Step spec State) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec X) (state : State) :
    execute step ((spec.query query : OracleComp spec _) >>= next) state =
      step query state >>= resume (fun reply after => execute step (next reply) after) := by
  simp only [execute, OracleComp.construct_query_bind]

/-- Sequential source execution retains failure/div effects and starts the next client only after a successful complete prefix. -/
theorem execute_bind (step : Step spec State) (work : OracleComp spec X)
    (next : X → OracleComp spec Y) (state : State) :
    execute step (work >>= next) state =
      execute step work state >>= resume (fun value after => execute step (next value) after) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [pure_bind, execute_pure, pure_bind, resume]
  | query_bind query tail ih =>
      simp only [bind_assoc, execute_query]
      apply bind_congr
      rintro ⟨outcome, after⟩
      cases outcome <;> simp only [resume, pure_bind, ih]

/-- A failed command retains its actual poststate and never calls the later adaptive client. -/
theorem execute_fail (step : Step spec State) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec X) (before after : State) (error : Error)
    (failed : step query before = pure (.fail error, after)) :
    execute step ((spec.query query : OracleComp spec _) >>= next) before = pure (.fail error, after) := by
  simp only [execute_query, failed, pure_bind, resume]

/-- The extracted divergence outcome is propagated with the same poststate and no subsequent command. -/
theorem execute_div (step : Step spec State) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec X) (before after : State)
    (diverged : step query before = pure (.div, after)) :
    execute step ((spec.query query : OracleComp spec _) >>= next) before = pure (.div, after) := by
  simp only [execute_query, diverged, pure_bind, resume]

/-- Pointwise equality must include each literal reply and complete poststate, not a selected projection. -/
theorem execute_congr (left right : Step spec State)
    (same : ∀ query state, left query state = right query state)
    (work : OracleComp spec X) (state : State) :
    execute left work state = execute right work state := by
  have equal : left = right := funext (fun query => funext (same query))
  rw [equal]

/-- Wrap only the actual native reply in Rust success; every primitive call and complete native poststate remains unchanged. -/
def liftStep (implementation : QueryImpl spec (StateT State ProbComp)) : Step spec State :=
  fun query state => (fun result => (.ok result.1, result.2)) <$> (implementation query).run state

/-- Adaptive structural execution of lifted native commands equals the full native simulation, including the final reply and every state field. -/
theorem execute_lift (implementation : QueryImpl spec (StateT State ProbComp))
    (work : OracleComp spec X) (state : State) :
    execute (liftStep implementation) work state =
      (fun result => (.ok result.1, result.2)) <$> (simulateQ implementation work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [execute_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query tail ih =>
      simp only [execute_query, liftStep, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        ← bind_pure_comp, bind_assoc, pure_bind, resume]
      simp only [ih, bind_pure_comp]

/-- A concrete consumer must prove the operational equality for every command and complete state; this theorem only composes those exact steps. -/
theorem source_exact (source : Step spec State)
    (implementation : QueryImpl spec (StateT State ProbComp))
    (operational : ∀ query state, source query state = liftStep implementation query state)
    (work : OracleComp spec X) (state : State) :
    execute source work state =
      (fun result => (.ok result.1, result.2)) <$> (simulateQ implementation work).run state := by
  exact (execute_congr source (liftStep implementation) operational work state).trans
    (execute_lift implementation work state)

/-- Any continuation sees the literal returned value and complete poststate; no projection, successful-run conditioning or event premise is introduced. -/
theorem source_continuation (source : Step spec State)
    (implementation : QueryImpl spec (StateT State ProbComp))
    (operational : ∀ query state, source query state = liftStep implementation query state)
    (work : OracleComp spec X) (state : State)
    (next : RustM X × State → ProbComp Y) :
    (execute source work state >>= next) =
      ((simulateQ implementation work).run state >>= fun result => next (.ok result.1, result.2)) := by
  rw [source_exact source implementation operational work state]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]

/-- Adapter outcome for an executor that returns its literal Rust result with the poststate inside `RustM`, the shape `ProbComp (RustM (reply × state))` of the published record and finish executors. A successful result keeps its reply and complete poststate. Such an executor has no poststate on `fail` or `div`, so the adapter reports the entry state there; `outcome_normal` and `ofResult_normal` show that this placeholder is never a supported outcome of a normal-returning executor. -/
def outcome (entry : State) : RustM (X × State) → RustM X × State
  | .ok result => (.ok result.1, result.2)
  | .fail error => (.fail error, entry)
  | .div => (.div, entry)

/-- The step form of a family of result-returning executors, one per query. -/
def ofResult (executor : (query : spec.Domain) → State → ProbComp (RustM (spec.Range query × State))) :
    Step spec State :=
  fun query state => outcome state <$> executor query state

/-- For one normal-returning computation, the adapter is the lifted native result with its complete poststate. -/
theorem outcome_ok (entry : State) (native : ProbComp (X × State)) :
    outcome entry <$> ((fun result => RustM.ok result) <$> native) =
      (fun result => (.ok result.1, result.2)) <$> native := by
  rw [Functor.map_map]
  rfl

/-- Every supported adapted outcome of a normal-returning computation is `ok` with a supported native reply and poststate; the entry-state placeholder is never supported. -/
theorem outcome_normal (entry : State) (native : ProbComp (X × State)) (result : RustM X × State)
    (supported : result ∈ support (outcome entry <$> ((fun result => RustM.ok result) <$> native))) :
    ∃ reply ∈ support native, result = (.ok reply.1, reply.2) := by
  rw [outcome_ok, support_map] at supported
  obtain ⟨reply, mem, rfl⟩ := supported
  exact ⟨reply, mem, rfl⟩

/-- An executor family whose every command equals `(fun result => ok result) <$>` of a native command (the form of the published executor equalities) adapts to exactly the lifted native step, for every query and complete state. -/
theorem ofResult_ok (executor : (query : spec.Domain) → State → ProbComp (RustM (spec.Range query × State)))
    (implementation : QueryImpl spec (StateT State ProbComp))
    (normal : ∀ query state, executor query state =
      (fun result => RustM.ok result) <$> (implementation query).run state)
    (query : spec.Domain) (state : State) :
    ofResult executor query state = liftStep implementation query state := by
  simp only [ofResult, liftStep, normal]
  exact outcome_ok state ((implementation query).run state)

/-- Under the same normal-return equalities, every supported outcome of every adapted command is `ok` with a supported native reply and poststate, so the failure placeholder of `outcome` is never observed. -/
theorem ofResult_normal (executor : (query : spec.Domain) → State → ProbComp (RustM (spec.Range query × State)))
    (implementation : QueryImpl spec (StateT State ProbComp))
    (normal : ∀ query state, executor query state =
      (fun result => RustM.ok result) <$> (implementation query).run state)
    (query : spec.Domain) (state : State) (result : RustM (spec.Range query) × State)
    (supported : result ∈ support (ofResult executor query state)) :
    ∃ reply ∈ support ((implementation query).run state), result = (.ok reply.1, reply.2) := by
  simp only [ofResult, normal] at supported
  exact outcome_normal state ((implementation query).run state) result supported

end BeaconcryptCore.Computational.PqxdhBoundaryProgram

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_pure' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_query' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_query

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_fail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_fail

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_div' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_div

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_congr' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_lift' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.execute_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.source_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.source_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.source_continuation' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.source_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.outcome_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.outcome_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.outcome_normal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.outcome_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.ofResult_ok' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.ofResult_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryProgram.ofResult_normal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryProgram.ofResult_normal
