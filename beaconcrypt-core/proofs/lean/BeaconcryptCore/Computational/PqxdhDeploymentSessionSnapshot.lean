-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze

/-!
Private snapshots retain the complete native state at the first stopping callback while every later callback still runs. Forgetting the bookkeeping recovers the original adaptive execution. The stopping view can therefore carry session secrets without retaining them in production or replacing the real suffix by default replies.
-/

open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot

variable {κ : Type} {spec : OracleSpec κ} {α σ : Type}

abbrev Journal (spec : OracleSpec κ) := List ((query : spec.Domain) × spec.Range query)

/-- Proof-only journal and first stopping state, beside the live native state. -/
structure State (spec : OracleSpec κ) (σ : Type) where
  journal : Journal spec
  captured : Option (Journal spec × σ)
  native : σ

/-- The saved stopping state, or the final state if no callback stopped. -/
def view (state : State spec σ) : Journal spec × σ :=
  state.captured.getD (state.journal, state.native)

/-- Observe a completed callback without changing its reply or native state. -/
def advance (stop : Journal spec → Prop) [DecidablePred stop]
    (state : State spec σ) (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    State spec σ :=
  let journal := state.journal ++ [⟨query, reply⟩]
  ⟨journal, state.captured.orElse (fun _ => if stop journal then some (journal, native) else none), native⟩

/-- Execute the real callback even after the private snapshot has been captured. -/
def handler (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] :
    QueryImpl spec (StateT (State spec σ) ProbComp) := fun query state =>
  (fun result => (result.1, advance stop state query result.1 result.2)) <$>
    (implementation query).run state.native

def run (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α) (native : σ) :
    ProbComp (α × State spec σ) :=
  (simulateQ (handler implementation stop) program).run ⟨[], none, native⟩

theorem handler_run (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (query : spec.Domain) (state : State spec σ) :
    (handler implementation stop query).run state =
      (fun result => (result.1, advance stop state query result.1 result.2)) <$>
        (implementation query).run state.native := rfl

/-- A later callback cannot overwrite the first private stopping state. -/
theorem advance_saved (stop : Journal spec → Prop) [DecidablePred stop]
    (state : State spec σ) (snapshot : Journal spec × σ) (saved : state.captured = some snapshot)
    (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    (advance stop state query reply native).captured = some snapshot := by
  simp [advance, saved]

/-- Instrumentation retains the exact result and complete final native state. -/
theorem erase_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α) (state : State spec σ) :
    (fun result => (result.1, result.2.native)) <$>
      (simulateQ (handler implementation stop) program).run state =
      (simulateQ implementation program).run state.native := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, handler_run, map_bind, bind_map_left, ih, advance]

/-- Erasing the proof-only state recovers the whole original adaptive run. -/
theorem erase (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α) (native : σ) :
    (fun result => (result.1, result.2.native)) <$> run implementation stop program native =
      (simulateQ implementation program).run native :=
  erase_from implementation stop program ⟨[], none, native⟩

/-- Every supported suffix retains the first captured state, including all failed protocol replies. -/
theorem saved_support (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α)
    (snapshot : Journal spec × σ) (state : State spec σ) (saved : state.captured = some snapshot)
    (outcome : α × State spec σ)
    (supported : outcome ∈ support ((simulateQ (handler implementation stop) program).run state)) :
    outcome.2.captured = some snapshot := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using saved
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, handler_run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, _, continued⟩ := supported
      exact ih step.1 _ (advance_saved stop state snapshot saved query step.1 step.2) continued

/-- Continuing after a stop leaves the saved-state observation constant with its full probability mass. -/
theorem saved_view (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α)
    (snapshot : Journal spec × σ) (state : State spec σ) (saved : state.captured = some snapshot) :
    EvalDistEq ((fun result => view result.2) <$>
      (simulateQ (handler implementation stop) program).run state) (pure snapshot : ProbComp _) := by
  apply PqxdhDeploymentServerAuthFreeze.map_const_support
  intro outcome supported
  simp [view, saved_support implementation stop program snapshot state saved outcome supported]

/-- The full private state at the first stop has exactly the frozen execution's distribution. -/
theorem view_frozen_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α)
    (start : Journal spec) (native : σ) (open_ : ¬ stop start) :
    EvalDistEq ((fun result => view result.2) <$>
      (simulateQ (handler implementation stop) program).run ⟨start, none, native⟩)
      ((fun result : (α × Journal spec) × σ => (result.1.2, result.2)) <$>
        (simulateQ implementation
          ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt stop) program).run start)).run native) := by
  induction program using OracleComp.inductionOn generalizing start native with
  | pure value => simp [view]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, handler_run, bind_map_left, map_bind,
        PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_eq_right open_, simulateQ_bind,
        simulateQ_query]
      refine EvalDistEq.bind_right _ fun step => ?_
      by_cases stopped : stop (start ++ [⟨query, step.1⟩])
      · obtain ⟨value, frozen⟩ := PqxdhDeploymentServerAuthFreeze.frozen_pure
          dflt stop (next step.1) _ stopped
        rw [frozen, simulateQ_pure, StateT.run_pure, map_pure]
        simpa [advance, stopped] using saved_view implementation stop (next step.1)
          (start ++ [⟨query, step.1⟩], step.2)
          ⟨start ++ [⟨query, step.1⟩], some (start ++ [⟨query, step.1⟩], step.2), step.2⟩ rfl
      · simpa [advance, stopped] using ih step.1 (start ++ [⟨query, step.1⟩]) step.2 stopped

/-- The write-once snapshot of a real complete run has the full frozen prefix state's distribution. -/
theorem view_frozen (implementation : QueryImpl spec (StateT σ ProbComp))
    (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α)
    (native : σ) (open_ : ¬ stop []) :
    EvalDistEq ((fun result => view result.2) <$> run implementation stop program native)
      ((fun result : (α × Journal spec) × σ => (result.1.2, result.2)) <$>
        (simulateQ implementation (PqxdhDeploymentServerAuthEmbed.freeze dflt stop program)).run native) := by
  simpa only [run, PqxdhDeploymentServerAuthEmbed.freeze] using
    view_frozen_from implementation dflt stop program [] native open_

end BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.handler_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.handler_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.advance_saved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.advance_saved

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.erase_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.erase_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.saved_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.saved_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.saved_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.saved_view

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.view_frozen_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.view_frozen_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.view_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot.view_frozen
