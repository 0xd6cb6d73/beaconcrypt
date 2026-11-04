-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshot

/-! Simultaneous private first-callback receipts. Every index observes one shared execution and one shared native state. Projection recovers the existing single-index instrument, while erasure retains the complete original execution, including all callbacks after every captured acceptance. The index may be a finite owner type. The adversary receives only the original callback replies; the causal-publication instantiation selects stops by public accept-attempt ordinal. -/

open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots

variable {κ Index α σ : Type} {spec : OracleSpec κ}
abbrev Journal (spec : OracleSpec κ) := PqxdhDeploymentSessionSnapshot.Journal spec

/-- One family of write-once receipts beside the single live execution. Finite `Index` gives a finite receipt map. -/
structure State (Index : Type) (spec : OracleSpec κ) (σ : Type) where
  journal : Journal spec
  captured : Index → Option (Journal spec × σ)
  native : σ

/-- Project a receipt without reconstructing any secret from a later native state. -/
def project (index : Index) (state : State Index spec σ) : PqxdhDeploymentSessionSnapshot.State spec σ :=
  ⟨state.journal, state.captured index, state.native⟩

theorem project_native (index : Index) (state : State Index spec σ) :
    (project index state).native = state.native := rfl

/-- Observe the same completed callback at every index, saving the actual state at its first stop. -/
def advance (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (state : State Index spec σ) (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    State Index spec σ :=
  let journal := state.journal ++ [⟨query, reply⟩]
  ⟨journal, fun index => (state.captured index).orElse
    (fun _ => if stop index journal then some (journal, native) else none), native⟩

/-- Execute each original callback exactly once, sharing all primitive effects and optional failures. -/
def handler (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)] :
    QueryImpl spec (StateT (State Index spec σ) ProbComp) := fun query state =>
  (fun result => (result.1, advance stop state query result.1 result.2)) <$>
    (implementation query).run state.native

def run (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ) : ProbComp (α × State Index spec σ) :=
  (simulateQ (handler implementation stop) program).run ⟨[], fun _ => none, native⟩

theorem handler_run (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (query : spec.Domain) (state : State Index spec σ) :
    (handler implementation stop query).run state =
      (fun result => (result.1, advance stop state query result.1 result.2)) <$>
        (implementation query).run state.native := rfl

theorem project_advance (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (state : State Index spec σ) (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    project index (advance stop state query reply native) =
      PqxdhDeploymentSessionSnapshot.advance (stop index) (project index state) query reply native := rfl

/-- A subsequent callback cannot replace any previously saved receipt. -/
theorem advance_saved (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (state : State Index spec σ) (snapshot : Journal spec × σ)
    (saved : state.captured index = some snapshot) (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    (advance stop state query reply native).captured index = some snapshot := by
  simp [advance, saved]

/-- The result and the complete final native state have exactly their original joint distribution. -/
theorem erase_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (state : State Index spec σ) :
    (fun result => (result.1, result.2.native)) <$>
      (simulateQ (handler implementation stop) program).run state =
      (simulateQ implementation program).run state.native := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, handler_run, map_bind, bind_map_left, ih, advance]

/-- Erasing all receipts retains one original run, rather than a product of separately sampled runs. -/
theorem erase (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ) :
    (fun result => (result.1, result.2.native)) <$> run implementation stop program native =
      (simulateQ implementation program).run native :=
  erase_from implementation stop program ⟨[], fun _ => none, native⟩

/-- Each owner's marginal, jointly with the returned value and live state, is exactly its original one-owner instrument. -/
theorem project_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (program : OracleComp spec α) (state : State Index spec σ) :
    (fun result => (result.1, project index result.2)) <$>
      (simulateQ (handler implementation stop) program).run state =
      (simulateQ (PqxdhDeploymentSessionSnapshot.handler implementation (stop index)) program).run
        (project index state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, handler_run, PqxdhDeploymentSessionSnapshot.handler_run,
        map_bind, bind_map_left, ih, project_advance, project_native]

/-- Projection from the simultaneous execution has exactly the one-owner distribution. -/
theorem project_run (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (program : OracleComp spec α) (native : σ) :
    (fun result => (result.1, project index result.2)) <$> run implementation stop program native =
      PqxdhDeploymentSessionSnapshot.run implementation (stop index) program native :=
  project_from implementation stop index program ⟨[], fun _ => none, native⟩

/-- A simultaneous receipt has the same complete frozen-prefix view as the existing per-owner construction. -/
theorem view_frozen (implementation : QueryImpl spec (StateT σ ProbComp))
    (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (program : OracleComp spec α) (native : σ) (open_ : ¬ stop index []) :
    EvalDistEq ((fun result => PqxdhDeploymentSessionSnapshot.view (project index result.2)) <$>
      run implementation stop program native)
      ((fun result : (α × Journal spec) × σ => (result.1.2, result.2)) <$>
        (simulateQ implementation (PqxdhDeploymentServerAuthEmbed.freeze dflt (stop index) program)).run native) := by
  have same := congrArg (fun work => (fun result => PqxdhDeploymentSessionSnapshot.view result.2) <$> work)
    (project_run implementation stop index program native)
  simp only [Functor.map_map] at same
  exact same ▸ PqxdhDeploymentSessionSnapshot.view_frozen implementation dflt (stop index) program native open_

/-- The all-owner union concerns receipts from this single run. Each summand is the unchanged one-owner experiment; this argument requires no independence. -/
theorem all_owner_bound [Fintype Index]
    (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ)
    (failure : Index → α × PqxdhDeploymentSessionSnapshot.State spec σ → Prop) :
    Pr{let result ← run implementation stop program native}[
      ∃ index, failure index (result.1, project index result.2)] ≤
      ∑ index, Pr{let result ← PqxdhDeploymentSessionSnapshot.run implementation (stop index) program native}[
        failure index result] := by
  classical
  have union := prEvent_exists_le (run implementation stop program native)
    (fun index result => failure index (result.1, project index result.2))
  simpa only [← project_run implementation stop, prEvent_map, tsum_fintype] using union

/-- A private property of an actually captured state is bounded by the same property in the publicly stopped execution. Only `stop` chooses the stopping point; the private property is never used by the reduction. -/
theorem captured_le_frozen (implementation : QueryImpl spec (StateT σ ProbComp))
    (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (index : Index) (program : OracleComp spec α) (native : σ) (open_ : ¬ stop index [])
    (event : σ → Prop) :
    Pr{let result ← run implementation stop program native}[
      ∃ snapshot, result.2.captured index = some snapshot ∧ event snapshot.2] ≤
      Pr{let result ← (simulateQ implementation
        (PqxdhDeploymentServerAuthEmbed.freeze dflt (stop index) program)).run native}[event result.2] := by
  calc
    _ ≤ Pr{let result ← run implementation stop program native}[
        event (PqxdhDeploymentSessionSnapshot.view (project index result.2)).2] := by
      apply prEvent_mono
      rintro result ⟨snapshot, saved, held⟩
      simpa only [PqxdhDeploymentSessionSnapshot.view, project, saved, Option.getD_some] using held
    _ = _ := by
      simpa only [prEvent_map] using
        (view_frozen implementation dflt stop index program native open_).prEvent_eq
          (fun snapshot => event snapshot.2)

end BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_native' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_native

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.handler_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.handler_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_advance' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_advance

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.advance_saved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.advance_saved

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.erase_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.erase_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.project_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.view_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.view_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.all_owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.all_owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.captured_le_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots.captured_le_frozen
