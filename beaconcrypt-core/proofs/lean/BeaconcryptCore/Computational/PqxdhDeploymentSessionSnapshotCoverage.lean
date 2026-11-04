-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshots

/-! Coverage of simultaneous first-stop receipts. These are generic callback instrumentation facts. Concrete acceptance ordinals still require the deployment-specific journal/ledger invariant and query-budget coverage; native session agreement is a separate obligation. -/

open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage

variable {κ Index α σ : Type} {spec : OracleSpec κ}
open PqxdhDeploymentSessionSnapshots (Journal State advance handler run)

/-- The original implementation with only a chronological public-call journal. -/
def logged (implementation : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl spec (StateT (Journal spec × σ) ProbComp) := fun query state =>
  (fun result => (result.1, (state.1 ++ [⟨query, result.1⟩], result.2))) <$>
    (implementation query).run state.2

theorem logged_run (implementation : QueryImpl spec (StateT σ ProbComp))
    (query : spec.Domain) (state : Journal spec × σ) :
    (logged implementation query).run state =
      (fun result => (result.1, (state.1 ++ [⟨query, result.1⟩], result.2))) <$>
        (implementation query).run state.2 := rfl

/-- Erasing all saved receipts preserves the result, the entire actual public-call journal and the final native state jointly. -/
theorem journal_erase_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (state : State Index spec σ) :
    (fun result => (result.1, (result.2.journal, result.2.native))) <$>
      (simulateQ (handler implementation stop) program).run state =
      (simulateQ (logged implementation) program).run (state.journal, state.native) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, PqxdhDeploymentSessionSnapshots.handler_run, logged_run,
        map_bind, bind_map_left, ih, advance]

/-- The simultaneous observer has exactly the original complete chronological journal, including every later callback. -/
theorem journal_erase (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ) :
    (fun result => (result.1, (result.2.journal, result.2.native))) <$>
      run implementation stop program native =
      (simulateQ (logged implementation) program).run ([], native) :=
  journal_erase_from implementation stop program ⟨[], fun _ => none, native⟩

/-- Whenever the stopping predicate holds at the current completed journal, a receipt has been saved. -/
def Covered (stop : Index → Journal spec → Prop) (state : State Index spec σ) : Prop :=
  ∀ index, stop index state.journal → ∃ snapshot, state.captured index = some snapshot

theorem advance_covered (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (state : State Index spec σ) (query : spec.Domain) (reply : spec.Range query) (native : σ) :
    Covered stop (advance stop state query reply native) := by
  intro index stopped
  cases saved : state.captured index <;> simp_all [advance]

/-- Every supported continuation retains coverage, including rejected operations and callbacks after the first capture. -/
theorem covered_from (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (state : State Index spec σ) (covered : Covered stop state)
    (outcome : α × State Index spec σ)
    (supported : outcome ∈ support ((simulateQ (handler implementation stop) program).run state)) :
    Covered stop outcome.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simpa only [supported] using covered
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind, PqxdhDeploymentSessionSnapshots.handler_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, _, continued⟩ := supported
      exact ih step.1 _ (advance_covered stop state query step.1 step.2) continued

/-- Every stopping predicate true on the final actual journal has a saved receipt in that same run. No callback or probabilistic outcome is discarded. -/
theorem run_covered (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ) (open_ : ∀ index, ¬stop index [])
    (outcome : α × State Index spec σ)
    (supported : outcome ∈ support (run implementation stop program native)) :
    Covered stop outcome.2 :=
  covered_from implementation stop program ⟨[], fun _ => none, native⟩
    (fun index stopped => (open_ index stopped).elim) outcome supported

/-- A stopping predicate true on the final journal cannot be absent from the receipt map. -/
theorem captured_of_stop (implementation : QueryImpl spec (StateT σ ProbComp))
    (stop : Index → Journal spec → Prop) [∀ index, DecidablePred (stop index)]
    (program : OracleComp spec α) (native : σ) (open_ : ∀ index, ¬stop index [])
    (outcome : α × State Index spec σ)
    (supported : outcome ∈ support (run implementation stop program native)) (index : Index)
    (stopped : stop index outcome.2.journal) :
    ∃ snapshot, outcome.2.captured index = some snapshot :=
  run_covered implementation stop program native open_ outcome supported index stopped

end BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.logged_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.logged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.journal_erase_from' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.journal_erase_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.journal_erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.journal_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.advance_covered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.advance_covered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.covered_from' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.covered_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.run_covered' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.run_covered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.captured_of_stop' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage.captured_of_stop
