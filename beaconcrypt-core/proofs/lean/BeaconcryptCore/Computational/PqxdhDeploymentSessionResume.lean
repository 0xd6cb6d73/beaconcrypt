-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling

/-! A stopped source prefix retains its actual residual program as private proof data. Resuming that exact continuation executes every later real source callback, rather than reconstructing a root or callback history from an erased final state. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionResume
variable {κ : Type} {spec : OracleSpec κ} {α : Type}
abbrev Journal (spec : OracleSpec κ) := List ((query : spec.Domain) × spec.Range query)

/-- Execute the actual query prefix and return the untouched residual program at the first stop. The residual is private analysis data and is never a network reply. -/
def cut (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) : OracleComp spec (OracleComp spec α × Journal spec) :=
  OracleComp.construct
    (fun value journal => pure (pure value, journal))
    (fun query next rest journal =>
      if stop journal then pure ((spec.query query : OracleComp spec _) >>= next, journal)
      else (spec.query query : OracleComp spec _) >>= fun reply => rest reply (journal ++ [⟨query, reply⟩]))
    program start

/-- A completed source computation has no remaining effects. -/
theorem cut_pure (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec) (value : α) :
    cut stop start (pure value : OracleComp spec α) = pure (pure value, start) := by
  simp only [cut, OracleComp.construct_pure]

/-- Exactly one original source query is performed while the stop has not been reached. -/
theorem cut_query_bind (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec α) :
    cut stop start (((spec.query query : OracleComp spec _) >>= next)) =
      if stop start then pure (((spec.query query : OracleComp spec _) >>= next), start)
      else (spec.query query : OracleComp spec _) >>= fun reply =>
        cut stop (start ++ [⟨query, reply⟩]) (next reply) := by
  simp only [cut, OracleComp.construct_query_bind]

/-- Once the stop holds, no callback is performed before returning the real untouched suffix. -/
theorem cut_stopped (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) (stopped : stop start) :
    cut stop start program = pure (program, start) := by
  induction program using OracleComp.inductionOn <;> simp only [cut_pure, cut_query_bind, stopped, ite_true]

/-- Resuming the retained residual is exactly the original source program, including every post-stop effect. -/
theorem resume_cut (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) :
    cut stop start program >>= Prod.fst = program := by
  induction program using OracleComp.inductionOn generalizing start
  all_goals simp_all only [cut_pure, cut_query_bind, ite_bind, pure_bind, bind_assoc, ite_self]

/-- Freezing a cut prefix performs exactly that prefix and records its own complete journal. -/
theorem frozen_cut_from (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) :
    (simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt stop) (cut stop start program)).run start =
      (fun result => (result, result.2)) <$> cut stop start program := by
  induction program using OracleComp.inductionOn generalizing start with
  | pure value => simp only [cut_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      by_cases stopped : stop start
      · simp only [cut_query_bind, ite_eq_left stopped, simulateQ_pure, StateT.run_pure, map_pure]
      · simp only [cut_query_bind, ite_eq_right stopped, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, bind_map_left, map_bind]
        exact bind_congr fun reply => ih reply _

/-- Discarding a cut's private residual returns exactly the original frozen query program. -/
theorem cut_unit_from (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) :
    (fun _ => ()) <$> cut stop start program =
      (fun _ => ()) <$> (simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt stop) program).run start := by
  induction program using OracleComp.inductionOn generalizing start with
  | pure value => simp only [cut_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      by_cases stopped : stop start
      · obtain ⟨value, frozen⟩ := PqxdhDeploymentServerAuthFreeze.frozen_pure dflt stop
          ((spec.query query : OracleComp spec _) >>= next) start stopped
        simp only [cut_stopped stop start _ stopped, frozen, map_pure]
      · simp only [cut_query_bind, ite_eq_right stopped, simulateQ_bind, simulateQ_spec_query,
          StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, bind_map_left, map_bind, ih]

/-- Returning the private real continuation changes no query of the original stopped adversary. -/
theorem frozen_cut_unit (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α) :
    (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.freeze dflt stop (cut stop [] program) =
      (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.freeze dflt stop program := by
  simpa only [PqxdhDeploymentServerAuthEmbed.freeze, frozen_cut_from, Functor.map_map] using
    cut_unit_from dflt stop [] program

/-- The private continuation value does not spend any oracle queries; cutting preserves every existing query cap. -/
theorem cut_query_bound (stop : Journal spec → Prop) [DecidablePred stop] (start : Journal spec)
    (program : OracleComp spec α) (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (n : Nat) (bounded : program.IsQueryBoundP predicate n) :
    (cut stop start program).IsQueryBoundP predicate n := by
  induction program using OracleComp.inductionOn generalizing start n with
  | pure value =>
      simpa only [cut_pure] using isQueryBoundP_pure predicate ((pure value : OracleComp spec α), start) n
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [cut_query_bind]
      split_ifs with stopped
      · exact isQueryBoundP_pure _ _ _
      · rw [isQueryBoundP_query_bind_iff]
        exact ⟨bounded.1, fun reply => ih reply _ _ (bounded.2 reply)⟩

variable {σ : Type}

/-- Execute the retained real suffix after the frozen cut; all original source effects and the final state are recovered exactly. -/
theorem resume_frozen (implementation : QueryImpl spec (StateT σ ProbComp))
    (dflt : (query : spec.Domain) → spec.Range query)
    (stop : Journal spec → Prop) [DecidablePred stop] (program : OracleComp spec α) (state : σ) :
    ((simulateQ implementation
      (PqxdhDeploymentServerAuthEmbed.freeze dflt stop (cut stop [] program))).run state >>=
        fun result => (simulateQ implementation result.1.1.1).run result.2) =
      (simulateQ implementation program).run state := by
  have same := congrArg (fun work => (simulateQ implementation work).run state) (resume_cut stop [] program)
  rw [PqxdhDeploymentServerAuthEmbed.freeze, frozen_cut_from, simulateQ_map, StateT.run_map, bind_map_left]
  simpa only [simulateQ_bind, StateT.run_bind] using same

end BeaconcryptCore.Computational.PqxdhDeploymentSessionResume

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.resume_frozen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.resume_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_query_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_stopped' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_stopped

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.resume_cut' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.resume_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.frozen_cut_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.frozen_cut_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_unit_from' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_unit_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.frozen_cut_unit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.frozen_cut_unit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_query_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionResume.cut_query_bound
