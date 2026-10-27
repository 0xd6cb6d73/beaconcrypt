-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEager

/-! Freezing a program at a stop of its journal (CE-8). `journal` runs a program unchanged and returns the journal of all its queries with their replies (`journal_erase`: forgetting the journal gives back the program). `freeze` journals the same queries until a stop predicate holds on the journal and then answers every later query with a fixed default, issuing nothing. Under every stateful handler, for every program, and for every stop predicate that does not hold on the empty journal, the frozen journal has the distribution of the full journal cut at its first prefix that stops (`frozen_journal`): the two runs agree query by query until the stop, and afterwards the cut of the full journal no longer changes. `unmatched_frozen` gives the consequence for the A1 failure: it holds on the registration view of a source14 journal exactly when it holds on that view of the journal cut at the stop of the creation index. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze
open PqxdhServerAuthExperiment
open PqxdhDeploymentServerAuthEvent (SourceEntry regsOfSource Stop Unmatched untilFrom untilStop)
open PqxdhDeploymentServerAuthEmbed (freezeImpl freeze stopAt)
open PqxdhBeaconPhase2Preparation (Word32)
variable {κ : Type} {spec : OracleSpec κ} {α σ : Type}

/-- The full journal: the program with every query and reply journaled, never frozen. -/
def journal (dfl : (query : spec.Domain) → spec.Range query) (program : OracleComp spec α) :
    OracleComp spec (α × List ((query : spec.Domain) × spec.Range query)) :=
  freeze dfl (fun _ => False) program

/-- Journaling without a stop changes nothing but the returned journal. -/
theorem journal_erase_from (dfl : (query : spec.Domain) → spec.Range query) (program : OracleComp spec α)
    (start : List ((query : spec.Domain) × spec.Range query)) :
    Prod.fst <$> (simulateQ (freezeImpl dfl (fun _ => False)) program).run start = program := by
  induction program using OracleComp.inductionOn generalizing start with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_false, bind_map_left, map_bind, ih]

/-- Forgetting the full journal gives back the program. -/
theorem journal_erase (dfl : (query : spec.Domain) → spec.Range query) (program : OracleComp spec α) :
    Prod.fst <$> journal dfl program = program :=
  journal_erase_from dfl program []

/-- A frozen program issues nothing and keeps its journal. -/
theorem frozen_pure (dfl : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop] (program : OracleComp spec α)
    (start : List ((query : spec.Domain) × spec.Range query)) (stopped : stop start) :
    ∃ value, (simulateQ (freezeImpl dfl stop) program).run start = pure (value, start) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp⟩
  | query_bind query next ih =>
      obtain ⟨value, same⟩ := ih (dfl query)
      refine ⟨value, ?_⟩
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_eq_left stopped, pure_bind, same]

/-- Under every handler, the full journal from a start extends the start. -/
theorem journal_extends (dfl : (query : spec.Domain) → spec.Range query) (handler : QueryImpl spec (StateT σ ProbComp))
    (program : OracleComp spec α) (start : List ((query : spec.Domain) × spec.Range query)) (state : σ)
    (outcome : (α × List ((query : spec.Domain) × spec.Range query)) × σ)
    (member : outcome ∈ support ((simulateQ handler ((simulateQ (freezeImpl dfl (fun _ => False)) program).run start)).run
      state)) : ∃ rest, outcome.1.2 = start ++ rest := by
  induction program using OracleComp.inductionOn generalizing start state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨[], by simp⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_false, bind_map_left, simulateQ_bind,
        simulateQ_query, mem_support_bind_iff] at member
      obtain ⟨step, _, continued⟩ := member
      obtain ⟨rest, same⟩ := ih step.1 _ step.2 continued
      exact ⟨⟨query, step.1⟩ :: rest, by simp [same]⟩

/-- A map that is constant on the support of a computation that never fails has the distribution of that constant. -/
theorem map_const_support {β γ : Type} (computation : ProbComp β) (f : β → γ) (value : γ)
    (constant : ∀ outcome ∈ support computation, f outcome = value) :
    EvalDistEq (f <$> computation) (pure value : ProbComp γ) := by
  rw [map_eq_bind_pure_comp]
  refine EvalDistEq.trans (OracleComp.EvalDistEq.bind_congr_of_support (g := fun _ => (pure value : ProbComp γ)) _
    fun outcome member => ?_) (OracleComp.EvalDistEq.bind_const _ _)
  simp [constant outcome member]

/-- From a journal that has not stopped, the frozen journal has the distribution of the full journal's continuation cut at its first stopping prefix. -/
theorem frozen_from (dfl : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop]
    (handler : QueryImpl spec (StateT σ ProbComp)) (program : OracleComp spec α)
    (start : List ((query : spec.Domain) × spec.Range query)) (open_ : ¬ stop start) (state : σ) :
    EvalDistEq ((fun outcome : (α × List ((query : spec.Domain) × spec.Range query)) × σ =>
        untilFrom stop start (outcome.1.2.drop start.length)) <$>
      (simulateQ handler ((simulateQ (freezeImpl dfl (fun _ => False)) program).run start)).run state)
      ((fun outcome : (α × List ((query : spec.Domain) × spec.Range query)) × σ => outcome.1.2) <$>
      (simulateQ handler ((simulateQ (freezeImpl dfl stop) program).run start)).run state) := by
  induction program using OracleComp.inductionOn generalizing start state with
  | pure value => simp [untilFrom]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, PqxdhDeploymentServerAuthLocalize.freezeImpl_run, ite_false, ite_eq_right open_, bind_map_left,
        simulateQ_bind, simulateQ_query, map_bind]
      refine EvalDistEq.bind_right _ fun step => ?_
      by_cases stopped : stop (start ++ [⟨query, step.1⟩])
      · obtain ⟨value, frozen⟩ := frozen_pure dfl stop (next step.1) _ stopped
        rw [frozen, simulateQ_pure, StateT.run_pure, map_pure]
        refine map_const_support _ _ _ fun outcome member => ?_
        obtain ⟨rest, same⟩ := journal_extends dfl handler (next step.1) _ step.2 outcome member
        simp only [same, List.append_assoc, List.singleton_append, List.drop_left, untilFrom, stopped, ite_true]
      · refine EvalDistEq.trans ?_ (ih step.1 _ stopped step.2)
        rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
        refine OracleComp.EvalDistEq.bind_congr_of_support _ fun outcome member => ?_
        obtain ⟨rest, same⟩ := journal_extends dfl handler (next step.1) _ step.2 outcome member
        simp only [Function.comp_apply, same, List.append_assoc, List.singleton_append, List.drop_left, untilFrom,
          stopped, ite_false, List.length_append, List.length_singleton]
        simp

/-- Under every handler, the frozen journal has the distribution of the full journal cut at its first stopping prefix, for every stop predicate that does not hold on the empty journal. -/
theorem frozen_journal (dfl : (query : spec.Domain) → spec.Range query)
    (stop : List ((query : spec.Domain) × spec.Range query) → Prop) [DecidablePred stop]
    (handler : QueryImpl spec (StateT σ ProbComp)) (program : OracleComp spec α) (open_ : ¬ stop []) (state : σ) :
    EvalDistEq ((fun outcome : (α × List ((query : spec.Domain) × spec.Range query)) × σ => untilStop stop outcome.1.2) <$>
      (simulateQ handler (journal dfl program)).run state)
      ((fun outcome : (α × List ((query : spec.Domain) × spec.Range query)) × σ => outcome.1.2) <$>
      (simulateQ handler (freeze dfl stop program)).run state) := by
  simpa only [untilStop, journal, freeze, List.length_nil, List.drop_zero] using
    frozen_from dfl stop handler program [] open_ state

/-- The A1 failure holds on the registration view of a source14 journal exactly when it holds on the view of the journal cut at the stop of the creation index. -/
theorem unmatched_frozen {Reader Response KemSK : Type} (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (binding : Word32 × Std.U64) (c : Nat) (entries : List (SourceEntry KemSK)) :
    Unmatched crypto codec binding c (regsOfSource (untilStop (stopAt c) entries)) ↔
      Unmatched crypto codec binding c (regsOfSource entries) := by
  rcases PqxdhDeploymentServerAuthEvent.untilStop_spec (stopAt c) entries with ⟨stopped, rest, same⟩ | same
  · conv_rhs => rw [same]
    rw [show regsOfSource (untilStop (stopAt c) entries ++ rest) =
      regsOfSource (untilStop (stopAt c) entries) ++ regsOfSource rest from List.filterMap_append]
    exact (PqxdhDeploymentServerAuthEvent.unmatched_stop crypto codec binding c _ _ stopped).symm
  · rw [same]

/-- No creation index has stopped on the empty journal. -/
theorem stopAt_nil {KemSK : Type} (c : Nat) : ¬ stopAt (KemSK := KemSK) c [] := by
  simp [stopAt, Stop, regsOfSource, PqxdhDeploymentServerAuthEvent.accepted, PqxdhDeploymentServerAuthEvent.acceptedFrom,
    PqxdhDeploymentServerAuthEvent.summarizeReg, PqxdhDeploymentTranscript.Summary.empty]

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_erase_from' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_erase_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.journal_extends

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.map_const_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.map_const_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_from

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.frozen_journal

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.unmatched_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.unmatched_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.stopAt_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthFreeze.stopAt_nil
