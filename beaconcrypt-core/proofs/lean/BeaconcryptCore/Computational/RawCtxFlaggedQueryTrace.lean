import BeaconcryptCore.Computational.RawCtxSelectedAliasInitial

/-!
Candidate logging and a query-derived sticky disclosure flag retain their original complete state. Reassociation exposes the existing checked alias coupling without resetting either history. The flag is private analysis state and does not alter the primitive reply. This module supplies operational coupling, not a source reachability or guessing bound.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace
open PqxdhSecretInputKdf

def mark {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (direct : spec.Domain → Bool) :
    QueryImpl spec (StateT (State × Bool) ProbComp) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, state.2 || direct query))

def trace {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) : QueryImpl spec (StateT ((State × List RootOutput) × Bool) ProbComp) :=
  fun query state => do
    let result ← (handler query).run state.1.1
    pure (result.1, ((result.2, state.1.2 ++ record query), state.2 || direct query))

def regroup {State : Type} : ((State × Bool) × List RootOutput) → ((State × List RootOutput) × Bool) :=
  fun state => ((state.1.1, state.2), state.1.2)

def split {State : Type} : ((State × List RootOutput) × Bool) → ((State × Bool) × List RootOutput) :=
  fun state => ((state.1.1, state.2), state.1.2)

/-- Reassociation preserves the primitive reply, complete state, prior candidate prefix and sticky flag on each query. -/
theorem step {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) (query : spec.Domain) (state : (State × Bool) × List RootOutput) :
    Prod.map id regroup <$>
      (RawCtxSelectedQueryTrace.recorded (mark handler direct) record query).run state =
      (trace handler record direct query).run (regroup state) := by
  simp [RawCtxSelectedQueryTrace.recorded, mark, trace, regroup, StateT.run]

/-- The full adaptive computation retains both histories; only tuple association changes. -/
theorem complete {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp)) (record : spec.Domain → List RootOutput)
    (direct : spec.Domain → Bool) (client : OracleComp spec Result)
    (state : (State × Bool) × List RootOutput) :
    Prod.map id regroup <$>
      (simulateQ (RawCtxSelectedQueryTrace.recorded (mark handler direct) record) client).run state =
      (simulateQ (trace handler record direct) client).run (regroup state) := by
  exact map_run_simulateQ_eq_of_query_map_eq _ _ regroup (step handler record direct) client state

/-- Exact-byte routing changes only the primitive callback; it retains the same query-derived disclosure flag. -/
theorem mark_routed {ι State : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (direct : spec.Domain → Bool) (target : RootOutput) :
    mark (RawCtxSelectedAliasCoupling.routed handler alternate record target) direct =
      RawCtxSelectedAliasCoupling.routed (mark handler direct) (mark alternate direct) record target := by
  funext query state
  by_cases hit : target ∈ record query <;> simp [mark, RawCtxSelectedAliasCoupling.routed, hit]

/-- Exact-byte routing is charged to the same complete candidate list while preserving the separate original disclosure flag. -/
theorem distance {ι State Result : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (direct : spec.Domain → Bool) (target : RootOutput)
    (client : OracleComp spec Result) (state : (State × List RootOutput) × Bool) :
    tvDist ((simulateQ (trace handler record direct) client).run state)
      ((simulateQ (trace (RawCtxSelectedAliasCoupling.routed handler alternate record target) record direct) client).run state) ≤
      Pr[fun result => target ∈ result.2.1.2 | (simulateQ (trace handler record direct) client).run state].toReal := by
  have original := complete handler record direct client (split state)
  have alternateRun := complete (RawCtxSelectedAliasCoupling.routed handler alternate record target)
    record direct client (split state)
  simp only [regroup, split, Prod.mk.eta] at original alternateRun
  rw [← original, ← alternateRun, mark_routed]
  simp only [probEvent_map, Function.comp_def, Prod.map_def, regroup, id_eq]
  exact (tvDist_map_le _ _ _).trans
    (RawCtxSelectedAliasInitial.recorded_distance_initial (mark handler direct) (mark alternate direct)
      record target client (split state))

end BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace

/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.step
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.complete
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.mark_routed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.mark_routed
/-- info: 'BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFlaggedQueryTrace.distance
