import BeaconcryptCore.Computational.RawCtxSelectedPublicTrace
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
An analysis-only sticky flag marks exact membership of a selected byte vector in the original callback's input list. At a marked query an arbitrary alternate callback may run; on every other query the callback stays unchanged. The existing full-state identical-until-bad theorem bounds the resulting distance by membership in the original execution's complete log, with no success conditioning and no protocol security premise.

This reusable coupling retains every reply, primitive poststate and input occurrence. It does not establish completeness of a particular source log, a native reached-cut distribution, or live-exposure freshness. Those source obligations must be discharged at its concrete instantiation. The alternate callback is an executable program, not an assumed security endpoint. Snapshot, persistence and restoration services are excluded.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling
open PqxdhSecretInputKdf

/-- The target is analysis state; removing the flag retains the original recorded callback. -/
noncomputable def marked {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput) :
    QueryImpl spec (StateT ((State × List RootOutput) × Bool) ProbComp) := fun query state => do
  let result ← (RawCtxSelectedQueryTrace.recorded handler record query).run state.1
  pure (result.1, (result.2, state.2 || decide (target ∈ record query)))

/-- Repeated equal inputs use the alternate selected response; all other calls retain the original handler. -/
noncomputable def routed {ι State : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput) :
    QueryImpl spec (StateT State ProbComp) := fun query =>
  if target ∈ record query then alternate query else handler query

/-- Marking changes no reply, log or original primitive state. -/
theorem marked_erase {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (query : spec.Domain) (state : (State × List RootOutput) × Bool) :
    Prod.map id Prod.fst <$> (marked handler record target query).run state =
      (RawCtxSelectedQueryTrace.recorded handler record query).run state.1 := by
  simp [marked, StateT.run]

/-- The analysis flag is sticky even when the first matching-input callback takes a different branch. -/
theorem marked_sticky {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (query : spec.Domain) (state : (State × List RootOutput) × Bool)
    (bad : state.2 = true) (result : spec.Range query × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((marked handler record target query).run state)) :
    result.2.2 = true := by
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, rfl⟩
  simp [bad]

/-- Every matching-input output is marked before any comparison of source and routed replies. -/
theorem hit_marked {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (query : spec.Domain) (state : (State × List RootOutput) × Bool)
    (hit : target ∈ record query) (result : spec.Range query × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((marked handler record target query).run state)) :
    result.2.2 = true := by
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, rfl⟩
  simp [hit]

/-- Good-output transitions are identical even though the first matching-input transition may differ. -/
theorem agree_good {ι State : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (query : spec.Domain) (state : State × List RootOutput)
    (reply : spec.Range query) (next : State × List RootOutput) :
    Pr{let x ← (marked handler record target query).run (state, false)}[x = (reply, (next, false))] =
      Pr{let x ← (marked (routed handler alternate record target) record target query).run (state, false)}[x = (reply, (next, false))] := by
  by_cases hit : target ∈ record query
  · have zero (implementation : QueryImpl spec (StateT State ProbComp)) :
        Pr{let x ← (marked implementation record target query).run (state, false)}[x = (reply, (next, false))] = 0 := by
      apply (prEvent_eq_zero_of_not_mem_support _)
      intro supported
      exact Bool.false_ne_true (hit_marked implementation record target query (state, false)
        hit (reply, (next, false)) supported)
    rw [zero, zero]
  · simp only [marked, StateT.run, RawCtxSelectedQueryTrace.recorded, routed, hit, ite_false]

/-- The full adaptive result, primitive state and input history differ by at most the first matching-input event in the original interpreter. -/
theorem marked_distance {ι State Result : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    tvDist ((simulateQ (marked handler record target) client).run (state, false))
      ((simulateQ (marked (routed handler alternate record target) record target) client).run (state, false)) ≤
      Pr{let result ← (simulateQ (marked handler record target) client).run (state, false)}[result.2.2 = true].toReal := by
  have bound := OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    _ _ client state (fun query before reply after => by
      simpa only [VCVioLegacy.probOutput_eq_prEvent] using
        agree_good handler alternate record target query before reply after)
    (marked_sticky handler record target)
    (marked_sticky (routed handler alternate record target) record target)
  rw [VCVioLegacy.probEvent_eq_prEvent] at bound
  exact bound

noncomputable def decorate {State : Type} (target : RootOutput)
    (state : State × List RootOutput) : (State × List RootOutput) × Bool :=
  (state, decide (target ∈ state.2))

/-- The flag is exactly the membership view of the retained full input history. -/
theorem marked_graph {ι State : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (query : spec.Domain) (state : State × List RootOutput) :
    Prod.map id (decorate target) <$> (RawCtxSelectedQueryTrace.recorded handler record query).run state =
      (marked handler record target query).run (decorate target state) := by
  simp [marked, RawCtxSelectedQueryTrace.recorded, decorate, StateT.run, List.mem_append]

/-- The same adaptive complete run reconstructs the flag from its actual log; no independent bad-event sampler is introduced. -/
theorem complete_graph {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    Prod.map id (decorate target) <$>
        (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run state =
      (simulateQ (marked handler record target) client).run (decorate target state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (decorate target)
    (marked_graph handler record target) client state

/-- Removing only the analysis flag retains every original callback, reply and logged byte. -/
theorem complete_erase {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : (State × List RootOutput) × Bool) :
    Prod.map id Prod.fst <$> (simulateQ (marked handler record target) client).run state =
      (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (marked_erase handler record target) client state

/-- Starting with an empty log, the bad probability is exactly membership in this run's complete candidate list. -/
theorem bad_probability {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State) :
    Pr{let result ← (simulateQ (marked handler record target) client).run ((state, []), false)}[result.2.2 = true] =
    Pr{let result ← (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run (state, [])}[target ∈ result.2.2] := by
  have graph := complete_graph handler record target client (state, [])
  simp only [decorate, List.not_mem_nil, decide_false] at graph
  rw [← graph, prEvent_map]
  simp only [Prod.map_def, id_eq, decorate, decide_eq_true_eq]

/-- Arbitrary adaptive alias routing costs only membership in the original actual candidate log, retaining its full result and primitive state. -/
theorem recorded_distance {ι State Result : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State) :
    tvDist ((simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run (state, []))
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (routed handler alternate record target) record) client).run (state, [])) ≤
    Pr{let result ← (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run (state, [])}[target ∈ result.2.2].toReal := by
  have projected := (tvDist_map_le (Prod.map id Prod.fst)
    ((simulateQ (marked handler record target) client).run ((state, []), false))
    ((simulateQ (marked (routed handler alternate record target) record target) client).run ((state, []), false))).trans
      (marked_distance handler alternate record target client (state, []))
  simpa only [complete_erase, bad_probability] using projected

end BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_sticky

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.hit_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.hit_marked

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.agree_good

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.marked_graph

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.complete_graph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.complete_graph

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.complete_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.complete_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.bad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.bad_probability

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.recorded_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling.recorded_distance
