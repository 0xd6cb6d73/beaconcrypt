import BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling

/-! Preserve an arbitrary existing candidate list in the complete alias-coupling experiment. The analysis flag starts at actual prior target membership; no prior occurrence is discarded or assumed absent. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAliasInitial
open PqxdhSecretInputKdf RawCtxSelectedAliasCoupling

private theorem marked_bad {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : (State × List RootOutput) × Bool)
    (bad : state.2 = true) (result : Result × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ (marked handler record target) client).run state)) :
    result.2.2 = true := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact bad
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, step, continued⟩ := supported
      exact ih reply.1 reply.2 (marked_sticky handler record target query state bad reply step) result continued

/-- The exact analysis flag is initialized from, and remains equal to membership in, the original complete candidate list. -/
theorem bad_probability_initial {ι State Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    Pr{let result ← (simulateQ (marked handler record target) client).run (decorate target state)}[result.2.2 = true] =
    Pr{let result ← (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run state}[target ∈ result.2.2] := by
  rw [← complete_graph handler record target client state, prEvent_map]
  simp only [Prod.map_def, id_eq, decorate, decide_eq_true_eq]

/-- A prior hit starts bad immediately; otherwise the existing complete-state identical-until-bad theorem applies to the unchanged callbacks. -/
theorem marked_distance_initial {ι State Result : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    tvDist ((simulateQ (marked handler record target) client).run (decorate target state))
      ((simulateQ (marked (routed handler alternate record target) record target) client).run (decorate target state)) ≤
      Pr{let result ← (simulateQ (marked handler record target) client).run (decorate target state)}[result.2.2 = true].toReal := by
  classical
  by_cases prior : target ∈ state.2
  · have one : Pr{let result ← (simulateQ (marked handler record target) client).run (decorate target state)}[result.2.2 = true] = 1 := by
      exact OracleComp.prEvent_eq_one_of_forall_mem_support _ _
        (marked_bad handler record target client (decorate target state) (by simp [decorate, prior]))
    rw [one, ENNReal.toReal_one]
    exact tvDist_le_one _ _
  · simpa only [decorate, decide_eq_false prior] using
      marked_distance handler alternate record target client state

/-- Full result and primitive-state distance is charged to membership in the same original final list, including all prior candidates. -/
theorem recorded_distance_initial {ι State Result : Type} {spec : OracleSpec ι}
    (handler alternate : QueryImpl spec (StateT State ProbComp))
    (record : spec.Domain → List RootOutput) (target : RootOutput)
    (client : OracleComp spec Result) (state : State × List RootOutput) :
    tvDist ((simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run state)
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (routed handler alternate record target) record) client).run state) ≤
    Pr{let result ← (simulateQ (RawCtxSelectedQueryTrace.recorded handler record) client).run state}[target ∈ result.2.2].toReal := by
  have projected := (tvDist_map_le (Prod.map id Prod.fst)
    ((simulateQ (marked handler record target) client).run (decorate target state))
    ((simulateQ (marked (routed handler alternate record target) record target) client).run (decorate target state))).trans
      (marked_distance_initial handler alternate record target client state)
  rw [bad_probability_initial] at projected
  simpa only [complete_erase, decorate] using projected

end BeaconcryptCore.Computational.RawCtxSelectedAliasInitial

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.bad_probability_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.bad_probability_initial

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.marked_distance_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.marked_distance_initial

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.recorded_distance_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAliasInitial.recorded_distance_initial
