-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeRandomBackend

/-! Project the actual forwarded random backend to its public hash dictionary without changing, resetting or reconstructing the backend execution. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection
open AdaptiveCtxSharedHash PqxdhFirstRecordConfidentiality CtxRomAuth
variable (decode : AdaptiveCtxReceive.RawDecoder) (crypto : Pqxdh.Crypto)

/-- The public dictionary already held by the complete ordinary random interpreter. -/
def cache (state : RandomState) : CtxRO.QueryCache := state.2.2.1.ctx.cache.publicCache

/-- A forwarded public hash has exactly the original public dictionary marginal; every remaining field stays in the actual backend computation. -/
theorem hash (query : CtxRO.Domain) (state : RandomState) :
    (fun result => (result.1, cache result.2)) <$>
      (PqxdhLaterChallengeRandomBackend.handler decode crypto (.inr query)).run state =
      (ctxRandomOracle query).run (cache state) := by
  simp only [PqxdhLaterChallengeRandomBackend.handler, RawCtxSourceSharedRom.forward,
    QueryImpl.compose, AdaptiveCtxSharedTarget.forward, RawCtxSelectedSealConsumer.liftSelected,
    simulateQ_spec_query]
  rcases state with ⟨reduction, publicHistory, receiver, history, primitive⟩
  rw [confRandomImpl_run, reduction_selected]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rw [lower2_run, guard_forward]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rw [lower3_run]
  have wrapped : (AdaptiveCtxReceive.reductionImpl decode (.inl (.inr (.inl query)))).run receiver =
      (fun result => (result.1, { receiver with ctx := result.2 })) <$>
        OracleComp.liftComp ((CtxIndependentTags.ctxIndependentPublicOracle query).run receiver.ctx)
          AdaptiveRawNonceAead.AdaptiveSpec := by
    simp [AdaptiveCtxReceive.reductionImpl, StateT.run, AdaptiveCtxReceive.publicStep, map_eq_bind_pure_comp]
  rw [wrapped, simulateQ_map, StateT.run_map, lower4_liftComp]
  simp only [CtxIndependentTags.ctxIndependentPublicOracle, StateT.run,
    cache, CtxIndependentTags.CtxIndependentTagState.addPublic, bind_pure_comp, Functor.map_map, Prod.mk.eta]
  exact congrFun Functor.map_id _

/-- Both explicit source query classes project to the same original hash interpreter. -/
theorem query (request : HashSpec.Domain) (state : RandomState) :
    Prod.map id cache <$> (PqxdhLaterChallengeRandomBackend.handler decode crypto request).run state =
      (hashImpl request).run (cache state) := by
  cases request with
  | inl n =>
    rw [PqxdhLaterChallengeRandomBackend.coin]
    simp only [Functor.map_map]
    rfl
  | inr q => exact hash decode crypto q state

/-- Every complete adaptive forwarded prefix projects to the exact source hash execution from its actual existing dictionary. -/
theorem program {Result : Type} (work : OracleComp HashSpec Result) (state : RandomState) :
    Prod.map id cache <$> (simulateQ (PqxdhLaterChallengeRandomBackend.handler decode crypto) work).run state =
      (simulateQ hashImpl work).run (cache state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ cache (query decode crypto) work state

/-- Every actual random-prefix outcome has the identical source result and its literal public dictionary in the source support. -/
theorem supported {Result : Type} (work : OracleComp HashSpec Result) (state after : RandomState)
    (result : Result) (actual : (result, after) ∈ support
      ((simulateQ (PqxdhLaterChallengeRandomBackend.handler decode crypto) work).run state)) :
    (result, cache after) ∈ support ((simulateQ hashImpl work).run (cache state)) := by
  rw [← program decode crypto work state, support_map]
  exact ⟨(result, after), actual, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.hash

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.query

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.program

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRandomProjection.supported
