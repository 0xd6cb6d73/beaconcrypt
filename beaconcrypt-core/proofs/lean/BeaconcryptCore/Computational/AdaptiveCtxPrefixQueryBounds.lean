import BeaconcryptCore.Computational.AdaptiveCtxPrefix

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxPrefixIsolation
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxPrefix AdaptiveCtxQueryBounds

/-- Public routed hashing may hit the private dictionary but still samples at most one digest. -/
theorem splitRandom_uniform (key : CtxKey) (query : CtxRO.Domain) (cache : SplitCache) :
    ((ctxSplitRandomOracle key query).run cache).IsTotalQueryBound 64 := by
  unfold ctxSplitRandomOracle
  simp only [StateT.run]
  split
  · exact CtxUnclaimedAcceptance.suffixStep_uniform_query_bound _ _
  · split
    · trivial
    · simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
        CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64

/-- Repeated suffixes, including those first installed by failed raw verification, reuse their digest rather than resampling. -/
theorem keyFreeSeal_uniform (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState) :
    ((ctxKeyFreeSealOracle c key input).run state).IsTotalQueryBound 64 := by
  unfold ctxKeyFreeSealOracle
  simp only [StateT.run]
  split
  · trivial
  · simpa only [ctxKeyFreeSuffixOracle, StateT.run, bind_pure_comp, OracleComp.IsTotalQueryBound,
        OracleComp.isQueryBound_map_iff] using
      CtxUnclaimedAcceptance.suffixStep_uniform_query_bound
        (outerSuffix input.nonce input.context (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext).2)
        state.cache

/-- Seals and public queries in either world pay at most 64 byte-valued uniform requests. -/
theorem sourceCtx_uniform (routed : Bool) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : ReceiveState) :
    (if routed then splitCtx c key query state else independentCtx c key query state).IsTotalQueryBound 64 := by
  have baseBound (routed : Bool) :
      ((if routed then ctxSplitRoutedImpl c key query else ctxIndependentTagImpl c key query).run state.ctx).IsTotalQueryBound 64 := by
    cases routed with
    | false =>
      cases query with
      | inl input => exact CtxComputationalSecurity.ctxIndependentPublicOracle_total_query_bound input state.ctx
      | inr input => exact keyFreeSeal_uniform c key input state.ctx
    | true =>
      cases query with
      | inl input =>
        change (do
          let (digest, cache) ← (ctxSplitRandomOracle key input).run state.ctx.cache
          pure (digest, state.ctx.addPublic input.2 cache) : ProbComp _).IsTotalQueryBound 64
        simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
          splitRandom_uniform key input state.ctx.cache
      | inr input => exact keyFreeSeal_uniform c key input state.ctx
  cases routed with
  | false => simpa only [Bool.false_eq_true, if_false, independentCtx, bind_pure_comp,
      OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using baseBound false
  | true => simpa only [if_true, splitCtx, bind_pure_comp,
      OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using baseBound true

/-- Every well-formed raw attempt can incur one 64-byte cache miss, including commitment/opening rejection. -/
theorem splitRaw_uniform (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : ReceiveState) :
    (splitRaw decode c key raw state).IsTotalQueryBound 64 := by
  cases parsed : decode raw with
  | none =>
    simp only [splitRaw, parsed]
    trivial
  | some target =>
    simpa only [splitRaw, parsed, bind_pure_comp, OracleComp.IsTotalQueryBound,
        OracleComp.isQueryBound_map_iff] using
      CtxUnclaimedAcceptance.suffixStep_uniform_query_bound
        (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache

/-- The sticky analysis bit adds no randomness; both full kernels charge source coins and every digest miss. -/
theorem sourceImpl_uniform_step (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : ReceiveState) :
    ((sourceImpl routed decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64) := by
  apply (OracleComp.isQueryBoundP_true_iff _ _).mpr
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      cases routed <;>
        change ((fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _)).IsTotalQueryBound 1 <;>
        apply (OracleComp.isQueryBoundP_true_iff _ _).mp <;>
        simp only [OracleComp.isQueryBoundP_map_iff] <;>
        exact (OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by intro _; decide)
    | inr query =>
      cases query with
      | inl input =>
        cases routed with
        | false => exact sourceCtx_uniform false c key (.inl input) state
        | true => exact sourceCtx_uniform true c key (.inl input) state
      | inr input =>
        cases routed with
        | false => exact sourceCtx_uniform false c key (.inr input) state
        | true => exact sourceCtx_uniform true c key (.inr input) state
  | inr raw =>
    cases routed <;> exact splitRaw_uniform decode c key raw state

/-- Adding a terminal sticky bit is a deterministic map over the actual source query. -/
theorem flaggedImpl_uniform_step (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : ReceiveState × Bool) :
    ((flaggedImpl routed decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64) := by
  simpa only [flaggedImpl, withStickyBad, StateT.run, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    sourceImpl_uniform_step routed decode c key query state.1

/-- An arbitrary source interpreter with these checked costs preserves the separate uniform and hash/seal/raw budgets. -/
theorem run_uniform_pair_bound {State Result : Type}
    (impl : QueryImpl ReceiveSpec (StateT State ProbComp))
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64))
    (adversary : OracleComp ReceiveSpec Result) (qCoins qWork : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (workBound : adversary.IsQueryBoundP SourceWork qWork) (state : State) :
    ((simulateQ impl adversary).run state).IsTotalQueryBound (qCoins + 64 * qWork) := by
  apply (OracleComp.isQueryBoundP_true_iff _ _).mp
  have vector := coinBound.and_isQueryBound_pair workBound
  exact vector.simulateQ_run_of_step
    (mapBudget := fun budget : ℕ × ℕ => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if SourceUniform query then 1 else 64)
    (combine := Nat.add)
    (fun hstep hrest => OracleComp.isQueryBoundP_bind hstep (fun result _ => hrest result))
    (fun query _ state _ => step query state)
    (fun query budget allowed => by
      by_cases coins : SourceUniform query
      · simp only [SourceWork, coins, not_true_eq_false, false_or, not_false_eq_true,
          true_or, if_true, if_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        omega
      · simp only [SourceWork, coins, not_true_eq_false, false_or, not_false_eq_true,
          true_or, if_true, if_false] at allowed ⊢
        change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
        omega)
    state

/-- The complete fixed-key prefix experiment counts every raw attempt, including private cache work on rejected requests. -/
theorem flaggedGame_uniform_bound (routed : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (flaggedGame routed decode c key adversary).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  run_uniform_pair_bound (flaggedImpl routed decode c key) (flaggedImpl_uniform_step routed decode c key)
    adversary qCoins (qHash + qSeal + qRaw) coinBound
    (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound) (initialState, false)

/-- The routed retained-key challenger additionally pays its 32 uniform seed bytes; analysis output itself consumes no query. -/
theorem retainedRoutedGame_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (retainedRoutedGame decode c adversary).IsTotalQueryBound
      (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  unfold retainedRoutedGame
  apply OracleComp.isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro key
  simpa only [splitGame, sourceImpl, if_true, bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    run_uniform_pair_bound (sourceImpl true decode c key) (sourceImpl_uniform_step true decode c key)
      adversary qCoins (qHash + qSeal + qRaw) coinBound
      (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound) initialState

end BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.sourceImpl_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.sourceImpl_uniform_step

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.flaggedGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.flaggedGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.retainedRoutedGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds.retainedRoutedGame_uniform_bound
