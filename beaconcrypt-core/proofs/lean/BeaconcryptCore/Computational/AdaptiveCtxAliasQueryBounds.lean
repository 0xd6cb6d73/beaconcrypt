import BeaconcryptCore.Computational.AdaptiveCtxAliasCoupling

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxReplayQueryBounds AdaptiveCtxStoppedRaw
open AdaptiveCtxAliasCoupling AdaptiveCtxQueryBounds

/-- Both sticky optional-reply kernels perform exactly the source coin or dictionary work. Computing the flag adds no uniform-oracle query. -/
theorem flaggedImpl_uniform_step (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState × Bool) :
    ((AdaptiveCtxAliasCoupling.flaggedImpl logged decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64) := by
  cases query with
  | inl request =>
    simpa only [AdaptiveCtxAliasCoupling.flaggedImpl, StateT.run, bind_pure_comp,
      OracleComp.isQueryBoundP_map_iff] using replayImpl_uniform_step decode c key (.inl request) state.1
  | inr raw =>
    simpa only [AdaptiveCtxAliasCoupling.flaggedImpl, StateT.run, bind_pure_comp,
      OracleComp.isQueryBoundP_map_iff,
      ite_eq_right (show ¬SourceUniform (.inr raw) from id)] using
      (OracleComp.isQueryBoundP_true_iff _ _).mpr (replayRaw_uniform_bound decode raw state.1)

/-- Full sticky runs include every source coin, hash, seal and raw slot, from any prior cache and counter. -/
theorem flaggedRun_uniform_bound (logged : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw)
    (state : AdaptiveCtxReceive.ReceiveState × Bool) :
    ((simulateQ (AdaptiveCtxAliasCoupling.flaggedImpl logged decode c key) adversary).run state).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  AdaptiveCtxPrefixQueryBounds.run_uniform_pair_bound (AdaptiveCtxAliasCoupling.flaggedImpl logged decode c key)
    (flaggedImpl_uniform_step logged decode c key) adversary qCoins (qHash + qSeal + qRaw) coinBound
    (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound) state

/-- Each selected raw comparison executes that request before stopping and inherits every full source budget. -/
theorem stoppedRun_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (index qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) (state : AdaptiveCtxReceive.ReceiveState) :
    (indexedGame decode c key adversary index state).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  replayRun_uniform_bound decode c key (stopAtRaw adversary index) qCoins qHash qSeal qRaw
    (stopAtRaw_query_bound SourceUniform adversary coinBound index)
    (stopAtRaw_query_bound SourceHash adversary hashBound index)
    (stopAtRaw_query_bound SourceSeal adversary sealBound index)
    (stopAtRaw_query_bound IsRawQuery adversary rawBound index) state

/-- The complete comparison challenger pays its sampled 32-byte key as well as all actual source randomness. Retaining the key only for analysis introduces no reveal. -/
theorem retainedReplayGame_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (retainedReplayGame decode c adversary).IsTotalQueryBound
      (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  unfold retainedReplayGame
  apply OracleComp.isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro key
  simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    replayRun_uniform_bound decode c key adversary qCoins qHash qSeal qRaw coinBound hashBound sealBound rawBound
      AdaptiveCtxReceive.initialState

/-- Every raw replay-comparison request increments one counter slot, including malformed input, rejection and repeat lookup. -/
theorem replayRaw_raw_count (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (replayRaw decode raw state)) :
    result.2.rawAttempts = state.rawAttempts + 1 := by
  cases parsed : decode raw with
  | none =>
    simp only [replayRaw, parsed, mem_support_pure_iff] at supported
    subst result
    rfl
  | some target =>
    simp only [replayRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    rfl

/-- Complete request accounting agrees with the actual raw class; primitive queries retain the prior counter. -/
theorem replayImpl_raw_count (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (result : ReceiveSpec.Range query × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support ((replayImpl decode c key query).run state)) :
    result.2.rawAttempts = state.rawAttempts + (if IsRawQuery query then 1 else 0) := by
  cases query with
  | inl request =>
    cases request <;> exact loggedImpl_raw_count decode c key _ state result supported
  | inr raw => exact replayRaw_raw_count decode raw state result supported

/-- Every finite adaptive run respects the exact source raw-attempt cap from any prior counter. -/
theorem replayRun_raw_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery qRaw) (state : AdaptiveCtxReceive.ReceiveState)
    (result : Result × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support ((simulateQ (replayImpl decode c key) adversary).run state)) :
    result.2.rawAttempts ≤ state.rawAttempts + qRaw := by
  induction adversary using OracleComp.inductionOn generalizing qRaw state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    change result ∈ support ((replayImpl decode c key query).run state >>= fun value =>
      (simulateQ (replayImpl decode c key) (next value.1)).run value.2) at supported
    obtain ⟨value, step, tail⟩ := (mem_support_bind_iff _ _ _).mp supported
    have rest := ih value.1 _ (bounded.2 value.1) value.2 tail
    have count := replayImpl_raw_count decode c key query state value step
    by_cases raw : IsRawQuery query
    · have positive : 0 < qRaw := bounded.1.resolve_left (not_not.mpr raw)
      simp only [raw, if_true] at rest count
      omega
    · simp only [raw, if_false] at rest count
      omega

end BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.flaggedImpl_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.flaggedImpl_uniform_step

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.flaggedRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.flaggedRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.stoppedRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.stoppedRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.retainedReplayGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.retainedReplayGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayRaw_raw_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayRaw_raw_count

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayImpl_raw_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayImpl_raw_count

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayRun_raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds.replayRun_raw_bound
