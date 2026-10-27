import BeaconcryptCore.Computational.AdaptiveCtxHonestCache

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxReplayTable AdaptiveCtxHonestCache JointEagerTable
open AdaptiveCtxQueryBounds

/-- Every actual well-formed replay comparison request performs its private lookup before returning, including rejection and repeated attempts. At most one 64-byte digest is drawn. -/
theorem replayRaw_uniform_bound (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) : (replayRaw decode raw state).IsTotalQueryBound 64 := by
  cases parsed : decode raw with
  | none => simp only [replayRaw, parsed]; trivial
  | some target =>
    simpa only [replayRaw, parsed, bind_pure_comp, OracleComp.IsTotalQueryBound,
        OracleComp.isQueryBound_map_iff] using
      CtxUnclaimedAcceptance.suffixStep_uniform_query_bound
        (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache

/-- Complete source per-request randomness: one arbitrary finite uniform query, or at most 64 byte-valued queries for its actual hash/commitment dictionary lookup. -/
theorem replayImpl_uniform_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((replayImpl decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64) := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      have computation : (replayImpl decode c key (.inl (.inl coin))).run state =
          (AdaptiveCtxPrefix.sourceImpl false decode c key (.inl (.inl coin))).run state := by
        unfold replayImpl AdaptiveCtxPrefix.sourceImpl AdaptiveCtxIndependent.independentImpl
        rfl
      exact computation.symm ▸ AdaptiveCtxPrefixQueryBounds.sourceImpl_uniform_step
        false decode c key (.inl (.inl coin)) state
    | inr query =>
      exact AdaptiveCtxPrefixQueryBounds.sourceImpl_uniform_step false decode c key _ state
  | inr raw => exact (OracleComp.isQueryBoundP_true_iff _ _).mpr (replayRaw_uniform_bound decode raw state)

/-- The actual complete replay-only source retains every declared source uniform/hash/seal/raw budget. The analysis-only reserved total table is not part of this concrete runtime source. -/
theorem replayRun_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) (state : AdaptiveCtxReceive.ReceiveState) :
    ((simulateQ (replayImpl decode c key) adversary).run state).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  AdaptiveCtxPrefixQueryBounds.run_uniform_pair_bound (replayImpl decode c key)
    (replayImpl_uniform_step decode c key) adversary qCoins (qHash + qSeal + qRaw) coinBound
    (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound) state

/-- The factored private dictionary has a separate query class; its requests are not silently treated as source uniform calls. -/
def IsPrivate : DictionarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred IsPrivate := fun query => by cases query <;> simp [IsPrivate] <;> infer_instance

/-- Explicit source/public-hash randomness cannot issue a private dictionary request. -/
theorem liftProbability_no_private {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work DictionarySpec).IsQueryBoundP IsPrivate 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := DictionarySpec) (p := fun _ => False)
    (hpq := fun query => by simp [IsPrivate, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false work 0)

/-- Each actual typed suffix operation makes exactly the one factored private query, on hits as well as misses. -/
theorem abstractSuffix_private_bound (address : Suffix) (cache : SplitCache) :
    (abstractSuffix address cache).IsQueryBoundP IsPrivate 1 := by
  simp only [abstractSuffix, bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
    OracleComp.isQueryBoundP_query_iff, IsPrivate]
  decide

/-- A successful seal queries its exact private suffix once; a used nonce rejects without that query. -/
theorem abstractSeal_private_bound (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (abstractSeal c key input state).IsQueryBoundP IsPrivate 1 := by
  unfold abstractSeal
  split
  · trivial
  · simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
      abstractSuffix_private_bound _ state.ctx.cache

/-- Every source seal attempt contributes at most one private query; all raw requests contribute zero to the honest-only comparison dictionary. -/
theorem honestOnlyImpl_private_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((honestOnlyImpl decode c key query).run state).IsQueryBoundP IsPrivate
      (if SourceSeal query then 1 else 0) := by
  cases query with
  | inr raw =>
    simp only [honestOnlyImpl, StateT.run, honestOnlyRaw]
    split <;> trivial
  | inl request =>
    cases request with
    | inl coin =>
      change OracleComp.IsQueryBoundP ((fun answer => (answer, state)) <$>
        (DictionarySpec.query (.inl coin) : OracleComp DictionarySpec _)) IsPrivate 0
      rw [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_query_iff]
      simp [IsPrivate]
    | inr operation =>
      cases operation with
      | inl hash => exact liftProbability_no_private (independentCtx c key (.inl hash) state)
      | inr input => exact abstractSeal_private_bound c key input state

/-- The complete mixed comparison asks at most qSeal honest private cells, with no uncharged private query hidden inside a raw replay reply. -/
theorem honestClient_private_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qSeal : ℕ)
    (bounded : adversary.IsQueryBoundP SourceSeal qSeal) :
    (honestClient decode c key adversary).IsQueryBoundP IsPrivate qSeal :=
  bounded.simulateQ_run_StateT_of_step (honestOnlyImpl_private_step decode c key) AdaptiveCtxReceive.initialState

/-- A well-formed raw request makes one actual factored private lookup even when its reply is a replay rejection. A malformed request makes none and still retains its raw accounting slot. -/
theorem abstractRaw_private_bound (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (abstractRaw decode raw state).IsQueryBoundP IsPrivate 1 := by
  unfold abstractRaw
  split
  · trivial
  · simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
      abstractSuffix_private_bound _ state.ctx.cache

/-- Actual source classes that may perform a private lookup; all attempted seals and raw deliveries count. -/
def SourcePrivate (query : ReceiveSpec.Domain) : Prop := SourceSeal query ∨ IsRawQuery query
instance : DecidablePred SourcePrivate := fun _query => inferInstanceAs (Decidable (_ ∨ _))

/-- Every actual source request introduces at most one private lookup in exactly its permitted class. -/
theorem abstractImpl_private_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((abstractImpl decode c key query).run state).IsQueryBoundP IsPrivate
      (if SourcePrivate query then 1 else 0) := by
  cases query with
  | inr raw => exact abstractRaw_private_bound decode raw state
  | inl request =>
    cases request with
    | inl coin =>
      change OracleComp.IsQueryBoundP ((fun answer => (answer, state)) <$>
        (DictionarySpec.query (.inl coin) : OracleComp DictionarySpec _)) IsPrivate 0
      rw [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_query_iff]
      simp [IsPrivate]
    | inr operation =>
      cases operation with
      | inl hash => exact liftProbability_no_private (independentCtx c key (.inl hash) state)
      | inr input => exact abstractSeal_private_bound c key input state

/-- Full source factoring counts all permitted private queries, including every failed/repeated raw lookup, by qSeal + qRaw. -/
theorem abstractRun_private_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qSeal qRaw : ℕ)
    (seals : adversary.IsQueryBoundP SourceSeal qSeal) (raws : adversary.IsQueryBoundP IsRawQuery qRaw)
    (state : AdaptiveCtxReceive.ReceiveState) :
    ((simulateQ (abstractImpl decode c key) adversary).run state).IsQueryBoundP IsPrivate (qSeal + qRaw) :=
  (query_union_bound adversary SourceSeal IsRawQuery qSeal qRaw seals raws).simulateQ_run_StateT_of_step
    (abstractImpl_private_step decode c key) state

/-- Honest-only comparison steps include every explicit source coin and all actual dictionary draws; omitted raw private queries introduce no new randomness. -/
theorem honestNative_uniform_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((honestNativeImpl decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if SourceUniform query then 1 else 64) := by
  cases query with
  | inl request => exact loggedImpl_uniform_step decode c key (.inl request) state
  | inr raw =>
    simp only [honestNativeImpl, StateT.run]
    split <;> trivial

/-- A uniform upper bound for the full direct comparison keeps every source class explicit. It may overcount the now-zero private randomness of raw replay steps, but never removes their local work or attempt slots. -/
theorem honestNativeRun_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) (state : AdaptiveCtxReceive.ReceiveState) :
    ((simulateQ (honestNativeImpl decode c key) adversary).run state).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  AdaptiveCtxPrefixQueryBounds.run_uniform_pair_bound (honestNativeImpl decode c key)
    (honestNative_uniform_step decode c key) adversary qCoins (qHash + qSeal + qRaw) coinBound
    (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound) state

end BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.replayRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.replayRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.honestClient_private_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.honestClient_private_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.abstractRun_private_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.abstractRun_private_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.honestNativeRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.honestNativeRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.abstractRaw_private_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds.abstractRaw_private_bound
