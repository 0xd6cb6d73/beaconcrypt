import BeaconcryptCore.Computational.AdaptiveCtxLoggedSource

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open CtxHonestTagSampling CtxComputationalSecurity

/-- A replay-only reply uses the exact previously issued full CTX tuple and supplied plaintext. -/
def replayPlaintext (state : CtxIndependentTagState) (target : CtxUnclaimedAcceptance.Target) : Option Pqxdh.Bytes :=
  (state.successfulSeals.find? (fun entry => decide (target.nonce = entry.input.nonce ∧ target.context.ad = entry.input.context.ad ∧ target.record.encode = entry.record.encode))).map
    (fun entry => entry.input.plaintext)

/-- No replay log match is exactly full CTX freshness. -/
theorem replayPlaintext_none_iff (state : CtxIndependentTagState) (target : CtxUnclaimedAcceptance.Target) :
    replayPlaintext state target = none ↔
      ∀ entry ∈ state.successfulSeals, ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  simp [replayPlaintext, CtxAliasTarget.sameFullTupleAsSuccessfulSeal, CtxUnclaimedAcceptance.Target.toLegacy]

/-- Equality of complete encoded records recovers only their typed fields by actual decoding. -/
theorem fullTuple_fields (target : CtxUnclaimedAcceptance.Target) (entry : CtxSuccessfulSeal)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    target.nonce = entry.input.nonce ∧ target.context.ad = entry.input.context.ad ∧
      target.record.toRecordCipher = entry.record.toRecordCipher := by
  refine ⟨same.1, same.2.1, ?_⟩
  have decoded := congrArg Pqxdh.decodeRecord same.2.2
  simpa only [decodeRecord_romRecord, Option.some.injEq, CtxUnclaimedAcceptance.Target.toLegacy] using decoded

/-- A full CTX replay is the same ordinary nonce/AD/ciphertext tuple. -/
theorem fullTuple_base (target : CtxUnclaimedAcceptance.Target) (entry : CtxSuccessfulSeal)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    (baseTarget target).nonce = (CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal entry).input.nonce ∧
    (baseTarget target).ad = (CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal entry).input.ad ∧
    (baseTarget target).ciphertext = (CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal entry).ciphertext := by
  obtain ⟨nonce, context, record⟩ := fullTuple_fields target entry same
  refine ⟨nonce, congrArg Pqxdh.RecordAD.bytes context, ?_⟩
  have body := congrArg Pqxdh.RecordCipher.body record
  have tag := congrArg Pqxdh.RecordCipher.tag record
  change target.record.body = entry.record.body at body
  change target.record.tag = entry.record.tag at tag
  simp only [baseTarget, CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal,
    CtxRomRecord.toModifiedNonceAeadCiphertext, body, tag]

/-- A full replay's plaintext is exactly the ordinary log's returned plaintext by functional opening correctness. -/
theorem fullTuple_loggedPlaintext (c : Pqxdh.Crypto) (key : CtxKey)
    (state : CtxIndependentTagState) (target : CtxUnclaimedAcceptance.Target)
    (correct : AdaptiveRawNonceAead.HistoryCorrect c key
      (state.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal))
    (entry : CtxSuccessfulSeal) (member : entry ∈ state.successfulSeals)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state).successfulSeals (baseTarget target) =
        some entry.input.plaintext := by
  have tuple := fullTuple_base target entry same
  have issued : (CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal entry) ∈
      state.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal := List.mem_map_of_mem member
  have notFresh : ¬ModifiedNonceAeadFresh
      (state.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal) (baseTarget target) := by
    intro h
    exact h _ issued tuple
  have found : AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state).successfulSeals (baseTarget target) ≠ none := by
    intro absent
    exact notFresh ((AdaptiveRawNonceAead.loggedPlaintext_none_iff_fresh _ _).mp absent)
  obtain ⟨plaintext, found⟩ := Option.ne_none_iff_exists'.mp found
  have opened := AdaptiveRawNonceAead.loggedPlaintext_correct c key _ correct _ plaintext found
  have known := correct _ issued
  have equal : plaintext = entry.input.plaintext := by
    rw [tuple.1, tuple.2.1, tuple.2.2, known] at opened
    exact (Option.some.inj opened).symm
  simpa only [equal] using found

/-- Every replay-only reply is exactly the ordinary log reply and has its issued commitment in the actual private dictionary. -/
theorem replayPlaintext_exact (c : Pqxdh.Crypto) (key : CtxKey)
    (state : AdaptiveCtxReceive.ReceiveState) (invariant : LoggedInvariant c key state)
    (target : CtxUnclaimedAcceptance.Target) (plaintext : Pqxdh.Bytes)
    (found : replayPlaintext state.ctx target = some plaintext)
    (lookup : CtxDigest × SplitCache)
    (supported : lookup ∈ support
      (ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache)) :
    AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target) = some plaintext ∧
    target.record.commit = lookup.1 := by
  obtain ⟨entry, located, value⟩ := Option.map_eq_some_iff.mp found
  have member := List.mem_of_find?_eq_some located
  have same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
    simpa only [decide_eq_true_eq, CtxAliasTarget.sameFullTupleAsSuccessfulSeal,
      CtxUnclaimedAcceptance.Target.toLegacy] using List.find?_some located
  have logged := fullTuple_loggedPlaintext c key state.ctx target invariant.2.2.2 entry member same
  refine ⟨by simpa only [value] using logged, ?_⟩
  obtain ⟨nonce, context, record⟩ := fullTuple_fields target entry same
  have tag := congrArg Pqxdh.RecordCipher.tag record
  change target.record.tag = entry.record.tag at tag
  have commit : target.record.commit = entry.record.commit :=
    List.Vector.toList_injective (congrArg Pqxdh.RecordCipher.commit record)
  have suffix : outerSuffix target.nonce target.context target.record.tag =
      outerSuffix entry.input.nonce entry.input.context entry.record.tag := by
    simp [outerSuffix, nonce, context, tag]
  have cached := invariant.1 entry member
  rw [← suffix] at cached
  unfold ctxKeyFreeSuffixStep at supported
  rw [cached, support_pure, Set.mem_singleton_iff] at supported
  exact commit.trans (congrArg Prod.fst supported).symm

/-- The replay-only comparison game still performs every actual private lookup and retains the complete cache; only fresh full tuples are forced to reject. -/
noncomputable def replayRaw (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) : ProbComp (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) := do
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let (_, cache) ← ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache
    pure (replayPlaintext state.ctx target, ⟨{ state.ctx with cache }, state.rawAttempts + 1,
      outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩)

/-- At each particular actual private lookup, replay-only and logged replies differ exactly when the logged reply accepts a fresh full tuple. -/
theorem replay_discrepancy_iff (c : Pqxdh.Crypto) (key : CtxKey)
    (state : AdaptiveCtxReceive.ReceiveState) (invariant : LoggedInvariant c key state)
    (target : CtxUnclaimedAcceptance.Target) (lookup : CtxDigest × SplitCache)
    (supported : lookup ∈ support
      (ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache)) :
    (if target.record.commit = lookup.1 then AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target) else none) ≠
      replayPlaintext state.ctx target ↔
    (∀ entry ∈ state.ctx.successfulSeals, ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry) ∧
      target.record.commit = lookup.1 ∧
      AdaptiveRawNonceAead.loggedPlaintext
        (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target) ≠ none := by
  cases replay : replayPlaintext state.ctx target with
  | none =>
    have fresh := (replayPlaintext_none_iff state.ctx target).mp replay
    split <;> simp_all
  | some plaintext =>
    obtain ⟨logged, commit⟩ := replayPlaintext_exact c key state invariant target plaintext replay lookup supported
    have notFresh : ¬∀ entry ∈ state.ctx.successfulSeals, ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
      rw [← replayPlaintext_none_iff, replay]
      simp
    simp [logged, commit, notFresh]

/-- Only the exact 197-byte production suffix is queried in the private dictionary. -/
abbrev Suffix := FixedBytes 197
abbrev PrivateSpec := Suffix →ₒ CtxDigest
abbrev DictionarySpec := unifSpec + PrivateSpec

@[inline, reducible] def privateRandom : QueryImpl PrivateSpec (StateT PrivateSpec.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

def typedSuffix (nonce : CtxNonce) (context : CtxRecordContext) (tag : Pqxdh.Bytes)
    (tagLength : tag.length = 16) : Suffix :=
  ⟨outerSuffix nonce context tag, outerSuffix_length nonce context tag tagLength⟩

/-- The full source private cache agrees with the external finite dictionary at every possible source address. Existing entries outside this width remain untouched. -/
def DictionaryAligned (cache : SplitCache) (dictionary : PrivateSpec.QueryCache) : Prop :=
  ∀ address : Suffix, cache.suffixCache address.toList = dictionary address

/-- Private queries mirror their exact returned value in the complete source cache, including repeated or rejected raw lookups. -/
def abstractSuffix (address : Suffix) (cache : SplitCache) :
    OracleComp DictionarySpec (CtxDigest × SplitCache) := do
  let digest ← DictionarySpec.query (.inr address)
  pure (digest, cacheSuffix cache address.toList digest)

/-- The left interface consists only of explicit uniform requests; the right interface is the actual lazy finite private dictionary. -/
noncomputable def lazyDictionary : QueryImpl DictionarySpec (StateT PrivateSpec.QueryCache ProbComp) :=
  fun query dictionary => match query with
  | .inl coin => do
    let answer ← unifSpec.query coin
    pure (answer, dictionary)
  | .inr address => (privateRandom address).run dictionary

/-- Reinstalling a known value leaves the entire split cache exactly unchanged. -/
theorem cacheSuffix_of_some (cache : SplitCache) (address : Pqxdh.Bytes) (digest : CtxDigest)
    (cached : cache.suffixCache address = some digest) : cacheSuffix cache address digest = cache := by
  apply SplitCache.ext
  · rfl
  · funext other
    by_cases same : other = address
    · subst other
      simpa only [cacheSuffix, QueryCache.cacheQuery_self] using cached.symm
    · exact QueryCache.cacheQuery_of_ne cache.suffixCache digest same

/-- The finite private dictionary projects exactly to the actual persistent source lookup, retaining every source cache value. -/
theorem abstractSuffix_projection (address : Suffix) (cache : SplitCache)
    (dictionary : PrivateSpec.QueryCache) (aligned : DictionaryAligned cache dictionary) :
    Prod.fst <$> (simulateQ lazyDictionary (abstractSuffix address cache)).run dictionary =
      ctxKeyFreeSuffixStep address.toList cache := by
  simp only [abstractSuffix, bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map, Functor.map_map]
  change ((fun reply : CtxDigest × PrivateSpec.QueryCache =>
    (reply.1, cacheSuffix cache address.toList reply.1)) <$>
      (privateRandom address).run dictionary) = _
  cases cached : dictionary address with
  | none =>
    rw [QueryImpl.withCaching_run_none _ cached]
    simp [ctxKeyFreeSuffixStep, aligned address, cached, Functor.map_map]
    rfl
  | some digest =>
    rw [QueryImpl.withCaching_run_some _ cached]
    have present : cache.suffixCache address.toList = some digest := (aligned address).trans cached
    simp [ctxKeyFreeSuffixStep, present, cacheSuffix_of_some cache address.toList digest present]

/-- Mirroring the same fixed-width address and digest preserves complete finite/source dictionary agreement. -/
theorem dictionaryAligned_cache (address : Suffix) (digest : CtxDigest) (cache : SplitCache)
    (dictionary : PrivateSpec.QueryCache) (aligned : DictionaryAligned cache dictionary) :
    DictionaryAligned (cacheSuffix cache address.toList digest) (dictionary.cacheQuery address digest) := by
  intro other
  by_cases same : other = address
  · subst other
    simp only [cacheSuffix, QueryCache.cacheQuery_self]
  · have different : other.toList ≠ address.toList := fun equal => same (List.Vector.toList_injective equal)
    simpa only [cacheSuffix, QueryCache.cacheQuery_of_ne cache.suffixCache digest different,
      QueryCache.cacheQuery_of_ne dictionary digest same] using aligned other

/-- Every abstract private query preserves source/external agreement, on hits and on misses. -/
theorem abstractSuffix_preserves (address : Suffix) (cache : SplitCache)
    (dictionary : PrivateSpec.QueryCache) (aligned : DictionaryAligned cache dictionary)
    (result : (CtxDigest × SplitCache) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ lazyDictionary (abstractSuffix address cache)).run dictionary)) :
    DictionaryAligned result.1.2 result.2 := by
  simp only [abstractSuffix, bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map] at supported
  change result ∈ support ((fun reply : CtxDigest × PrivateSpec.QueryCache =>
    ((reply.1, cacheSuffix cache address.toList reply.1), reply.2)) <$>
      (privateRandom address).run dictionary) at supported
  obtain ⟨reply, step, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases cached : dictionary address with
  | none =>
    rw [QueryImpl.withCaching_run_none _ cached] at step
    obtain ⟨digest, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ step
    exact dictionaryAligned_cache address digest cache dictionary aligned
  | some digest =>
    rw [QueryImpl.withCaching_run_some _ cached] at step
    obtain rfl := eq_of_mem_support_pure step
    have present : cache.suffixCache address.toList = some digest := (aligned address).trans cached
    simpa only [cacheSuffix_of_some cache address.toList digest present] using aligned

/-- Explicit source/public-cache randomness keeps the complete finite private dictionary untouched. -/
theorem simulate_coins {Result : Type} (work : ProbComp Result) (dictionary : PrivateSpec.QueryCache) :
    (simulateQ lazyDictionary (OracleComp.liftComp work DictionarySpec)).run dictionary =
      (fun answer => (answer, dictionary)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (simulateQ lazyDictionary (DictionarySpec.query (.inl coin))).run before = _
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- Honest sealing uses the same primitive result and complete public context, then queries the finite private dictionary at the exact typed suffix. -/
def abstractSeal (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : AdaptiveCtxReceive.ReceiveState) : OracleComp DictionarySpec (Option CtxRomRecord × AdaptiveCtxReceive.ReceiveState) := do
  if input.nonce ∈ state.ctx.usedNonces then pure (none, state)
  else
    let base := c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let address := typedSuffix input.nonce input.context base.2 (c.aeadSeal_tag_length _ _ _ _)
    let (commit, cache) ← abstractSuffix address state.ctx.cache
    let record : CtxRomRecord := ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
    pure (some record, ⟨state.ctx.addSeal ⟨input, record⟩ cache, state.rawAttempts,
      address.toList :: state.privateInputs⟩)

/-- Rejected fresh raw requests still query and mirror the actual private dictionary; their replies use only public successful replay history. -/
def abstractRaw (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    OracleComp DictionarySpec (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) := do
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let address := typedSuffix target.nonce target.context target.record.tag target.record.tagLength
    let (_, cache) ← abstractSuffix address state.ctx.cache
    pure (replayPlaintext state.ctx target, ⟨{ state.ctx with cache }, state.rawAttempts + 1,
      address.toList :: state.privateInputs⟩)

/-- The source exposes the same query interface while its private dictionary is factored into an ordinary finite lazy oracle. -/
noncomputable def abstractImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState (OracleComp DictionarySpec)) :=
  fun query state => match query with
  | .inl (.inl coin) => do
    let answer ← DictionarySpec.query (.inl coin)
    pure (answer, state)
  | .inl (.inr (.inl hash)) => OracleComp.liftComp (independentCtx c key (.inl hash) state) DictionarySpec
  | .inl (.inr (.inr input)) => abstractSeal c key input state
  | .inr raw => abstractRaw decode raw state

/-- Direct comparison source: only full fresh raw tuples are forced to reject; all cache operations and non-raw replies remain actual. -/
noncomputable def replayImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => match query with
  | .inl (.inl coin) => do
    let answer ← unifSpec.query coin
    pure (answer, state)
  | .inl (.inr query) => independentCtx c key query state
  | .inr raw => replayRaw decode raw state

/-- Factoring the private dictionary preserves the actual complete replay-only raw response and source poststate. -/
theorem abstractRaw_projection (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary) :
    Prod.fst <$> (simulateQ lazyDictionary (abstractRaw decode raw state)).run dictionary =
      replayRaw decode raw state := by
  cases parsed : decode raw with
  | none => simp [abstractRaw, replayRaw, parsed]
  | some target =>
    let address := typedSuffix target.nonce target.context target.record.tag target.record.tagLength
    let finish : CtxDigest × SplitCache → Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState :=
      fun lookup => (replayPlaintext state.ctx target,
        ⟨{ state.ctx with cache := lookup.2 }, state.rawAttempts + 1, address.toList :: state.privateInputs⟩)
    simpa only [abstractRaw, replayRaw, parsed, bind_pure_comp, simulateQ_map, StateT.run_map,
      Functor.map_map, Function.comp_def, finish, address, typedSuffix, List.Vector.toList] using
      congrArg (fun game => finish <$> game) (abstractSuffix_projection address state.ctx.cache dictionary aligned)

/-- Honest sealing retains exactly its source primitive arguments, optional nonce rejection, full cache and state after finite dictionary factoring. -/
theorem abstractSeal_projection (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary) :
    Prod.fst <$> (simulateQ lazyDictionary (abstractSeal c key input state)).run dictionary =
      independentCtx c key (.inr input) state := by
  by_cases used : input.nonce ∈ state.ctx.usedNonces
  · simp only [abstractSeal, used, if_true, simulateQ_pure, StateT.run_pure, map_pure]
    simp [independentCtx, ctxIndependentTagImpl, ctxKeyFreeSealOracle, used, sealPrivateInputs, StateT.run]
  · simp only [abstractSeal, used, if_false, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    let base := c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let address := typedSuffix input.nonce input.context base.2 (c.aeadSeal_tag_length _ _ _ _)
    let finish : CtxDigest × SplitCache → Option CtxRomRecord × AdaptiveCtxReceive.ReceiveState := fun lookup =>
      let record : CtxRomRecord := ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, lookup.1⟩
      (some record, ⟨state.ctx.addSeal ⟨input, record⟩ lookup.2, state.rawAttempts,
        address.toList :: state.privateInputs⟩)
    simpa [used, independentCtx, ctxIndependentTagImpl, ctxKeyFreeSealOracle,
      ctxKeyFreeSuffixOracle, StateT.run, bind_pure_comp, simulateQ_map, StateT.run_map,
      Functor.map_map, sealPrivateInputs, address, base, finish, typedSuffix] using
      congrArg (fun game => finish <$> game) (abstractSuffix_projection address state.ctx.cache dictionary aligned)

/-- Raw dictionary factoring retains full source/external agreement even when the reply rejects. -/
theorem abstractRaw_preserves (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary)
    (result : (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ lazyDictionary (abstractRaw decode raw state)).run dictionary)) :
    DictionaryAligned result.1.2.ctx.cache result.2 := by
  cases parsed : decode raw with
  | none =>
    simp only [abstractRaw, parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact aligned
  | some target =>
    simp only [abstractRaw, parsed, bind_pure_comp, simulateQ_map, StateT.run_map] at supported
    obtain ⟨lookup, step, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
    exact abstractSuffix_preserves _ state.ctx.cache dictionary aligned lookup step

/-- Honest sealing preserves the same full dictionary relation, including nonce rejection and prior failed-raw cache entries. -/
theorem abstractSeal_preserves (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary)
    (result : (Option CtxRomRecord × AdaptiveCtxReceive.ReceiveState) × PrivateSpec.QueryCache)
    (supported : result ∈ support ((simulateQ lazyDictionary (abstractSeal c key input state)).run dictionary)) :
    DictionaryAligned result.1.2.ctx.cache result.2 := by
  by_cases used : input.nonce ∈ state.ctx.usedNonces
  · simp only [abstractSeal, used, if_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact aligned
  · simp only [abstractSeal, used, if_false, bind_pure_comp, simulateQ_map, StateT.run_map] at supported
    obtain ⟨lookup, step, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
    exact abstractSuffix_preserves _ state.ctx.cache dictionary aligned lookup step

abbrev DictionaryState := AdaptiveCtxReceive.ReceiveState × PrivateSpec.QueryCache

def SourceDictionaryAligned (state : DictionaryState) : Prop :=
  DictionaryAligned state.1.ctx.cache state.2

noncomputable def dictionaryLinked (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT DictionaryState ProbComp) :=
  QueryImpl.Stateful.link (abstractImpl decode c key) lazyDictionary

theorem dictionaryLinked_run (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache) :
    (dictionaryLinked decode c key query).run (state, dictionary) =
      (fun result => (result.1.1, result.1.2, result.2)) <$>
        (simulateQ lazyDictionary ((abstractImpl decode c key query).run state)).run dictionary := rfl

/-- Full per-query factoring changes only the duplicate private-dictionary representation, preserving actual source replies and every source-state field. -/
theorem dictionaryLinked_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : DictionaryState) (aligned : SourceDictionaryAligned state) :
    Prod.map id Prod.fst <$> (dictionaryLinked decode c key query).run state =
      (replayImpl decode c key query).run state.1 := by
  rcases state with ⟨state, dictionary⟩
  rw [dictionaryLinked_run]
  simp only [Functor.map_map]
  cases query with
  | inr raw => exact abstractRaw_projection decode raw state dictionary aligned
  | inl request =>
    cases request with
    | inr operation =>
      cases operation with
      | inr input => exact abstractSeal_projection c key input state dictionary aligned
      | inl hash =>
        change Prod.fst <$> (simulateQ lazyDictionary
          (OracleComp.liftComp (independentCtx c key (.inl hash) state) DictionarySpec)).run dictionary = _
        rw [simulate_coins]
        simp only [Functor.map_map]
        exact id_map _
    | inl coin =>
      change Prod.fst <$> (simulateQ lazyDictionary (do
        let answer ← DictionarySpec.query (.inl coin)
        pure (answer, state))).run dictionary = _
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map, Functor.map_map]
      change ((fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _)) = _
      simp only [replayImpl, StateT.run, bind_pure_comp]
      rfl

/-- Independent public hashing changes only the public cache and public observation log. -/
theorem independentHash_preserves_suffix (c : Pqxdh.Crypto) (key : CtxKey)
    (hash : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (result : CtxDigest × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (independentCtx c key (.inl hash) state)) :
    result.2.ctx.cache.suffixCache = state.ctx.cache.suffixCache := by
  unfold independentCtx at supported
  obtain ⟨ctxResult, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain rfl := eq_of_mem_support_pure supported
  change ctxResult ∈ support ((ctxIndependentPublicOracle hash).run state.ctx) at step
  unfold ctxIndependentPublicOracle at step
  obtain ⟨oracleResult, _, step⟩ := (mem_support_bind_iff _ _ _).mp step
  obtain rfl := eq_of_mem_support_pure step
  rfl

/-- Complete source/external dictionary agreement is preserved through all adaptive query classes. -/
theorem dictionaryLinked_preserves (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (dictionaryLinked decode c key) SourceDictionaryAligned := by
  rintro query ⟨state, dictionary⟩ aligned result supported
  rw [dictionaryLinked_run] at supported
  obtain ⟨value, step, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  cases query with
  | inr raw => exact abstractRaw_preserves decode raw state dictionary aligned value step
  | inl request =>
    cases request with
    | inr operation =>
      cases operation with
      | inr input => exact abstractSeal_preserves c key input state dictionary aligned value step
      | inl hash =>
        change value ∈ support ((simulateQ lazyDictionary
          (OracleComp.liftComp (independentCtx c key (.inl hash) state) DictionarySpec)).run dictionary) at step
        rw [simulate_coins] at step
        obtain ⟨reply, actual, rfl⟩ := OracleComp.mem_support_map_peel _ _ step
        have unchanged := independentHash_preserves_suffix c key hash state reply actual
        intro address
        simpa only [unchanged] using aligned address
    | inl coin =>
      change value ∈ support ((simulateQ lazyDictionary (do
        let answer ← DictionarySpec.query (.inl coin)
        pure (answer, state))).run dictionary) at step
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_query,
        OracleQuery.input_query, OracleQuery.cont_query, id_map] at step
      change value ∈ support ((fun answer => ((answer, state), dictionary)) <$>
        (unifSpec.query coin : ProbComp _)) at step
      obtain ⟨answer, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ step
      exact aligned

/-- The entire adaptive replay-only source is exactly the finite dictionary client with its duplicate external cache projected away. No marginal distribution or ambient alignment premise replaces this complete continuation equality. -/
theorem abstractRun_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) (dictionary : PrivateSpec.QueryCache)
    (aligned : DictionaryAligned state.ctx.cache dictionary) :
    Prod.fst <$> (simulateQ lazyDictionary
      ((simulateQ (abstractImpl decode c key) adversary).run state)).run dictionary =
      (simulateQ (replayImpl decode c key) adversary).run state := by
  have related := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (dictionaryLinked decode c key) (replayImpl decode c key) SourceDictionaryAligned Prod.fst
    (dictionaryLinked_preserves decode c key) (dictionaryLinked_projection decode c key)
    adversary (state, dictionary) aligned
  unfold dictionaryLinked at related
  rw [QueryImpl.Stateful.simulateQ_link_run] at related
  simpa only [Functor.map_map, Function.comp_def, QueryImpl.Stateful.Frame.prod,
    QueryImpl.Stateful.Frame.linkReshape, PFunctor.Lens.State.fst, PFunctor.Lens.State.snd,
    PFunctor.Lens.State.mk_put, Prod.map, id_eq] using related

/-- Fresh source dictionaries satisfy the alignment relation by construction. -/
theorem initial_dictionary_aligned : DictionaryAligned AdaptiveCtxReceive.initialState.ctx.cache (∅ : PrivateSpec.QueryCache) := by
  intro address
  rfl

end BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.replayPlaintext_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.replayPlaintext_exact

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.replay_discrepancy_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.replay_discrepancy_iff

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractSuffix_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractSuffix_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractSuffix_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractSuffix_preserves

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.dictionaryLinked_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.dictionaryLinked_preserves

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractRun_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReplayDictionary.abstractRun_projection
