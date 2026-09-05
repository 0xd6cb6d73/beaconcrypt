import BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation
import BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds

/-!
# Complete persistent-cache logged CTX source

The logged ordinary opening experiment is identified with an exact direct source interpreter retaining both caches, every failed private lookup, successful seal/nonce histories and raw-attempt instrumentation. The actual seal handler preserves cached honest commitments without assuming that every private cache entry came from sealing. Every fresh accepted optional raw reply is classified as a context alias at an already-used nonce and an address distinct from every honestly exposed commitment. These are structural simulation and freshness results; the adaptive hidden-dictionary guessing probability is a separate remaining proof.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxLoggedSource
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent
open CtxHonestTagSampling CtxComputationalSecurity

/-- On computations with no raw opening request, changing opening mode preserves even the complete auxiliary challenger state. -/
theorem noRaw_mode_eq (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (work : OracleComp AdaptiveRawNonceAead.AdaptiveSpec Result)
    (noRaw : work.IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 0) (state : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key) work).run state =
      (simulateQ (AdaptiveRawNonceAead.adaptiveImpl true (baseDecoder decode) c key) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at noRaw
    cases query with
    | inr raw => exact False.elim (noRaw.1.elim (fun h => h trivial) (by omega))
    | inl primitive =>
      simp only [simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query]
      apply bind_congr
      intro result
      exact ih result.1 (by simpa [AdaptiveRawNonceAead.IsRawQuery] using noRaw.2 result.1) result.2

/-- Direct raw receive in the logged world preserves all failed private suffix operations and returns only plaintext already supplied to a successful base encryption. -/
noncomputable def loggedRaw (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) : ProbComp (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) := do
  match decode raw with
  | none => pure (none, { state with rawAttempts := state.rawAttempts + 1 })
  | some target =>
    let (digest, cache) ← ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache
    let answer := if target.record.commit = digest then
      AdaptiveRawNonceAead.loggedPlaintext
        (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals (baseTarget target)
      else none
    pure (answer, ⟨{ state.ctx with cache }, state.rawAttempts + 1,
      outerSuffix target.nonce target.context target.record.tag :: state.privateInputs⟩)

/-- A delegated raw opening in the logged game returns exactly its public encryption-log lookup. -/
theorem simulate_logged_raw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (base : BaseState) :
    (simulateQ (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key)
      (AdaptiveRawNonceAead.AdaptiveSpec.query (.inr raw))).run base =
        AdaptiveRawNonceAead.receiveStep false (baseDecoder decode) c key raw base := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

/-- The logged direct source has the exact full raw query result when the complete source/base histories agree. -/
theorem loggedRaw_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState)
    (aligned : Aligned (state, base)) :
    Prod.fst <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key)
      (rawStep decode raw state)).run base = loggedRaw decode raw state := by
  have history : base.1.seals = ctxIndependentTagStateToModifiedNonceAead state.ctx := aligned
  cases parsed : decode raw with
  | none => simp [rawStep, loggedRaw, parsed]
  | some target =>
    simp only [rawStep, parsed, simulateQ_bind, StateT.run_bind, simulate_private,
      bind_map_left, map_bind, loggedRaw]
    apply bind_congr
    rintro ⟨digest, cache⟩
    by_cases equal : target.record.commit = digest
    · simp only [equal, if_true, bind_pure_comp, simulateQ_map, StateT.run_map, simulate_logged_raw]
      simp [AdaptiveRawNonceAead.receiveStep, AdaptiveRawNonceAead.simulatedOpen,
        baseDecoder, parsed, history]
    · simp [equal]

/-- Logged raw verification keeps the entire nonce and successful-encryption histories aligned, including on every failed private lookup. -/
theorem loggedRaw_preserves_aligned (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (base : BaseState) (aligned : Aligned (state, base))
    (result : (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) × BaseState)
    (supported : result ∈ support ((simulateQ
      (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key)
        (rawStep decode raw state)).run base)) : Aligned (result.1.2, result.2) := by
  cases parsed : decode raw with
  | none =>
    simp only [rawStep, parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact aligned
  | some target =>
    simp only [rawStep, parsed, simulateQ_bind, StateT.run_bind, simulate_private,
      bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨⟨digest, cache⟩, _, supported⟩ := supported
    by_cases equal : target.record.commit = digest
    · simp only [equal, if_true, bind_pure_comp, simulateQ_map, StateT.run_map,
        simulate_logged_raw, AdaptiveRawNonceAead.receiveStep] at supported
      subst result
      exact aligned
    · simp only [equal, if_false, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact aligned

/-- Link the existing CTX wrapper to logged ordinary opening while retaining both complete private states. -/
noncomputable def loggedLinkedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT JointState ProbComp) :=
  QueryImpl.Stateful.link (reductionImpl decode)
    (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key)

theorem loggedLinkedImpl_run (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) (base : BaseState) :
    (loggedLinkedImpl decode c key query).run (state, base) =
      retainBoth <$> (simulateQ (AdaptiveRawNonceAead.adaptiveImpl false (baseDecoder decode) c key)
        ((reductionImpl decode query).run state)).run base := rfl

/-- All non-raw queries retain the exact earlier source and challenger behavior. -/
theorem loggedLinkedImpl_nonraw (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (notRaw : ¬AdaptiveCtxReceive.IsRawQuery query) (state : JointState) :
    (loggedLinkedImpl decode c key query).run state = (linkedImpl decode c key query).run state := by
  rcases state with ⟨state, base⟩
  rw [loggedLinkedImpl_run, linkedImpl_run]
  rw [noRaw_mode_eq decode c key _ (by
    simpa only [notRaw, if_false] using reductionImpl_raw_query_bound_step decode query state) base]

/-- The logged linked execution needs no ambient history-alignment assumption: it preserves the proved initial full-history relation. -/
theorem loggedLinked_preserves_aligned (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (loggedLinkedImpl decode c key) Aligned := by
  rintro query ⟨state, base⟩ aligned result supported
  cases query with
  | inl request =>
    rw [loggedLinkedImpl_nonraw decode c key _ (by simp [AdaptiveCtxReceive.IsRawQuery])] at supported
    exact linked_preserves_aligned decode c key _ _ aligned result supported
  | inr raw =>
    rw [loggedLinkedImpl_run] at supported
    obtain ⟨value, step, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
    exact loggedRaw_preserves_aligned decode c key raw state base aligned value step

/-- Direct source interpretation for the logged world: honest primitive encryption is unchanged and raw verification consults only its public encryption log after the exact private lookup. -/
noncomputable def loggedImpl (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxReceive.ReceiveState ProbComp) :=
  fun query state => match query with
  | .inl (.inl coin) => do
    let answer ← unifSpec.query coin
    pure (answer, state)
  | .inl (.inr query) => independentCtx c key query state
  | .inr raw => loggedRaw decode raw state

/-- Full per-query projection retains the actual logged optional plaintext and every source-state component. -/
theorem loggedLinked_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : JointState) (aligned : Aligned state) :
    Prod.map id Prod.fst <$> (loggedLinkedImpl decode c key query).run state =
      (loggedImpl decode c key query).run state.1 := by
  cases query with
  | inl request =>
    rw [loggedLinkedImpl_nonraw decode c key _ (by simp [AdaptiveCtxReceive.IsRawQuery])]
    cases request <;> exact linked_projection decode c key _ state aligned
  | inr raw =>
    rcases state with ⟨state, base⟩
    rw [loggedLinkedImpl_run]
    simp only [Functor.map_map]
    exact loggedRaw_projection decode c key raw state base aligned

/-- The entire arbitrary adaptive logged source execution retains its full poststate. -/
noncomputable def loggedGame (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × AdaptiveCtxReceive.ReceiveState) :=
  (simulateQ (loggedImpl decode c key) adversary).run AdaptiveCtxReceive.initialState

/-- Exact complete-continuation bridge from the linked log/reject game to direct persistent-cache source semantics. -/
theorem linkedLoggedGame_projection (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    Prod.map id Prod.fst <$> linkedGame false decode c key adversary = loggedGame decode c key adversary := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (loggedLinkedImpl decode c key) (loggedImpl decode c key) Aligned Prod.fst
    (loggedLinked_preserves_aligned decode c key) (loggedLinked_projection decode c key)
    adversary (AdaptiveCtxReceive.initialState, AdaptiveRawNonceAead.initialState, false) initial_aligned

/-- Every private lookup, including a failed raw attempt, retains all earlier dictionary values exactly. -/
theorem suffixStep_preserves (query known : Pqxdh.Bytes) (cache : SplitCache) (digest : CtxDigest)
    (cached : cache.suffixCache known = some digest) (result : CtxDigest × SplitCache)
    (supported : result ∈ support (ctxKeyFreeSuffixStep query cache)) :
    result.2.suffixCache known = some digest := by
  unfold ctxKeyFreeSuffixStep at supported
  split at supported
  · obtain rfl := eq_of_mem_support_pure supported
    exact cached
  · rename_i missing
    obtain ⟨sample, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    have distinct : known ≠ query := by
      intro same
      rw [same, missing] at cached
      contradiction
    simpa [cacheSuffix, QueryCache.cacheQuery_of_ne cache.suffixCache sample distinct] using cached

/-- A cache hit reuses the existing value and a miss installs the sampled value, even if subsequent verification rejects. -/
theorem suffixStep_installs (query : Pqxdh.Bytes) (cache : SplitCache) (result : CtxDigest × SplitCache)
    (supported : result ∈ support (ctxKeyFreeSuffixStep query cache)) :
    result.2.suffixCache query = some result.1 := by
  unfold ctxKeyFreeSuffixStep at supported
  split at supported
  · rename_i digest cached
    obtain rfl := eq_of_mem_support_pure supported
    exact cached
  · obtain ⟨sample, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    simp [cacheSuffix]

theorem seal_preserves_commitments (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (cached : CtxIndependentTagStateCommitmentsCached state)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (supported : result ∈ support ((ctxKeyFreeSealOracle c key input).run state)) :
    CtxIndependentTagStateCommitmentsCached result.2 := by
  by_cases used : input.nonce ∈ state.usedNonces
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_true] at supported
    obtain rfl := eq_of_mem_support_pure supported
    exact cached
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_false] at supported
    obtain ⟨suffixResult, suffixSupported, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    intro entry member
    simp only [CtxIndependentTagState.addSeal, List.mem_cons] at member
    rcases member with rfl | member
    · exact suffixStep_installs _ _ _ suffixSupported
    · exact suffixStep_preserves _ _ _ _ (cached entry member) _ suffixSupported

/-- Nonce bookkeeping is independent of whether the suffix lookup is a hit or miss. -/
theorem seal_preserves_nonces (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (marked : CtxIndependentTagStateSealsMarkedUsed state)
    (unique : CtxIndependentTagStateUniqueSealNonces state)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (supported : result ∈ support ((ctxKeyFreeSealOracle c key input).run state)) :
    CtxIndependentTagStateSealsMarkedUsed result.2 ∧
      CtxIndependentTagStateUniqueSealNonces result.2 := by
  by_cases used : input.nonce ∈ state.usedNonces
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_true] at supported
    obtain rfl := eq_of_mem_support_pure supported
    exact ⟨marked, unique⟩
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_false] at supported
    obtain ⟨suffixResult, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    constructor
    · intro entry member
      simp only [CtxIndependentTagState.addSeal, List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (marked entry member)
    · intro left hleft right hright same
      simp only [CtxIndependentTagState.addSeal, List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exact False.elim (used (same ▸ marked right hright))
      · exact False.elim (used (same ▸ marked left hleft))
      · exact unique left hleft right hright same

/-- Exact ordinary opening correctness of issued base ciphertexts survives cached commitments. -/
theorem seal_preserves_history (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (correct : AdaptiveRawNonceAead.HistoryCorrect c key
      (state.successfulSeals.map CtxNonceAeadIntCtxt.CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal))
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (supported : result ∈ support ((ctxKeyFreeSealOracle c key input).run state)) :
    AdaptiveRawNonceAead.HistoryCorrect c key
      (result.2.successfulSeals.map CtxNonceAeadIntCtxt.CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal) := by
  by_cases used : input.nonce ∈ state.usedNonces
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_true] at supported
    obtain rfl := eq_of_mem_support_pure supported
    exact correct
  · unfold ctxKeyFreeSealOracle at supported
    simp only [StateT.run, used, if_false] at supported
    obtain ⟨suffixResult, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
    obtain rfl := eq_of_mem_support_pure supported
    intro entry member
    simp only [CtxIndependentTagState.addSeal, List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact c.aead_open_seal _ _ _ _
    · exact correct entry member


/-- Full terminal key retention relates the direct persistent-cache logged source to the executable ordinary client without a further security loss. -/
noncomputable def retainedDirectLoggedGame (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × AdaptiveCtxReceive.ReceiveState)) := do
  let key ← $ᵗ CtxKey
  let result ← loggedGame decode c key adversary
  pure (key, result)

theorem retainedDirectLoggedGame_eq_client (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    retainedDirectLoggedGame decode c adversary =
      AdaptiveCtxLogSimulation.retainedLoggedGame decode c adversary := by
  rw [AdaptiveCtxLogSimulation.retainedLoggedGame_eq]
  simp only [retainedDirectLoggedGame, AdaptiveCtxRetainedKey.retainedLinkedGame,
    map_bind, bind_pure_comp, Functor.map_map, AdaptiveCtxRetainedKey.sourceProjection]
  congr 1
  funext key
  simpa only [Functor.map_map, Function.comp_def] using
    congrArg (fun game => (Prod.mk key) <$> game) (linkedLoggedGame_projection decode c key adversary).symm

/-- A logged raw acceptance with full CTX freshness must change the authenticated outer context of an existing base encryption. This classification does not rely on a claimed plaintext or on resampling a suffix. -/
theorem loggedFresh_is_alias (key : CtxKey) (state : CtxIndependentTagState)
    (target : CtxUnclaimedAcceptance.Target) (expected : CtxDigest) (next : SplitCache)
    (cached : CtxComputationalSecurity.CtxIndependentTagStateCommitmentsCached state)
    (fresh : ∀ entry ∈ state.successfulSeals, ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (commitment : target.record.commit = expected)
    (opened : AdaptiveRawNonceAead.loggedPlaintext
      (ctxIndependentTagStateToModifiedNonceAead state).successfulSeals (baseTarget target) ≠ none)
    (lookup : (expected, next) ∈ support
      (ctxKeyFreeSuffixStep (outerSuffix target.nonce target.context target.record.tag) state.cache)) :
    CtxFullAliasShape ⟨key, target.toLegacy, state.successfulSeals, state.usedNonces, state.publicInputs⟩ := by
  have notFresh : ¬ModifiedNonceAeadFresh
      (state.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal)
      (baseTarget target) := by
    intro h
    exact opened ((AdaptiveRawNonceAead.loggedPlaintext_none_iff_fresh _ _).mpr h)
  simp only [ModifiedNonceAeadFresh, List.forall_mem_map, not_forall, not_not] at notFresh
  obtain ⟨source, sourceMem, sameNonce, sameAd, sameCipher⟩ := notFresh
  change target.nonce = source.input.nonce at sameNonce
  change target.context.ad.bytes = source.input.context.ad.bytes at sameAd
  have sameBody := congrArg ModifiedNonceAeadCiphertext.body sameCipher
  have sameTag := congrArg ModifiedNonceAeadCiphertext.tag sameCipher
  change target.record.body = source.record.body at sameBody
  change target.record.tag = source.record.tag at sameTag
  have differentContext : target.context.ad ≠ source.input.context.ad := by
    intro sameContext
    have sameSuffix : outerSuffix target.nonce target.context target.record.tag =
        outerSuffix source.input.nonce source.input.context source.record.tag := by
      simp [outerSuffix, sameNonce, sameContext, sameTag]
    have cachedSource := cached source sourceMem
    rw [← sameSuffix] at cachedSource
    unfold ctxKeyFreeSuffixStep at lookup
    rw [cachedSource, support_pure, Set.mem_singleton_iff] at lookup
    have sameExpected : expected = source.record.commit := congrArg (fun pair => pair.1) lookup
    have sameCommitment := commitment.trans sameExpected
    have sameEncoding : target.record.encode = source.record.encode := by
      simp [CtxRomRecord.encode, CtxRomRecord.toRecordCipher, Pqxdh.RecordCipher.encode,
        sameBody, sameTag, sameCommitment]
    exact fresh source sourceMem ⟨sameNonce, sameContext, sameEncoding⟩
  exact ⟨fresh, source, sourceMem, sameNonce, sameAd, sameBody, sameTag, differentContext⟩

/-- An alias address differs from every honestly revealed commitment address by source nonce uniqueness and fixed-width transcript encoding, without any cryptographic constructor injectivity assumption. -/
theorem alias_excludes_honestSuffix (key : CtxKey) (state : CtxIndependentTagState)
    (target : CtxUnclaimedAcceptance.Target)
    (unique : CtxHonestTagSampling.CtxIndependentTagStateUniqueSealNonces state)
    (hasAlias : CtxFullAliasShape ⟨key, target.toLegacy, state.successfulSeals, state.usedNonces, state.publicInputs⟩) :
    ∀ honest ∈ state.successfulSeals,
      outerSuffix target.nonce target.context target.record.tag ≠
        outerSuffix honest.input.nonce honest.input.context honest.record.tag := by
  intro honest honestMem sameSuffix
  obtain ⟨source, sourceMem, sourceMatch⟩ := hasAlias.2
  have sameOuter : outerInput key target.nonce target.context target.record.tag =
      outerInput key honest.input.nonce honest.input.context honest.record.tag := by
    rw [outerInput_eq_secretAddress_outerSuffix, outerInput_eq_secretAddress_outerSuffix, sameSuffix]
  obtain ⟨sameMaterial, sameContext, _⟩ := Pqxdh.ctxPreimage_inj
    (recordWf key target.nonce target.context) (recordWf key honest.input.nonce honest.input.context)
    target.record.tagLength honest.record.tagLength sameOuter
  have sameNonce : target.nonce = honest.input.nonce :=
    List.Vector.toList_injective (congrArg Prod.snd sameMaterial)
  have sameSource : honest = source := unique honest honestMem source sourceMem
    (sameNonce.symm.trans sourceMatch.1)
  subst source
  exact sourceMatch.2.2.2.2 sameContext

/-- Every context alias reuses a base nonce already marked used; this is independent of private cache contents. -/
theorem alias_nonce_used (key : CtxKey) (state : CtxIndependentTagState)
    (target : CtxUnclaimedAcceptance.Target)
    (marked : CtxHonestTagSampling.CtxIndependentTagStateSealsMarkedUsed state)
    (hasAlias : CtxFullAliasShape ⟨key, target.toLegacy, state.successfulSeals, state.usedNonces, state.publicInputs⟩) :
    target.nonce ∈ state.usedNonces := by
  obtain ⟨source, sourceMem, sourceMatch⟩ := hasAlias.2
  have sameNonce : target.nonce = source.input.nonce := sourceMatch.1
  rw [sameNonce]
  exact marked source sourceMem

/-- Once a target nonce is used, any later permitted honest seal has a different suffix, irrespective of its AD, tag, sequence or sender. -/
theorem used_nonce_excludes_futureSuffix (target : CtxUnclaimedAcceptance.Target)
    (used : List CtxNonce) (marked : target.nonce ∈ used) (input : CtxSealInput)
    (fresh : input.nonce ∉ used) (tag : Pqxdh.Bytes) :
    outerSuffix target.nonce target.context target.record.tag ≠ outerSuffix input.nonce input.context tag := by
  intro same
  have sameNonce := CtxHonestTagSampling.outerSuffix_eq_implies_nonce_eq
    target.nonce input.nonce target.context input.context target.record.tag tag same
  exact fresh (sameNonce ▸ marked)

/-- The adaptive dictionary invariant permits private entries created by rejected raw attempts; it makes no honest-only cache provenance assertion. -/
def LoggedInvariant (c : Pqxdh.Crypto) (key : CtxKey) (state : AdaptiveCtxReceive.ReceiveState) : Prop :=
  CtxIndependentTagStateCommitmentsCached state.ctx ∧
  CtxIndependentTagStateSealsMarkedUsed state.ctx ∧
  CtxIndependentTagStateUniqueSealNonces state.ctx ∧
  AdaptiveRawNonceAead.HistoryCorrect c key
    (state.ctx.successfulSeals.map CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal)

/-- Every malformed or well-formed raw attempt retains honest cached commitments, nonce discipline and ordinary successful-encryption correctness. -/
theorem loggedRaw_preserves_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (invariant : LoggedInvariant c key state)
    (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (loggedRaw decode raw state)) :
    LoggedInvariant c key result.2 := by
  cases parsed : decode raw with
  | none =>
    simp only [loggedRaw, parsed, mem_support_pure_iff] at supported
    subst result
    exact invariant
  | some target =>
    simp only [loggedRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, lookupSupported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    refine ⟨?_, invariant.2⟩
    intro entry member
    exact suffixStep_preserves _ _ _ _ (invariant.1 entry member) _ lookupSupported

/-- Every actual logged source operation preserves the adaptive dictionary invariant without a cache-provenance premise. -/
theorem loggedImpl_preserves_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (loggedImpl decode c key) (LoggedInvariant c key) := by
  intro query state invariant result supported
  cases query with
  | inr raw => exact loggedRaw_preserves_invariant decode c key raw state invariant result supported
  | inl request =>
    cases request with
    | inl coin =>
      change result ∈ support ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)) at supported
      obtain ⟨value, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      exact invariant
    | inr operation =>
      change result ∈ support (independentCtx c key operation state) at supported
      unfold independentCtx at supported
      obtain ⟨ctxResult, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      cases operation with
      | inr input =>
        have nonces := seal_preserves_nonces c key input state.ctx invariant.2.1 invariant.2.2.1 ctxResult step
        exact ⟨seal_preserves_commitments c key input state.ctx invariant.1 ctxResult step,
          nonces.1, nonces.2, seal_preserves_history c key input state.ctx invariant.2.2.2 ctxResult step⟩
      | inl hash =>
        change ctxResult ∈ support ((ctxIndependentPublicOracle hash).run state.ctx) at step
        have cached := ctxIndependentPublicOracle_preserves_commitmentsCached hash state.ctx invariant.1 ctxResult step
        unfold ctxIndependentPublicOracle at step
        obtain ⟨oracleResult, _, step⟩ := (mem_support_bind_iff _ _ _).mp step
        obtain rfl := eq_of_mem_support_pure step
        exact ⟨cached, invariant.2⟩

/-- Every fresh source run starts from the proved empty invariant. -/
theorem initial_invariant (c : Pqxdh.Crypto) (key : CtxKey) :
    LoggedInvariant c key AdaptiveCtxReceive.initialState := by
  simp [LoggedInvariant, AdaptiveCtxReceive.initialState, emptyCtxIndependentTagState,
    CtxIndependentTagStateCommitmentsCached, CtxIndependentTagStateSealsMarkedUsed,
    CtxIndependentTagStateUniqueSealNonces, AdaptiveRawNonceAead.HistoryCorrect]

/-- The complete arbitrary adaptive logged execution reaches only states with correct honest commitments, nonce history and optional base opening. -/
theorem loggedGame_invariant (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (result : Result × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (loggedGame decode c key adversary)) :
    LoggedInvariant c key result.2 :=
  OracleComp.simulateQ_run_preservesInv (loggedImpl decode c key) (LoggedInvariant c key)
    (loggedImpl_preserves_invariant decode c key) adversary AdaptiveCtxReceive.initialState
    (initial_invariant c key) result supported

/-- A successful fresh raw reply is an alias on an already-used nonce, at an address distinct from every honestly exposed commitment. The premise uses the actual returned optional plaintext. -/
theorem loggedRaw_acceptedFresh_protected (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState)
    (invariant : LoggedInvariant c key state)
    (fresh : ∀ target, decode raw = some target → ∀ entry ∈ state.ctx.successfulSeals,
      ¬target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (loggedRaw decode raw state)) (accepted : result.1 ≠ none) :
    ∃ target, decode raw = some target ∧
      CtxFullAliasShape ⟨key, target.toLegacy, state.ctx.successfulSeals, state.ctx.usedNonces, state.ctx.publicInputs⟩ ∧
      target.nonce ∈ state.ctx.usedNonces ∧
      (∀ honest ∈ state.ctx.successfulSeals, outerSuffix target.nonce target.context target.record.tag ≠
        outerSuffix honest.input.nonce honest.input.context honest.record.tag) := by
  cases parsed : decode raw with
  | none =>
    simp only [loggedRaw, parsed, mem_support_pure_iff] at supported
    subst result
    exact False.elim (accepted rfl)
  | some target =>
    simp only [loggedRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, lookupSupported, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    by_cases commitEq : target.record.commit = lookup.1
    · simp only [commitEq, if_true] at accepted
      have hasAlias := loggedFresh_is_alias key state.ctx target lookup.1 lookup.2 invariant.1
        (fresh target parsed) commitEq accepted lookupSupported
      exact ⟨target, rfl, hasAlias, alias_nonce_used key state.ctx target invariant.2.1 hasAlias,
        alias_excludes_honestSuffix key state.ctx target invariant.2.2.1 hasAlias⟩
    · simp only [commitEq, if_false] at accepted
      exact False.elim (accepted rfl)

/-- Raw verification increments exactly one source counter slot, regardless of parsing or acceptance. -/
theorem loggedRaw_raw_count (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) (result : Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support (loggedRaw decode raw state)) :
    result.2.rawAttempts = state.rawAttempts + 1 := by
  cases parsed : decode raw with
  | none =>
    simp only [loggedRaw, parsed, mem_support_pure_iff] at supported
    subst result
    rfl
  | some target =>
    simp only [loggedRaw, parsed, mem_support_bind_iff] at supported
    obtain ⟨lookup, _, supported⟩ := supported
    obtain rfl := eq_of_mem_support_pure supported
    rfl

/-- The source counter advances once for every raw input, including malformed and commitment-rejected attempts. -/
theorem loggedImpl_raw_count (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (result : ReceiveSpec.Range query × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support ((loggedImpl decode c key query).run state)) :
    result.2.rawAttempts = state.rawAttempts + (if IsRawQuery query then 1 else 0) := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      change result ∈ support ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)) at supported
      obtain ⟨value, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      simp [IsRawQuery]
    | inr operation =>
      change result ∈ support (independentCtx c key operation state) at supported
      unfold independentCtx at supported
      obtain ⟨ctxResult, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      simp [IsRawQuery]
  | inr raw => exact loggedRaw_raw_count decode raw state result supported

/-- Every finite adaptive run respects the exact source raw-attempt cap from any prior counter. -/
theorem loggedRun_raw_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery qRaw) (state : AdaptiveCtxReceive.ReceiveState)
    (result : Result × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support ((simulateQ (loggedImpl decode c key) adversary).run state)) :
    result.2.rawAttempts ≤ state.rawAttempts + qRaw := by
  induction adversary using OracleComp.inductionOn generalizing qRaw state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    change result ∈ support ((loggedImpl decode c key query).run state >>= fun value =>
      (simulateQ (loggedImpl decode c key) (next value.1)).run value.2) at supported
    obtain ⟨value, step, tail⟩ := (mem_support_bind_iff _ _ _).mp supported
    have rest := ih value.1 _ (bounded.2 value.1) value.2 tail
    have count := loggedImpl_raw_count decode c key query state value step
    by_cases raw : IsRawQuery query
    · have positive : 0 < qRaw := bounded.1.resolve_left (not_not.mpr raw)
      simp only [raw, if_true] at rest count
      omega
    · simp only [raw, if_false] at rest count
      omega

/-- Every well-formed logged verification pays at most one 64-byte private digest draw; cache hits reuse the existing value. -/
theorem loggedRaw_uniform_bound (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (loggedRaw decode raw state).IsTotalQueryBound 64 := by
  cases parsed : decode raw with
  | none => simp only [loggedRaw, parsed]; trivial
  | some target =>
    simpa only [loggedRaw, parsed, bind_pure_comp, OracleComp.IsTotalQueryBound,
        OracleComp.isQueryBound_map_iff] using
      CtxUnclaimedAcceptance.suffixStep_uniform_query_bound
        (outerSuffix target.nonce target.context target.record.tag) state.ctx.cache

/-- Exact interpreted source cost per query: one arbitrary uniform request, or at most 64 byte-valued requests for the actual public/private digest cache. -/
theorem loggedImpl_uniform_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((loggedImpl decode c key query).run state).IsQueryBoundP (fun _ => True)
      (if AdaptiveCtxQueryBounds.SourceUniform query then 1 else 64) := by
  cases query with
  | inl request =>
    cases request <;>
      exact AdaptiveCtxPrefixQueryBounds.sourceImpl_uniform_step false decode c key _ state
  | inr raw =>
    exact (OracleComp.isQueryBoundP_true_iff _ _).mpr (loggedRaw_uniform_bound decode raw state)

/-- All source randomness and every hash, seal and raw-attempt slot are included in the complete fixed-key logged execution. -/
theorem loggedGame_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (loggedGame decode c key adversary).IsTotalQueryBound (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  AdaptiveCtxPrefixQueryBounds.run_uniform_pair_bound (loggedImpl decode c key)
    (loggedImpl_uniform_step decode c key) adversary qCoins (qHash + qSeal + qRaw) coinBound
    (AdaptiveCtxQueryBounds.sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound)
    AdaptiveCtxReceive.initialState

/-- The complete uniform-key challenger additionally charges all 32 key bytes; retaining that key for analysis adds no oracle request or adversary reveal. -/
theorem retainedDirectLoggedGame_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (retainedDirectLoggedGame decode c adversary).IsTotalQueryBound
      (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  unfold retainedDirectLoggedGame
  apply OracleComp.isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro key
  simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    loggedGame_uniform_bound decode c key adversary qCoins qHash qSeal qRaw coinBound hashBound sealBound rawBound

end BeaconcryptCore.Computational.AdaptiveCtxLoggedSource

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.linkedLoggedGame_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.linkedLoggedGame_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.retainedDirectLoggedGame_eq_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.retainedDirectLoggedGame_eq_client

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_commitments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_commitments

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_nonces

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.seal_preserves_history

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedFresh_is_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedFresh_is_alias

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.alias_excludes_honestSuffix' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.alias_excludes_honestSuffix

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.used_nonce_excludes_futureSuffix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.used_nonce_excludes_futureSuffix

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedImpl_preserves_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedImpl_preserves_invariant

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedGame_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedGame_invariant

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedRaw_acceptedFresh_protected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedRaw_acceptedFresh_protected

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedRun_raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.loggedRun_raw_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.retainedDirectLoggedGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxLoggedSource.retainedDirectLoggedGame_uniform_bound
