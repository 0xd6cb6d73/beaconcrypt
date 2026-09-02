import BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation
import VCVio.CryptoFoundations.SecExp

/-!
# Modified CTX computational security

This module composes the exact split-cache projection, key-free independent-tag game, fresh honest-tag sampling, retained-base INT-CTXT reduction, and both conventional and key-probe IND$ reductions.
It proves the final typed full-fresh one-key CTX bounds with explicit query accounting.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxComputationalSecurity

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling CtxNonceAeadIntCtxt CtxNonceAeadIndDollar
  CtxNonceAeadIndDollarValidation

/-- The exact union already exposed by the scheme-specific retained-base/alias classification. -/
def CtxClassifiedForgeryAt (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  CtxFreshAcceptedRetainedBase c before ∨
    CtxAcceptedFullAliasReplayAt c before expected

/-- Full freshness of the complete typed `(nonce, context, C || T || T*)` tuple. -/
def CtxTypedFullFresh (before : CtxBeforeVerify) : Prop :=
  ∀ entry ∈ before.successfulSeals,
    ¬ before.target.sameFullTupleAsSuccessfulSeal entry

/-- Actual typed full-fresh CTX acceptance at the final expected outer tag. -/
def CtxAcceptedTypedFullFreshAt (c : Pqxdh.Crypto)
    (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  CtxTypedFullFresh before ∧
    before.target.record.commit = expected ∧
    c.aeadOpen before.key.toList before.target.nonce.toList
      before.target.context.ad.bytes before.target.record.body
      before.target.record.tag = some before.target.claimedPlaintext

/-- Every recorded honest tag is still installed at its exact key-free suffix. -/
def CtxHonestCommitmentsCached (before : CtxBeforeVerify)
    (cache : SplitCache) : Prop :=
  ∀ entry ∈ before.successfulSeals,
    cache.suffixCache
      (outerSuffix entry.input.nonce entry.input.context entry.record.tag) =
        some entry.record.commit

/-- Direct-state form of exact honest commitment cache soundness. -/
def CtxIndependentTagStateCommitmentsCached
    (state : CtxIndependentTagState) : Prop :=
  ∀ entry ∈ state.successfulSeals,
    state.cache.suffixCache
      (outerSuffix entry.input.nonce entry.input.context entry.record.tag) =
        some entry.record.commit

@[simp] theorem emptyCtxIndependentTagState_commitmentsCached :
    CtxIndependentTagStateCommitmentsCached emptyCtxIndependentTagState := by
  simp [CtxIndependentTagStateCommitmentsCached, emptyCtxIndependentTagState]

theorem ctxIndependentPublicOracle_preserves_commitmentsCached
    (query : CtxRO.Domain) (state : CtxIndependentTagState)
    (hsound : CtxIndependentTagStateCommitmentsCached state)
    (result : CtxDigest × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxIndependentPublicOracle query).run state)) :
    CtxIndependentTagStateCommitmentsCached result.2 := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache.publicCache >>=
      fun oracleResult =>
        let cache := { state.cache with publicCache := oracleResult.2 }
        pure (oracleResult.1, state.addPublic query.2 cache)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  simpa [CtxIndependentTagStateCommitmentsCached,
    CtxIndependentTagState.addPublic] using hsound

theorem ctxDirectSampleKeyFreeSealOracle_preserves_commitmentsCached
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state)
    (hsound : CtxIndependentTagStateCommitmentsCached state)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleKeyFreeSealOracle c key input).run state)) :
    CtxIndependentTagStateCommitmentsCached result.2 := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    exact hsound
  · let base := c.aeadSeal key.toList input.nonce.toList
      input.context.ad.bytes input.plaintext
    let suffix := outerSuffix input.nonce input.context base.2
    unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_false] at hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨commit, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    let record : CtxRomRecord :=
      ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
    intro entry hentry
    simp only [CtxIndependentTagState.addSeal, List.mem_cons] at hentry
    rcases hentry with hnew | hold
    · subst entry
      change (cacheSuffix state.cache suffix commit).suffixCache suffix =
        some commit
      simp [cacheSuffix]
    · have holdCached := hsound entry hold
      have hfresh : state.cache.suffixCache suffix = none := by
        exact ctxKeyFreeSeal_suffix_fresh_of_unused c key input state
          hinvariant hused
      have hne :
          outerSuffix entry.input.nonce entry.input.context entry.record.tag ≠
            suffix := by
        intro heq
        rw [heq, hfresh] at holdCached
        simp at holdCached
      change (cacheSuffix state.cache suffix commit).suffixCache
        (outerSuffix entry.input.nonce entry.input.context entry.record.tag) =
          some entry.record.commit
      simpa [cacheSuffix,
        QueryCache.cacheQuery_of_ne state.cache.suffixCache commit hne] using
        holdCached

theorem ctxDirectSampleIndependentTagImpl_preserves_full_invariant
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (ctxDirectSampleIndependentTagImpl c key)
      (fun state => CtxIndependentTagStateInvariant state ∧
        CtxIndependentTagStateCommitmentsCached state) := by
  intro query state hstate result hresult
  rcases query with query | input
  · exact ⟨ctxIndependentPublicOracle_preserves_invariant query state
      hstate.1 result hresult,
      ctxIndependentPublicOracle_preserves_commitmentsCached query state
        hstate.2 result hresult⟩
  · exact ⟨ctxDirectSampleKeyFreeSealOracle_preserves_invariant
      c key input state hstate.1 result hresult,
      ctxDirectSampleKeyFreeSealOracle_preserves_commitmentsCached
        c key input state hstate.1 hstate.2 result hresult⟩

theorem ctxDirectSampleIndependentTag_run_commitmentsCached
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    CtxIndependentTagStateCommitmentsCached result.2 := by
  exact (OracleComp.simulateQ_run_preservesInv
    (ctxDirectSampleIndependentTagImpl c key)
    (fun state => CtxIndependentTagStateInvariant state ∧
      CtxIndependentTagStateCommitmentsCached state)
    (ctxDirectSampleIndependentTagImpl_preserves_full_invariant c key)
    adversary.main emptyCtxIndependentTagState
    ⟨emptyCtxIndependentTagState_invariant,
      emptyCtxIndependentTagState_commitmentsCached⟩ result hresult).2

theorem independentTrackedProjection_commitmentsCached
    (key : CtxKey) (result : CtxAliasTarget × CtxIndependentTagState)
    (hsound : CtxIndependentTagStateCommitmentsCached result.2) :
    CtxHonestCommitmentsCached
      (independentTrackedProjection key result).1
      (independentTrackedProjection key result).2 := by
  simpa [CtxHonestCommitmentsCached,
    CtxIndependentTagStateCommitmentsCached,
    independentTrackedProjection, independentHandlerStateToBeforeVerify] using
    hsound

/-- Every direct uniform-key transcript retains exact honest cache values. -/
theorem ctxDirectSampleIndependentTagGame_commitmentsCached
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (result : CtxBeforeVerify × SplitCache)
    (hresult : result ∈ support
      (ctxDirectSampleIndependentTagGame c adversary)) :
    CtxHonestCommitmentsCached result.1 result.2 := by
  unfold ctxDirectSampleIndependentTagGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨key, _, hresult⟩ := hresult
  unfold ctxDirectSampleIndependentTagBeforeVerifyInner at hresult
  rw [support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  exact independentTrackedProjection_commitmentsCached key source
    (ctxDirectSampleIndependentTag_run_commitmentsCached
      c key adversary source hsource)

/-- Typed full-fresh acceptance projects pointwise to the retained/alias union when honest cache values are sound. -/
theorem acceptedTypedFullFreshAt_implies_classified_of_cache_sound
    (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (cache next : SplitCache)
    (expected : CtxDigest)
    (hsound : CtxHonestCommitmentsCached before cache)
    (horacle : (expected, next) ∈ support
      (ctxKeyFreeSuffixStep
        (outerSuffix before.target.nonce before.target.context
          before.target.record.tag) cache))
    (haccepted : CtxAcceptedTypedFullFreshAt c before expected) :
    CtxClassifiedForgeryAt c before expected := by
  classical
  unfold CtxClassifiedForgeryAt
  by_cases hbaseFresh : ModifiedNonceAeadFresh
    (before.successfulSeals.map
      CtxSuccessfulSeal.toModifiedNonceAeadSuccessfulSeal)
    (CtxAliasTarget.toModifiedNonceAeadForgery before.target)
  · exact Or.inl ⟨haccepted.2.2, hbaseFresh⟩
  · simp only [ModifiedNonceAeadFresh, List.forall_mem_map,
      not_forall, not_not] at hbaseFresh
    obtain ⟨source, hsource, hnonce, had, hcipher⟩ := hbaseFresh
    change before.target.nonce = source.input.nonce at hnonce
    change before.target.context.ad.bytes = source.input.context.ad.bytes at had
    have hbody := congrArg ModifiedNonceAeadCiphertext.body hcipher
    have htag := congrArg ModifiedNonceAeadCiphertext.tag hcipher
    change before.target.record.body = source.record.body at hbody
    change before.target.record.tag = source.record.tag at htag
    have hcontextNe :
        before.target.context.ad ≠ source.input.context.ad := by
      intro hcontext
      have hsuffix :
          outerSuffix before.target.nonce before.target.context
              before.target.record.tag =
            outerSuffix source.input.nonce source.input.context
              source.record.tag := by
        simp [outerSuffix, hnonce, hcontext, htag]
      have hcache := hsound source hsource
      rw [← hsuffix] at hcache
      unfold ctxKeyFreeSuffixStep at horacle
      rw [hcache, support_pure, Set.mem_singleton_iff] at horacle
      have hexpected : expected = source.record.commit :=
        congrArg (fun pair => pair.1) horacle
      have hcommit : before.target.record.commit = source.record.commit :=
        haccepted.2.1.trans hexpected
      have hencode : before.target.record.encode = source.record.encode := by
        simp [CtxRomRecord.encode, CtxRomRecord.toRecordCipher,
          Pqxdh.RecordCipher.encode, hbody, htag, hcommit]
      exact haccepted.1 source hsource ⟨hnonce, hcontext, hencode⟩
    right
    exact ⟨⟨haccepted.1, source, hsource,
      hnonce, had, hbody, htag, hcontextNe⟩,
      haccepted.2.1, haccepted.2.2⟩

/-- Final classified verifier over the key-free suffix cache. -/
noncomputable def ctxClassifiedVerifier (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × SplitCache) : ProbComp Bool := by
  classical
  exact do
    let suffix := outerSuffix result.1.target.nonce result.1.target.context
      result.1.target.record.tag
    let oracleResult ← ctxKeyFreeSuffixStep suffix result.2
    pure (decide (CtxClassifiedForgeryAt c result.1 oracleResult.1))

/-- Canonical split-cache classified modified-CTX game. -/
noncomputable def ctxClassifiedForgeryGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxSplitBeforeVerifyGame c adversary >>= ctxClassifiedVerifier c

/-- Direct independent-tag classified modified-CTX game. -/
noncomputable def ctxDirectClassifiedForgeryGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxDirectSampleIndependentTagGame c adversary >>= ctxClassifiedVerifier c

/-- Final verifier for the actual typed full-fresh event. -/
noncomputable def ctxTypedFullFreshVerifier (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × SplitCache) : ProbComp Bool := by
  classical
  exact do
    let suffix := outerSuffix result.1.target.nonce result.1.target.context
      result.1.target.record.tag
    let oracleResult ← ctxKeyFreeSuffixStep suffix result.2
    pure (decide (CtxAcceptedTypedFullFreshAt c result.1 oracleResult.1))

/-- Canonical split-cache game for actual typed full-fresh modified-CTX acceptance. -/
noncomputable def ctxTypedFullFreshForgeryGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxSplitBeforeVerifyGame c adversary >>= ctxTypedFullFreshVerifier c

/-- Direct independent-tag game for actual typed full-fresh modified-CTX acceptance. -/
noncomputable def ctxDirectTypedFullFreshForgeryGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxDirectSampleIndependentTagGame c adversary >>=
    ctxTypedFullFreshVerifier c

/-- An alias target in a reachable direct-sampling state addresses a fresh honest suffix. -/
theorem ctxDirectSample_alias_suffix_fresh
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (target : CtxAliasTarget) (state : CtxIndependentTagState)
    (hresult : (target, state) ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState))
    (halias : CtxFullAliasShape
      (independentHandlerStateToBeforeVerify key target state)) :
    state.cache.suffixCache
      (outerSuffix target.nonce target.context target.record.tag) = none := by
  have hinvariant := ctxDirectSampleIndependentTag_run_invariant
    c key adversary (target, state) hresult
  by_contra hhit
  obtain ⟨entry, hentry, hsuffix⟩ := hinvariant.2.2 _ hhit
  obtain ⟨source, hsource, hmatch⟩ := halias.2
  change source ∈ state.successfulSeals at hsource
  change target.matchesSuccessfulSeal source at hmatch
  have htargetEntry : target.nonce = entry.input.nonce :=
    outerSuffix_eq_implies_nonce_eq target.nonce entry.input.nonce
      target.context entry.input.context target.record.tag entry.record.tag
      hsuffix
  have hentrySource : entry = source :=
    hinvariant.2.1 entry hentry source hsource
      (htargetEntry.symm.trans hmatch.1)
  subst entry
  have houter :
      outerInput key target.nonce target.context target.record.tag =
        outerInput key source.input.nonce source.input.context
          source.record.tag := by
    rw [outerInput_eq_secretAddress_outerSuffix,
      outerInput_eq_secretAddress_outerSuffix, hsuffix]
  obtain ⟨_, hcontext, _⟩ := Pqxdh.ctxPreimage_inj
    (recordWf key target.nonce target.context)
    (recordWf key source.input.nonce source.input.context)
    target.record.tagLength source.record.tagLength houter
  exact hmatch.2.2.2.2 hcontext

/-- The classified verifier pays one inverse digest factor off the retained-base branch. -/
theorem ctxClassifiedVerifier_le_inv_of_direct_support
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (target : CtxAliasTarget) (state : CtxIndependentTagState)
    (hresult : (target, state) ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState))
    (hnotRetained : ¬ CtxFreshAcceptedRetainedBase c
      (independentHandlerStateToBeforeVerify key target state)) :
    Pr[= true | ctxClassifiedVerifier c
      (independentTrackedProjection key (target, state))] ≤
        (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  by_cases halias : CtxFullAliasShape
    (independentHandlerStateToBeforeVerify key target state)
  · have hfresh := ctxDirectSample_alias_suffix_fresh
      c key adversary target state hresult halias
    unfold ctxClassifiedVerifier
    simp only [independentTrackedProjection,
      independentHandlerStateToBeforeVerify]
    unfold ctxKeyFreeSuffixStep
    rw [hfresh]
    simp only [bind_assoc, pure_bind]
    rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
    refine (probEvent_mono''
      (q := fun x : CtxDigest => x = target.record.commit) ?_).trans ?_
    · intro expected haccepted
      simp only [Function.comp_apply, decide_eq_true_eq] at haccepted
      unfold CtxClassifiedForgeryAt at haccepted
      rcases haccepted with hretained | haliasAccepted
      · exact (hnotRetained hretained).elim
      · exact haliasAccepted.2.1.symm
    · rw [probEvent_eq_eq_probOutput,
        probOutput_uniformSample CtxDigest target.record.commit]
  · unfold ctxClassifiedVerifier
    unfold independentHandlerStateToBeforeVerify at hnotRetained halias
    simp only [independentTrackedProjection,
      independentHandlerStateToBeforeVerify]
    simp [CtxClassifiedForgeryAt, CtxAcceptedFullAliasReplayAt,
      hnotRetained, halias]

/-- On a cache-sound transcript, typed full-fresh verification is contained in the classified verifier. -/
theorem ctxTypedFullFreshVerifier_le_classified_of_cache_sound
    (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache)
    (hsound : CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | ctxTypedFullFreshVerifier c result] ≤
      Pr[= true | ctxClassifiedVerifier c result] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  unfold ctxTypedFullFreshVerifier ctxClassifiedVerifier
  simp only [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  intro oracleResult horacle haccepted
  simp only [Function.comp_apply, decide_eq_true_eq] at haccepted ⊢
  exact acceptedTypedFullFreshAt_implies_classified_of_cache_sound
    c result.1 result.2 oracleResult.2 oracleResult.1 hsound horacle haccepted

/-- A cache-sound direct pre-verification distribution lifts the pointwise typed-to-classified bridge. -/
theorem ctxDirectTypedFullFreshForgeryGame_le_classified_of_cache_sound
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (hsound : ∀ result ∈ support
      (ctxDirectSampleIndependentTagGame c adversary),
      CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] ≤
      Pr[= true | ctxDirectClassifiedForgeryGame c adversary] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  unfold ctxDirectTypedFullFreshForgeryGame
    ctxDirectClassifiedForgeryGame
  apply probEvent_bind_mono
  intro result hresult
  simpa [probEvent_eq_eq_probOutput] using
    (ctxTypedFullFreshVerifier_le_classified_of_cache_sound
      c result (hsound result hresult))

/-- The direct classified game is bounded by retained-base integrity plus one fresh digest. -/
theorem ctxDirectClassifiedForgeryGame_le_retained_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | ctxDirectClassifiedForgeryGame c adversary] ≤
      Pr[fun result : CtxBeforeVerify × SplitCache =>
          CtxFreshAcceptedRetainedBase c result.1 |
        ctxDirectSampleIndependentTagGame c adversary] +
      (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  unfold ctxDirectClassifiedForgeryGame
  refine probEvent_bind_le_probEvent_add ?_
  intro result hresult hnotRetained
  unfold ctxDirectSampleIndependentTagGame at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨key, _, hresult⟩ := hresult
  unfold ctxDirectSampleIndependentTagBeforeVerifyInner at hresult
  rw [support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  rcases source with ⟨target, state⟩
  simpa [probEvent_eq_eq_probOutput] using
    (ctxClassifiedVerifier_le_inv_of_direct_support
      c key adversary target state hsource hnotRetained)

/-- The canonical-to-direct hop charges the secret-prefix event exactly once. -/
theorem ctxClassifiedForgeryGame_le_direct_add_prefix
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | ctxClassifiedForgeryGame c adversary] ≤
      Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
        ctxSecretPrefixQueriedProbability c adversary := by
  have htv : tvDist (ctxClassifiedForgeryGame c adversary)
      (ctxDirectClassifiedForgeryGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    unfold ctxClassifiedForgeryGame ctxDirectClassifiedForgeryGame
    exact (tvDist_bind_right_le (ctxClassifiedVerifier c)
      (ctxSplitBeforeVerifyGame c adversary)
      (ctxDirectSampleIndependentTagGame c adversary)).trans
        (tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried
          c adversary)
  have hdiff := abs_probOutput_toReal_sub_le_tvDist
    (ctxClassifiedForgeryGame c adversary)
    (ctxDirectClassifiedForgeryGame c adversary)
  have hadv :
      (ctxClassifiedForgeryGame c adversary).boolDistAdvantage
          (ctxDirectClassifiedForgeryGame c adversary) ≤
        (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    simpa [ProbComp.boolDistAdvantage] using hdiff.trans htv
  calc
    Pr[= true | ctxClassifiedForgeryGame c adversary] ≤
        Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
          ENNReal.ofReal
            ((ctxClassifiedForgeryGame c adversary).boolDistAdvantage
              (ctxDirectClassifiedForgeryGame c adversary)) :=
      ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _ _
    _ ≤ Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
          ENNReal.ofReal
            (ctxSecretPrefixQueriedProbability c adversary).toReal := by
      gcongr
    _ = Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary := by
      have hprefix : ctxSecretPrefixQueriedProbability c adversary ≠ ⊤ := by
        unfold ctxSecretPrefixQueriedProbability
        exact probEvent_ne_top
      rw [ENNReal.ofReal_toReal hprefix]

/-- The actual typed full-fresh game pays the same single canonical-to-direct prefix charge. -/
theorem ctxTypedFullFreshForgeryGame_le_direct_add_prefix
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | ctxTypedFullFreshForgeryGame c adversary] ≤
      Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] +
        ctxSecretPrefixQueriedProbability c adversary := by
  have htv : tvDist (ctxTypedFullFreshForgeryGame c adversary)
      (ctxDirectTypedFullFreshForgeryGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    unfold ctxTypedFullFreshForgeryGame
      ctxDirectTypedFullFreshForgeryGame
    exact (tvDist_bind_right_le (ctxTypedFullFreshVerifier c)
      (ctxSplitBeforeVerifyGame c adversary)
      (ctxDirectSampleIndependentTagGame c adversary)).trans
        (tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried
          c adversary)
  have hdiff := abs_probOutput_toReal_sub_le_tvDist
    (ctxTypedFullFreshForgeryGame c adversary)
    (ctxDirectTypedFullFreshForgeryGame c adversary)
  have hadv :
      (ctxTypedFullFreshForgeryGame c adversary).boolDistAdvantage
          (ctxDirectTypedFullFreshForgeryGame c adversary) ≤
        (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    simpa [ProbComp.boolDistAdvantage] using hdiff.trans htv
  calc
    Pr[= true | ctxTypedFullFreshForgeryGame c adversary] ≤
        Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] +
          ENNReal.ofReal
            ((ctxTypedFullFreshForgeryGame c adversary).boolDistAdvantage
              (ctxDirectTypedFullFreshForgeryGame c adversary)) :=
      ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _ _
    _ ≤ Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] +
          ENNReal.ofReal
            (ctxSecretPrefixQueriedProbability c adversary).toReal := by
      gcongr
    _ = Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary := by
      have hprefix : ctxSecretPrefixQueriedProbability c adversary ≠ ⊤ := by
        unfold ctxSecretPrefixQueriedProbability
        exact probEvent_ne_top
      rw [ENNReal.ofReal_toReal hprefix]

/-- Core classified modified-CTX bound before reducing the one prefix event. -/
theorem ctxClassifiedForgeryProbability_le_intCtxt_add_prefix_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | ctxClassifiedForgeryGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true | ctxClassifiedForgeryGame c adversary] ≤
        Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary :=
      ctxClassifiedForgeryGame_le_direct_add_prefix c adversary
    _ ≤ (Pr[fun result : CtxBeforeVerify × SplitCache =>
            CtxFreshAcceptedRetainedBase c result.1 |
          ctxDirectSampleIndependentTagGame c adversary] +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact ctxDirectClassifiedForgeryGame_le_retained_add_inv c adversary
    _ ≤ (modifiedNonceAeadINTCTXTAdvantage c
            (ctxRetainedBaseReduction adversary) +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact ctxFreshAcceptedRetainedBaseProbability_le_intCtxtAdvantage
        c adversary
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [ctxDigest_card]
      ac_rfl

/-- Actual typed full-fresh security follows from the classified core whenever direct honest cache values are sound. -/
theorem ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv_of_cache_sound
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (hsound : ∀ result ∈ support
      (ctxDirectSampleIndependentTagGame c adversary),
      CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | ctxTypedFullFreshForgeryGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true | ctxTypedFullFreshForgeryGame c adversary] ≤
        Pr[= true | ctxDirectTypedFullFreshForgeryGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary :=
      ctxTypedFullFreshForgeryGame_le_direct_add_prefix c adversary
    _ ≤ Pr[= true | ctxDirectClassifiedForgeryGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact ctxDirectTypedFullFreshForgeryGame_le_classified_of_cache_sound
        c adversary hsound
    _ ≤ (Pr[fun result : CtxBeforeVerify × SplitCache =>
            CtxFreshAcceptedRetainedBase c result.1 |
          ctxDirectSampleIndependentTagGame c adversary] +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact ctxDirectClassifiedForgeryGame_le_retained_add_inv c adversary
    _ ≤ (modifiedNonceAeadINTCTXTAdvantage c
            (ctxRetainedBaseReduction adversary) +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact ctxFreshAcceptedRetainedBaseProbability_le_intCtxtAdvantage
        c adversary
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [ctxDigest_card]
      ac_rfl

/-- Unconditional actual typed full-fresh core bound from the reachable direct cache invariant. -/
theorem ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | ctxTypedFullFreshForgeryGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  exact ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv_of_cache_sound
    c adversary (ctxDirectSampleIndependentTagGame_commitmentsCached
      c adversary)

/-- Final one-key classified modified-CTX computational bound with explicit `qH` accounting. -/
theorem ctxClassifiedForgeryProbability_le_intCtxt_add_indDollar_add_guesses
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    Pr[= true |
        ctxClassifiedForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true |
        ctxClassifiedForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ :=
      ctxClassifiedForgeryProbability_le_intCtxt_add_prefix_add_inv
        c adversary.toCtxAdversary
    _ ≤ modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        (ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
          (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹) +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      gcongr
      exact ctxSecretPrefixQueriedProbability_le_modifiedNonceAeadINDDollar
        c adversary
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      ac_rfl

/-- Final actual typed full-fresh one-key modified-CTX bound with explicit `qH` terms. -/
theorem ctxTypedFullFreshForgeryProbability_le_intCtxt_add_indDollar_add_guesses
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    Pr[= true |
        ctxTypedFullFreshForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true |
        ctxTypedFullFreshForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ :=
      ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv
        c adversary.toCtxAdversary
    _ ≤ modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        (ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
          (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹) +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      gcongr
      exact ctxSecretPrefixQueriedProbability_le_modifiedNonceAeadINDDollar
        c adversary
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      ac_rfl

/-- Final conventional Boolean IND$ bound, using one fresh validation encryption and a 128-bit random-world tag check. -/
theorem ctxTypedFullFreshForgeryProbability_le_intCtxt_add_booleanIndDollar_add_guesses
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    Pr[= true |
        ctxTypedFullFreshForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrefixToBooleanINDDollarReduction c adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true |
        ctxTypedFullFreshForgeryGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ :=
      ctxTypedFullFreshForgeryProbability_le_intCtxt_add_prefix_add_inv
        c adversary.toCtxAdversary
    _ ≤ modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        (ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrefixToBooleanINDDollarReduction c adversary)) +
          (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹) +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      gcongr
      exact ctxSecretPrefixQueriedProbability_le_booleanINDDollar
        c adversary hqE
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrefixToBooleanINDDollarReduction c adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      ac_rfl

/-- One uniform byte costs one underlying `unifSpec` query. -/
theorem uniformUInt8_isTotalQueryBound :
    ($ᵗ UInt8).IsTotalQueryBound 1 := by
  change IsTotalQueryBound
    ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
      ($[0..255] : ProbComp (Fin 256))) 1
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  change OracleComp.IsQueryBound
    (liftM (unifSpec.query 255) : ProbComp (Fin 256)) 1
      (fun _ b => 0 < b) (fun _ b => b - 1)
  rw [OracleComp.isQueryBound_query_iff]
  omega

/-- A uniform fixed byte vector costs exactly its width in underlying queries. -/
theorem uniformFixedBytes_isTotalQueryBound (n : ℕ) :
    ($ᵗ List.Vector UInt8 n).IsTotalQueryBound n := by
  have hvector : ($ᵗ Vector UInt8 n).IsTotalQueryBound n := by
    induction n with
    | zero =>
        change IsTotalQueryBound (pure #v[]) 0
        trivial
    | succ n ih =>
        change IsTotalQueryBound
          (Vector.push <$> ($ᵗ Vector UInt8 n) <*> ($ᵗ UInt8)) (n + 1)
        exact OracleComp.isTotalQueryBound_seq
          ((OracleComp.isQueryBound_map_iff _ _ _ _ _).2 ih)
          uniformUInt8_isTotalQueryBound
  change IsTotalQueryBound
    (List.Vector.ofFn <$>
      ((fun (v : Vector UInt8 n) (i : Fin n) => v.get i) <$>
        ($ᵗ Vector UInt8 n))) n
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff, OracleComp.isQueryBound_map_iff]
  exact hvector

/-- Identify primitive-interface uniform-randomness queries. -/
def IsModifiedNonceAeadUniformQuery :
    ModifiedNonceAeadAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsModifiedNonceAeadUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

theorem liftProbComp_uniform_query_bound
    {alpha : Type} {oa : ProbComp alpha} {n : ℕ}
    (hbound : oa.IsTotalQueryBound n) :
    (OracleComp.liftComp oa ModifiedNonceAeadAdversarySpec).IsQueryBoundP
      IsModifiedNonceAeadUniformQuery n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind query rest ih =>
      rw [OracleComp.isTotalQueryBound_query_bind_iff] at hbound
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM (ModifiedNonceAeadAdversarySpec.query (.inl query)) >>=
          fun response => OracleComp.liftComp (rest response)
            ModifiedNonceAeadAdversarySpec)).IsQueryBoundP
        IsModifiedNonceAeadUniformQuery n
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun response => ?_⟩
      · simpa [IsModifiedNonceAeadUniformQuery] using hbound.1
      · simpa [IsModifiedNonceAeadUniformQuery] using
          ih response (hbound.2 response)

theorem ctxRandomOracle_total_query_bound
    (query : CtxRO.Domain) (cache : CtxRO.QueryCache) :
    ((ctxRandomOracle query).run cache).IsTotalQueryBound 64 := by
  cases hcache : cache query with
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache]
      unfold IsTotalQueryBound
      rw [OracleComp.isQueryBound_map_iff]
      exact uniformFixedBytes_isTotalQueryBound 64
  | some digest =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
      trivial

theorem ctxIndependentPublicOracle_total_query_bound
    (query : CtxRO.Domain) (state : CtxIndependentTagState) :
    ((ctxIndependentPublicOracle query).run state).IsTotalQueryBound 64 := by
  change IsTotalQueryBound
    ((ctxRandomOracle query).run state.cache.publicCache >>= fun result =>
      pure (result.1, state.addPublic query.2
        { state.cache with publicCache := result.2 })) 64
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := 64) (n₂ := 0)
    (ctxRandomOracle_total_query_bound query state.cache.publicCache)
    (fun result => show IsTotalQueryBound
      (pure (result.1, state.addPublic query.2
        { state.cache with publicCache := result.2 }) :
          ProbComp (CtxDigest × CtxIndependentTagState)) 0 from trivial)

theorem ctxRetainedBasePublicOracle_uniform_query_bound
    (query : CtxRO.Domain) (state : CtxIndependentTagState) :
    ((ctxRetainedBasePublicOracle query).run state).IsQueryBoundP
      IsModifiedNonceAeadUniformQuery 64 := by
  unfold ctxRetainedBasePublicOracle
  exact liftProbComp_uniform_query_bound
    (ctxIndependentPublicOracle_total_query_bound query state)

theorem queryModifiedNonceAeadSeal_no_uniform_queries
    (input : ModifiedNonceAeadSealInput) :
    (queryModifiedNonceAeadSeal input).IsQueryBoundP
      IsModifiedNonceAeadUniformQuery 0 := by
  unfold queryModifiedNonceAeadSeal
  exact (OracleComp.isQueryBoundP_query_iff
    (spec := ModifiedNonceAeadAdversarySpec)
    (p := IsModifiedNonceAeadUniformQuery)
    (.inr input) 0).2 (by simp [IsModifiedNonceAeadUniformQuery])

theorem modifiedNonceAeadDigest_uniform_query_bound :
    modifiedNonceAeadDigest.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery 64 := by
  unfold modifiedNonceAeadDigest
  exact liftProbComp_uniform_query_bound
    (uniformFixedBytes_isTotalQueryBound 64)

theorem ctxRetainedBaseSealOracle_uniform_query_bound
    (input : CtxSealInput) (state : CtxIndependentTagState) :
    ((ctxRetainedBaseSealOracle input).run state).IsQueryBoundP
      IsModifiedNonceAeadUniformQuery 64 := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxRetainedBaseSealOracle
    simp [StateT.run, hused]
  · simp only [ctxRetainedBaseSealOracle, StateT.run, hused, if_false]
    unfold queryModifiedNonceAeadSeal
    refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 64) ?_ ?_).mono ?_
    · exact queryModifiedNonceAeadSeal_no_uniform_queries
        (CtxSealInput.toModifiedNonceAeadSealInput input)
    · intro base _
      cases base with
      | none => simp
      | some ciphertext =>
          exact (OracleComp.isQueryBoundP_map_iff
            modifiedNonceAeadDigest _ 64).mpr
              modifiedNonceAeadDigest_uniform_query_bound
    · omega

theorem OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step_le_total
    {i i' : Type} {spec : OracleSpec i} {spec' : OracleSpec i'}
    {sigma alpha : Type} {q : i' → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT sigma (OracleComp spec'))}
    {oa : OracleComp spec alpha} {n step : ℕ}
    (hbound : oa.IsTotalQueryBound n)
    (hstep : ∀ query state,
      ((impl query).run state).IsQueryBoundP q step)
    (state : sigma) :
    ((simulateQ impl oa).run state).IsQueryBoundP q (n * step) := by
  induction oa using OracleComp.inductionOn generalizing n state with
  | pure output => simp [simulateQ_pure]
  | query_bind query rest ih =>
      rw [OracleComp.isTotalQueryBound_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind]
      have hrest : ∀ result ∈ support ((impl query).run state),
          ((simulateQ impl (rest result.1)).run result.2).IsQueryBoundP q
            ((n - 1) * step) := by
        intro result _
        exact ih result.1 (hbound.2 result.1) result.2
      have hbind := OracleComp.isQueryBoundP_bind
        (hstep query state) hrest
      refine hbind.mono ?_
      rw [Nat.sub_one_mul,
        Nat.add_sub_cancel' (Nat.le_mul_of_pos_left step hbound.1)]

theorem ctxRetainedBaseReductionImpl_uniform_query_bound_step
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState) :
    ((ctxRetainedBaseReductionImpl query).run state).IsQueryBoundP
      IsModifiedNonceAeadUniformQuery 64 := by
  rcases query with publicQuery | sealInput
  · exact ctxRetainedBasePublicOracle_uniform_query_bound publicQuery state
  · exact ctxRetainedBaseSealOracle_uniform_query_bound sealInput state

theorem ctxRetainedBaseReduction_uniform_query_bound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxRetainedBaseReduction adversary.toCtxAdversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64) := by
  unfold ctxRetainedBaseReduction
  simp only [bind_pure_comp]
  rw [OracleComp.isQueryBoundP_map_iff]
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step_le_total
    adversary.totalQueryBound
    ctxRetainedBaseReductionImpl_uniform_query_bound_step
    emptyCtxIndependentTagState

theorem isTotalQueryBound_of_modified_uniform_and_seal_bounds
    {alpha : Type} {oa : OracleComp ModifiedNonceAeadAdversarySpec alpha}
    {qR qE : ℕ}
    (huniform : oa.IsQueryBoundP IsModifiedNonceAeadUniformQuery qR)
    (hseal : oa.IsQueryBoundP IsModifiedNonceAeadSealQuery qE) :
    oa.IsTotalQueryBound (qR + qE) := by
  induction oa using OracleComp.inductionOn generalizing qR qE with
  | pure output => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at huniform hseal
      rw [OracleComp.isTotalQueryBound_query_bind_iff]
      rcases query with randomQuery | sealInput
      · simp [IsModifiedNonceAeadUniformQuery,
          IsModifiedNonceAeadSealQuery] at huniform hseal
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform.2 response) (hseal response)).mono
          (by omega)
      · simp [IsModifiedNonceAeadUniformQuery,
          IsModifiedNonceAeadSealQuery] at huniform hseal
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform response) (hseal.2 response)).mono
          (by omega)

theorem ctxRetainedBaseReduction_total_query_bound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxRetainedBaseReduction adversary.toCtxAdversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE) := by
  have huniform := ctxRetainedBaseReduction_uniform_query_bound adversary
  have hseal :
      (ctxRetainedBaseReduction adversary.toCtxAdversary).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery qE :=
    ctxRetainedBaseReduction_seal_query_bound
      adversary.toCtxAdversary qE adversary.sealQueryBound
  have htotal := isTotalQueryBound_of_modified_uniform_and_seal_bounds
    huniform hseal
  exact htotal.mono (by omega)

theorem ctxPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64) := by
  unfold ctxPrefixToModifiedNonceAeadINDDollarReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step_le_total
    adversary.totalQueryBound
    ctxRetainedBaseReductionImpl_uniform_query_bound_step
    emptyCtxIndependentTagState

theorem ctxPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE) := by
  have huniform :=
    ctxPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound adversary
  have hseal :
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery qE :=
    ctxPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound adversary
  have htotal := isTotalQueryBound_of_modified_uniform_and_seal_bounds
    huniform hseal
  exact htotal.mono (by omega)

/-- The conventional validation reduction uses the same private 64-byte samples as the source simulation. -/
theorem ctxPrefixToBooleanINDDollarReduction_uniform_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64) := by
  unfold ctxPrefixToBooleanINDDollarReduction
  refine OracleComp.isQueryBoundP_bind
    (n := (qH + qE) * 64) (m := 0) ?_ ?_
  · exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step_le_total
      adversary.totalQueryBound
      ctxRetainedBaseReductionImpl_uniform_query_bound_step
      emptyCtxIndependentTagState
  · intro result _
    simp only
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (queryModifiedNonceAeadSeal_no_uniform_queries
        (ctxValidationInput (chooseFreshCtxNonce result.2.usedNonces)))
      (fun _ _ => by trivial)

/-- Including the one validation encryption, the conventional reduction has `64qH + 65qE + 1` total primitive-interface calls. -/
theorem ctxPrefixToBooleanINDDollarReduction_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE + 1) := by
  have htotal := isTotalQueryBound_of_modified_uniform_and_seal_bounds
    (ctxPrefixToBooleanINDDollarReduction_uniform_query_bound c adversary)
    (ctxPrefixToBooleanINDDollarReduction_seal_query_bound c adversary)
  exact htotal.mono (by omega)

theorem modifiedNonceAeadINTCTXTImpl_total_query_bound_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ModifiedNonceAeadAdversarySpec.Domain)
    (state : ModifiedNonceAeadHandlerState) :
    ((modifiedNonceAeadINTCTXTImpl c key query).run state).IsTotalQueryBound 1 := by
  rcases query with randomQuery | sealInput
  · unfold modifiedNonceAeadINTCTXTImpl
    simp only [QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      QueryImpl.ofLift_apply]
    exact (show IsTotalQueryBound
      (liftM (unifSpec.query randomQuery) : ProbComp (Fin (randomQuery + 1))) 1 by
        unfold IsTotalQueryBound
        rw [OracleComp.isQueryBound_query_iff]
        omega)
  · unfold modifiedNonceAeadINTCTXTImpl
    simp only [QueryImpl.add_apply_inr]
    unfold modifiedNonceAeadSealOracle
    simp only [StateT.run]
    split <;> trivial

theorem modifiedNonceAeadINTCTXTImpl_uniform_to_total_query_bound_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ModifiedNonceAeadAdversarySpec.Domain)
    (state : ModifiedNonceAeadHandlerState) :
    ((modifiedNonceAeadINTCTXTImpl c key query).run state).IsQueryBoundP
      (fun _ : ℕ => True)
      (if IsModifiedNonceAeadUniformQuery query then 1 else 0) := by
  rcases query with randomQuery | sealInput
  · simp only [IsModifiedNonceAeadUniformQuery, if_true]
    exact (OracleComp.isQueryBoundP_true_iff _ _).2
      (modifiedNonceAeadINTCTXTImpl_total_query_bound_step
        c key (.inl randomQuery) state)
  · simp only [IsModifiedNonceAeadUniformQuery, if_false]
    apply (OracleComp.isQueryBoundP_true_iff _ _).2
    unfold modifiedNonceAeadINTCTXTImpl
    simp only [QueryImpl.add_apply_inr]
    unfold modifiedNonceAeadSealOracle
    simp only [StateT.run]
    split <;> trivial

theorem modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound
    {alpha : Type} (c : Pqxdh.Crypto) (key : CtxKey)
    (oa : OracleComp ModifiedNonceAeadAdversarySpec alpha)
    (n : ℕ)
    (hbound : oa.IsQueryBoundP IsModifiedNonceAeadUniformQuery n) :
    ((simulateQ (modifiedNonceAeadINTCTXTImpl c key) oa).run
      emptyModifiedNonceAeadHandlerState).IsTotalQueryBound n := by
  apply (OracleComp.isQueryBoundP_true_iff _ _).1
  exact hbound.simulateQ_run_StateT_of_step
    (modifiedNonceAeadINTCTXTImpl_uniform_to_total_query_bound_step c key)
    emptyModifiedNonceAeadHandlerState

theorem modifiedNonceAeadINTCTXTBeforeVerifyInner_total_query_bound
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary)
    (key : CtxKey) (n : ℕ)
    (hbound : adversary.main.IsTotalQueryBound n) :
    (modifiedNonceAeadINTCTXTBeforeVerifyInner c adversary key).IsTotalQueryBound n := by
  unfold modifiedNonceAeadINTCTXTBeforeVerifyInner
  have hrun := hbound.simulateQ_run_of_step
    (modifiedNonceAeadINTCTXTImpl_total_query_bound_step c key)
    emptyModifiedNonceAeadHandlerState
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := n) (n₂ := 0)
    hrun (fun result => show IsTotalQueryBound
      (pure ⟨key, result.1, result.2.successfulSeals,
        result.2.usedNonces⟩ : ProbComp ModifiedNonceAeadBeforeVerify) 0 from trivial)

theorem modifiedNonceAeadINTCTXTBeforeVerifyInner_total_of_uniform_query_bound
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary)
    (key : CtxKey) (n : ℕ)
    (hbound : adversary.main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery n) :
    (modifiedNonceAeadINTCTXTBeforeVerifyInner c adversary key).IsTotalQueryBound n := by
  unfold modifiedNonceAeadINTCTXTBeforeVerifyInner
  have hrun := modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound
    c key adversary.main n hbound
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := n) (n₂ := 0)
    hrun (fun result => show IsTotalQueryBound
      (pure ⟨key, result.1, result.2.successfulSeals,
        result.2.usedNonces⟩ : ProbComp ModifiedNonceAeadBeforeVerify) 0 from trivial)

theorem modifiedNonceAeadINTCTXTGame_total_query_bound
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary)
    (n : ℕ) (hbound : adversary.main.IsTotalQueryBound n) :
    (modifiedNonceAeadINTCTXTGame c adversary).IsTotalQueryBound (32 + n) := by
  unfold modifiedNonceAeadINTCTXTGame
  exact OracleComp.isTotalQueryBound_bind
    (uniformFixedBytes_isTotalQueryBound 32)
    (fun key => modifiedNonceAeadINTCTXTBeforeVerifyInner_total_query_bound
      c adversary key n hbound)

theorem modifiedNonceAeadINTCTXTGame_total_of_uniform_query_bound
    (c : Pqxdh.Crypto) (adversary : ModifiedNonceAeadAdversary)
    (n : ℕ) (hbound : adversary.main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery n) :
    (modifiedNonceAeadINTCTXTGame c adversary).IsTotalQueryBound (32 + n) := by
  unfold modifiedNonceAeadINTCTXTGame
  exact OracleComp.isTotalQueryBound_bind
    (uniformFixedBytes_isTotalQueryBound 32)
    (fun key =>
      modifiedNonceAeadINTCTXTBeforeVerifyInner_total_of_uniform_query_bound
        c adversary key n hbound)

theorem modifiedNonceAeadINTCTXTGame_retainedReduction_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (modifiedNonceAeadINTCTXTGame c
      (ctxRetainedBaseReduction adversary.toCtxAdversary)).IsTotalQueryBound
        (32 + (64 * qH + 65 * qE)) := by
  exact modifiedNonceAeadINTCTXTGame_total_query_bound c _ _
    (ctxRetainedBaseReduction_total_query_bound adversary)

theorem modifiedNonceAeadINTCTXTGame_retainedReduction_uniform_draw_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (modifiedNonceAeadINTCTXTGame c
      (ctxRetainedBaseReduction adversary.toCtxAdversary)).IsTotalQueryBound
        (32 + (qH + qE) * 64) := by
  exact modifiedNonceAeadINTCTXTGame_total_of_uniform_query_bound c _ _
    (ctxRetainedBaseReduction_uniform_query_bound adversary)

theorem modifiedNonceAeadINDDollarRealProbeExp_total_query_bound
    (c : Pqxdh.Crypto) {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH)
    (n : ℕ) (hbound : adversary.main.IsTotalQueryBound n) :
    (modifiedNonceAeadINDDollarRealProbeExp c adversary).IsTotalQueryBound
      (32 + n) := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExp
  refine OracleComp.isTotalQueryBound_bind
    (uniformFixedBytes_isTotalQueryBound 32) (fun key => ?_)
  have hrun := hbound.simulateQ_run_of_step
    (modifiedNonceAeadINTCTXTImpl_total_query_bound_step c key)
    emptyModifiedNonceAeadHandlerState
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := n) (n₂ := 0)
    hrun (fun result => show IsTotalQueryBound
      (pure (decide (CtxKeyProbeHit key result.1)) : ProbComp Bool) 0 from trivial)

theorem modifiedNonceAeadINDDollarRealProbeExp_total_of_uniform_query_bound
    (c : Pqxdh.Crypto) {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH)
    (n : ℕ) (hbound : adversary.main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery n) :
    (modifiedNonceAeadINDDollarRealProbeExp c adversary).IsTotalQueryBound
      (32 + n) := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExp
  refine OracleComp.isTotalQueryBound_bind
    (uniformFixedBytes_isTotalQueryBound 32) (fun key => ?_)
  have hrun := modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound
    c key adversary.main n hbound
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := n) (n₂ := 0)
    hrun (fun result => show IsTotalQueryBound
      (pure (decide (CtxKeyProbeHit key result.1)) : ProbComp Bool) 0 from trivial)

theorem modifiedNonceAeadINDDollarRealProbeExp_prefixReduction_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (modifiedNonceAeadINDDollarRealProbeExp c
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)).IsTotalQueryBound
        (32 + (64 * qH + 65 * qE)) := by
  exact modifiedNonceAeadINDDollarRealProbeExp_total_query_bound c _ _
    (ctxPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound adversary)

theorem modifiedNonceAeadINDDollarRealProbeExp_prefixReduction_uniform_draw_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (modifiedNonceAeadINDDollarRealProbeExp c
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)).IsTotalQueryBound
        (32 + (qH + qE) * 64) := by
  exact modifiedNonceAeadINDDollarRealProbeExp_total_of_uniform_query_bound c _ _
    (ctxPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound adversary)

/-- One direct honest CTX seal draws at most its 64-byte outer commitment. -/
theorem ctxDirectSampleKeyFreeSealOracle_total_query_bound
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState) :
    ((ctxDirectSampleKeyFreeSealOracle c key input).run state).IsTotalQueryBound
      64 := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle
    simp only [StateT.run, hused, if_true]
    trivial
  · unfold ctxDirectSampleKeyFreeSealOracle
    simp only [StateT.run, hused, if_false]
    simpa using OracleComp.isTotalQueryBound_bind (n₁ := 64) (n₂ := 0)
      (uniformFixedBytes_isTotalQueryBound 64)
      (fun commit => show IsTotalQueryBound
        (pure (some
          (⟨(c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
              input.plaintext).1,
            (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
              input.plaintext).2,
            c.aeadSeal_tag_length _ _ _ _, commit⟩ : CtxRomRecord),
          state.addSeal
            ⟨input,
              ⟨(c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                  input.plaintext).1,
                (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                  input.plaintext).2,
                c.aeadSeal_tag_length _ _ _ _, commit⟩⟩
            (cacheSuffix state.cache
              (outerSuffix input.nonce input.context
                (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                  input.plaintext).2) commit)) :
          ProbComp (Option CtxRomRecord × CtxIndependentTagState)) 0 from trivial)

/-- Every direct public or sealing step draws at most one 64-byte digest. -/
theorem ctxDirectSampleIndependentTagImpl_total_query_bound_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState) :
    ((ctxDirectSampleIndependentTagImpl c key query).run state).IsTotalQueryBound
      64 := by
  rcases query with publicQuery | sealInput
  · exact ctxIndependentPublicOracle_total_query_bound publicQuery state
  · exact ctxDirectSampleKeyFreeSealOracle_total_query_bound
      c key sealInput state

/-- A fixed-key direct pre-verification run costs at most 64 byte draws per source query. -/
theorem ctxDirectSampleIndependentTagBeforeVerifyInner_total_query_bound
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxDirectSampleIndependentTagBeforeVerifyInner c
      adversary.toCtxAdversary key).IsTotalQueryBound ((qH + qE) * 64) := by
  unfold ctxDirectSampleIndependentTagBeforeVerifyInner
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  apply (OracleComp.isQueryBoundP_true_iff _ _).1
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step_le_total
    adversary.totalQueryBound
    (fun query state => (OracleComp.isQueryBoundP_true_iff _ _).2
      (ctxDirectSampleIndependentTagImpl_total_query_bound_step
        c key query state))
    emptyCtxIndependentTagState

/-- The direct pre-verification game includes 32 key bytes and 64 bytes per source query. -/
theorem ctxDirectSampleIndependentTagGame_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxDirectSampleIndependentTagGame c
      adversary.toCtxAdversary).IsTotalQueryBound
        (32 + (qH + qE) * 64) := by
  unfold ctxDirectSampleIndependentTagGame
  exact OracleComp.isTotalQueryBound_bind
    (uniformFixedBytes_isTotalQueryBound 32)
    (fun key => ctxDirectSampleIndependentTagBeforeVerifyInner_total_query_bound
      c key adversary)

/-- The private final verifier makes one 64-byte suffix-ROM draw at most. -/
theorem ctxClassifiedVerifier_totalQueryBound
    (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache) :
    (ctxClassifiedVerifier c result).IsTotalQueryBound 64 := by
  unfold ctxClassifiedVerifier
  by_cases hcache : result.2.suffixCache
      (outerSuffix result.1.target.nonce result.1.target.context
        result.1.target.record.tag) = none
  · unfold ctxKeyFreeSuffixStep
    simp only [hcache]
    simp only [bind_assoc, pure_bind]
    rw [bind_pure_comp]
    exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).2
      (uniformFixedBytes_isTotalQueryBound 64)
  · cases hvalue : result.2.suffixCache
        (outerSuffix result.1.target.nonce result.1.target.context
          result.1.target.record.tag) with
    | none => exact (hcache hvalue).elim
    | some digest =>
        unfold ctxKeyFreeSuffixStep
        simp only [hvalue, pure_bind]
        trivial

/-- The typed full-fresh verifier has the same single 64-byte draw bound. -/
theorem ctxTypedFullFreshVerifier_totalQueryBound
    (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache) :
    (ctxTypedFullFreshVerifier c result).IsTotalQueryBound 64 := by
  unfold ctxTypedFullFreshVerifier
  by_cases hcache : result.2.suffixCache
      (outerSuffix result.1.target.nonce result.1.target.context
        result.1.target.record.tag) = none
  · unfold ctxKeyFreeSuffixStep
    simp only [hcache]
    simp only [bind_assoc, pure_bind]
    rw [bind_pure_comp]
    exact (OracleComp.isQueryBound_map_iff _ _ _ _ _).2
      (uniformFixedBytes_isTotalQueryBound 64)
  · cases hvalue : result.2.suffixCache
        (outerSuffix result.1.target.nonce result.1.target.context
          result.1.target.record.tag) with
    | none => exact (hcache hvalue).elim
    | some digest =>
        unfold ctxKeyFreeSuffixStep
        simp only [hvalue, pure_bind]
        trivial

/-- The complete direct classified game costs at most 32 key bytes, 64 bytes per source query, and 64 final-verifier bytes. -/
theorem ctxDirectClassifiedForgeryGame_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxDirectClassifiedForgeryGame c
      adversary.toCtxAdversary).IsTotalQueryBound
        (96 + (qH + qE) * 64) := by
  unfold ctxDirectClassifiedForgeryGame
  have hbound := OracleComp.isTotalQueryBound_bind
    (ctxDirectSampleIndependentTagGame_total_query_bound c adversary)
    (ctxClassifiedVerifier_totalQueryBound c)
  exact hbound.mono (by omega)

/-- The complete direct typed full-fresh game has the same explicit uniform-byte cost. -/
theorem ctxDirectTypedFullFreshForgeryGame_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxDirectTypedFullFreshForgeryGame c
      adversary.toCtxAdversary).IsTotalQueryBound
        (96 + (qH + qE) * 64) := by
  unfold ctxDirectTypedFullFreshForgeryGame
  have hbound := OracleComp.isTotalQueryBound_bind
    (ctxDirectSampleIndependentTagGame_total_query_bound c adversary)
    (ctxTypedFullFreshVerifier_totalQueryBound c)
  exact hbound.mono (by omega)

/-- Complete source, reduction, and final-verifier query accounting. -/
structure CtxComputationalQueryAccounting (c : Pqxdh.Crypto)
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) : Prop where
  sourceTotal : adversary.main.IsTotalQueryBound (qH + qE)
  retainedSeals :
    (ctxRetainedBaseReduction adversary.toCtxAdversary).MakesAtMostSealQueries qE
  retainedUniform :
    (ctxRetainedBaseReduction adversary.toCtxAdversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64)
  retainedTotal :
    (ctxRetainedBaseReduction adversary.toCtxAdversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE)
  retainedGameTotal :
    (modifiedNonceAeadINTCTXTGame c
      (ctxRetainedBaseReduction adversary.toCtxAdversary)).IsTotalQueryBound
        (32 + (64 * qH + 65 * qE))
  retainedGameUniformDraws :
    (modifiedNonceAeadINTCTXTGame c
      (ctxRetainedBaseReduction adversary.toCtxAdversary)).IsTotalQueryBound
        (32 + (qH + qE) * 64)
  prefixSeals :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).MakesAtMostSealQueries qE
  prefixUniform :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64)
  prefixTotal :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE)
  prefixRealProbeTotal :
    (modifiedNonceAeadINDDollarRealProbeExp c
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)).IsTotalQueryBound
        (32 + (64 * qH + 65 * qE))
  prefixRealProbeUniformDraws :
    (modifiedNonceAeadINDDollarRealProbeExp c
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)).IsTotalQueryBound
        (32 + (qH + qE) * 64)
  booleanPrefixSeals :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery (qE + 1)
  booleanPrefixUniform :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64)
  booleanPrefixTotal :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE + 1)
  directClassifiedGame :
    (ctxDirectClassifiedForgeryGame c
      adversary.toCtxAdversary).IsTotalQueryBound
        (96 + (qH + qE) * 64)
  directTypedGame :
    (ctxDirectTypedFullFreshForgeryGame c
      adversary.toCtxAdversary).IsTotalQueryBound
        (96 + (qH + qE) * 64)
  classifiedVerifier : ∀ result,
    (ctxClassifiedVerifier c result).IsTotalQueryBound 64
  typedVerifier : ∀ result,
    (ctxTypedFullFreshVerifier c result).IsTotalQueryBound 64

/-- Every bounded CTX adversary satisfies the explicit composed accounting record. -/
theorem ctxComputationalSecurity_query_accounting
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    CtxComputationalQueryAccounting c adversary where
  sourceTotal := adversary.totalQueryBound
  retainedSeals := ctxRetainedBaseReduction_seal_query_bound
    adversary.toCtxAdversary qE adversary.sealQueryBound
  retainedUniform := ctxRetainedBaseReduction_uniform_query_bound adversary
  retainedTotal := ctxRetainedBaseReduction_total_query_bound adversary
  retainedGameTotal :=
    modifiedNonceAeadINTCTXTGame_retainedReduction_total_query_bound c adversary
  retainedGameUniformDraws :=
    modifiedNonceAeadINTCTXTGame_retainedReduction_uniform_draw_bound c adversary
  prefixSeals :=
    ctxPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound adversary
  prefixUniform :=
    ctxPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound adversary
  prefixTotal :=
    ctxPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound adversary
  prefixRealProbeTotal :=
    modifiedNonceAeadINDDollarRealProbeExp_prefixReduction_total_query_bound
      c adversary
  prefixRealProbeUniformDraws :=
    modifiedNonceAeadINDDollarRealProbeExp_prefixReduction_uniform_draw_bound
      c adversary
  booleanPrefixSeals :=
    ctxPrefixToBooleanINDDollarReduction_seal_query_bound c adversary
  booleanPrefixUniform :=
    ctxPrefixToBooleanINDDollarReduction_uniform_query_bound c adversary
  booleanPrefixTotal :=
    ctxPrefixToBooleanINDDollarReduction_total_query_bound c adversary
  directClassifiedGame :=
    ctxDirectClassifiedForgeryGame_total_query_bound c adversary
  directTypedGame :=
    ctxDirectTypedFullFreshForgeryGame_total_query_bound c adversary
  classifiedVerifier := ctxClassifiedVerifier_totalQueryBound c
  typedVerifier := ctxTypedFullFreshVerifier_totalQueryBound c

end BeaconcryptCore.Computational.CtxComputationalSecurity
