import BeaconcryptCore.Computational.CtxIndependentTags

/-!
# Fresh independent honest outer tags for modified CTX

This module proves that nonce uniqueness makes every successful honest suffix query fresh in the key-free independent-tag game.
The lazy suffix-ROM sealing transition is therefore exactly equal to one direct uniform digest sample per successful seal, with reused nonces rejected before sampling.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxHonestTagSampling

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags

/-- The first 12 bytes of every honest suffix are exactly its nonce. -/
@[simp] theorem outerSuffix_take_nonce
    (nonce : CtxNonce) (context : CtxRecordContext) (tag : Pqxdh.Bytes) :
    (outerSuffix nonce context tag).take 12 = nonce.toList := by
  simp [outerSuffix]

/-- Equal honest suffixes necessarily carry equal nonces. -/
theorem outerSuffix_eq_implies_nonce_eq
    (n₁ n₂ : CtxNonce) (x₁ x₂ : CtxRecordContext)
    (t₁ t₂ : Pqxdh.Bytes)
    (h : outerSuffix n₁ x₁ t₁ = outerSuffix n₂ x₂ t₂) :
    n₁ = n₂ := by
  apply List.Vector.toList_injective
  have htake := congrArg (List.take 12) h
  simpa using htake

/-- Every successful seal's nonce appears in the rejection history. -/
def CtxIndependentTagStateSealsMarkedUsed
    (state : CtxIndependentTagState) : Prop :=
  ∀ entry ∈ state.successfulSeals, entry.input.nonce ∈ state.usedNonces

/-- Distinct successful seals have distinct nonces. -/
def CtxIndependentTagStateUniqueSealNonces
    (state : CtxIndependentTagState) : Prop :=
  ∀ left ∈ state.successfulSeals, ∀ right ∈ state.successfulSeals,
    left.input.nonce = right.input.nonce → left = right

/-- Every suffix-cache entry originated at an exact successful honest suffix. -/
def CtxIndependentTagStateSuffixCacheProvenance
    (state : CtxIndependentTagState) : Prop :=
  ∀ suffix, state.cache.suffixCache suffix ≠ none →
    ∃ entry ∈ state.successfulSeals,
      suffix = outerSuffix entry.input.nonce entry.input.context
        entry.record.tag

/-- Reachable independent-tag states retain nonce and suffix provenance. -/
def CtxIndependentTagStateInvariant
    (state : CtxIndependentTagState) : Prop :=
  CtxIndependentTagStateSealsMarkedUsed state ∧
    CtxIndependentTagStateUniqueSealNonces state ∧
    CtxIndependentTagStateSuffixCacheProvenance state

/-- The empty split handler satisfies the complete suffix invariant. -/
@[simp] theorem emptyCtxIndependentTagState_invariant :
    CtxIndependentTagStateInvariant emptyCtxIndependentTagState := by
  simp [CtxIndependentTagStateInvariant,
    CtxIndependentTagStateSealsMarkedUsed,
    CtxIndependentTagStateUniqueSealNonces,
    CtxIndependentTagStateSuffixCacheProvenance,
    emptyCtxIndependentTagState]

/-- An unused nonce cannot address any suffix already installed by an honest seal. -/
theorem outerSuffix_fresh_of_unused
    (state : CtxIndependentTagState) (nonce : CtxNonce)
    (context : CtxRecordContext) (tag : Pqxdh.Bytes)
    (hinvariant : CtxIndependentTagStateInvariant state)
    (hunused : nonce ∉ state.usedNonces) :
    state.cache.suffixCache (outerSuffix nonce context tag) = none := by
  by_contra hhit
  obtain ⟨entry, hentry, hsuffix⟩ := hinvariant.2.2 _ hhit
  have hnonce : nonce = entry.input.nonce :=
    outerSuffix_eq_implies_nonce_eq nonce entry.input.nonce context
      entry.input.context tag entry.record.tag hsuffix
  apply hunused
  rw [hnonce]
  exact hinvariant.1 entry hentry

/-- Every nonce-respecting key-free sealing suffix is fresh. -/
theorem ctxKeyFreeSeal_suffix_fresh_of_unused
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state)
    (hunused : input.nonce ∉ state.usedNonces) :
    state.cache.suffixCache
      (outerSuffix input.nonce input.context
        (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
          input.plaintext).2) = none := by
  exact outerSuffix_fresh_of_unused state input.nonce input.context _
    hinvariant hunused

/-- Successful key-free sealing with an explicit independent uniform digest sample. -/
noncomputable def ctxDirectSampleKeyFreeSealOracle
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxSealSpec (StateT CtxIndependentTagState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let base := c.aeadSeal key.toList input.nonce.toList
        input.context.ad.bytes input.plaintext
      let suffix := outerSuffix input.nonce input.context base.2
      let commit ← $ᵗ CtxDigest
      let cache := cacheSuffix state.cache suffix commit
      let record : CtxRomRecord :=
        ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- On every invariant state, lazy honest suffix lookup is exactly direct sampling. -/
theorem ctxKeyFreeSealOracle_eq_directSample_of_invariant
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state) :
    (ctxKeyFreeSealOracle c key input).run state =
      (ctxDirectSampleKeyFreeSealOracle c key input).run state := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · change (if input.nonce ∈ state.usedNonces then pure (none, state) else _) =
      (if input.nonce ∈ state.usedNonces then pure (none, state) else _)
    rw [if_pos hused, if_pos hused]
  · have hfresh := ctxKeyFreeSeal_suffix_fresh_of_unused
      c key input state hinvariant hused
    unfold ctxKeyFreeSealOracle ctxDirectSampleKeyFreeSealOracle
    simp only [StateT.run, hused, if_false]
    unfold ctxKeyFreeSuffixOracle ctxKeyFreeSuffixStep
    rw [hfresh]
    simp

/-- A suffix-cache hit after installation was old or is the installed address. -/
theorem cacheSuffix_origin (cache : SplitCache) (suffix : Pqxdh.Bytes)
    (digest : CtxDigest) (candidate : Pqxdh.Bytes)
    (hhit : (cacheSuffix cache suffix digest).suffixCache candidate ≠ none) :
    cache.suffixCache candidate ≠ none ∨ candidate = suffix := by
  by_cases heq : candidate = suffix
  · exact Or.inr heq
  · exact Or.inl (by
      simpa [cacheSuffix,
        QueryCache.cacheQuery_of_ne cache.suffixCache digest heq] using hhit)

/-- Public independent-ROM queries preserve every honest-suffix invariant. -/
theorem ctxIndependentPublicOracle_preserves_invariant
    (query : CtxRO.Domain) (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state)
    (result : CtxDigest × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxIndependentPublicOracle query).run state)) :
    CtxIndependentTagStateInvariant result.2 := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache.publicCache >>=
      fun oracleResult =>
        let cache := { state.cache with publicCache := oracleResult.2 }
        pure (oracleResult.1, state.addPublic query.2 cache)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rcases hinvariant with ⟨hmarked, hunique, hprovenance⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [CtxIndependentTagStateSealsMarkedUsed,
      CtxIndependentTagState.addPublic] using hmarked
  · simpa [CtxIndependentTagStateUniqueSealNonces,
      CtxIndependentTagState.addPublic] using hunique
  · simpa [CtxIndependentTagStateSuffixCacheProvenance,
      CtxIndependentTagState.addPublic] using hprovenance

/-- Directly sampled sealing preserves nonce uniqueness and suffix provenance. -/
theorem ctxDirectSampleKeyFreeSealOracle_preserves_invariant
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleKeyFreeSealOracle c key input).run state)) :
    CtxIndependentTagStateInvariant result.2 := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    exact hinvariant
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
    rcases hinvariant with ⟨hmarked, hunique, hprovenance⟩
    refine ⟨?_, ?_, ?_⟩
    · intro entry hentry
      simp only [CtxIndependentTagState.addSeal, List.mem_cons] at hentry ⊢
      rcases hentry with hnew | hold
      · subst entry
        exact Or.inl rfl
      · exact Or.inr (hmarked entry hold)
    · intro left hleft right hright hnonce
      simp only [CtxIndependentTagState.addSeal, List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright
      · simp [hleft, hright]
      · subst left
        exfalso
        apply hused
        rw [hnonce]
        exact hmarked right hright
      · subst right
        exfalso
        apply hused
        rw [← hnonce]
        exact hmarked left hleft
      · exact hunique left hleft right hright hnonce
    · intro candidate hhit
      rcases cacheSuffix_origin state.cache suffix commit candidate hhit with
        hold | hnew
      · obtain ⟨entry, hentry, heq⟩ := hprovenance candidate hold
        exact ⟨entry, by
          simpa only [CtxIndependentTagState.addSeal, List.mem_cons] using
            Or.inr hentry,
          heq⟩
      · refine ⟨⟨input, record⟩, ?_, ?_⟩
        · exact List.Mem.head _
        · simpa [record, suffix, base] using hnew

/-- Independent public ROM access plus direct independent honest-tag sampling. -/
noncomputable def ctxDirectSampleIndependentTagImpl
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT CtxIndependentTagState ProbComp) :=
  ctxIndependentPublicOracle + ctxDirectSampleKeyFreeSealOracle c key

/-- The direct independent-tag handler preserves the complete split invariant. -/
theorem ctxDirectSampleIndependentTagImpl_preserves_invariant
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (ctxDirectSampleIndependentTagImpl c key)
      CtxIndependentTagStateInvariant := by
  intro query state hinvariant result hresult
  rcases query with query | input
  · exact ctxIndependentPublicOracle_preserves_invariant query state
      hinvariant result hresult
  · exact ctxDirectSampleKeyFreeSealOracle_preserves_invariant
      c key input state hinvariant result hresult

/-- Every invariant query step is unchanged by exposing the honest sample directly. -/
theorem ctxIndependentTagImpl_eq_directSample_step_of_invariant
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState)
    (hinvariant : CtxIndependentTagStateInvariant state) :
    (ctxIndependentTagImpl c key query).run state =
      (ctxDirectSampleIndependentTagImpl c key query).run state := by
  rcases query with query | input
  · rfl
  · exact ctxKeyFreeSealOracle_eq_directSample_of_invariant
      c key input state hinvariant

/-- Every reachable direct-sampling transcript retains nonce uniqueness and provenance. -/
theorem ctxDirectSampleIndependentTag_run_invariant_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α)
    (result : α × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key) main).run
        emptyCtxIndependentTagState)) :
    CtxIndependentTagStateInvariant result.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (ctxDirectSampleIndependentTagImpl c key)
    CtxIndependentTagStateInvariant
    (ctxDirectSampleIndependentTagImpl_preserves_invariant c key)
    main emptyCtxIndependentTagState
    emptyCtxIndependentTagState_invariant result hresult

/-- Every reachable direct-sampling adversary transcript retains nonce uniqueness and provenance. -/
theorem ctxDirectSampleIndependentTag_run_invariant
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    CtxIndependentTagStateInvariant result.2 := by
  exact ctxDirectSampleIndependentTag_run_invariant_of_main
    c key adversary.main result hresult

/-- Adaptive lazy-suffix and direct independent-sampling runs are exactly equal for any output. -/
theorem ctxIndependentTagImpl_run_eq_directSample_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    (simulateQ (ctxIndependentTagImpl c key) main).run
        emptyCtxIndependentTagState =
      (simulateQ (ctxDirectSampleIndependentTagImpl c key) main).run
        emptyCtxIndependentTagState := by
  simpa using (OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (ctxDirectSampleIndependentTagImpl c key)
    (ctxIndependentTagImpl c key)
    CtxIndependentTagStateInvariant id
    (ctxDirectSampleIndependentTagImpl_preserves_invariant c key)
    (fun query state hinvariant => by
      rw [← ctxIndependentTagImpl_eq_directSample_step_of_invariant
        c key query state hinvariant]
      simp)
    main emptyCtxIndependentTagState
    emptyCtxIndependentTagState_invariant).symm

/-- Adaptive lazy-suffix and direct independent-sampling adversary runs are exactly equal. -/
theorem ctxIndependentTagImpl_run_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    (simulateQ (ctxIndependentTagImpl c key) adversary.main).run
        emptyCtxIndependentTagState =
      (simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState := by
  exact ctxIndependentTagImpl_run_eq_directSample_of_main
    c key adversary.main

/-- Reachable successful direct-sampling seals have pairwise-unique nonces. -/
theorem ctxDirectSampleIndependentTag_run_unique_seal_nonces
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    CtxIndependentTagStateUniqueSealNonces result.2 :=
  (ctxDirectSampleIndependentTag_run_invariant
    c key adversary result hresult).2.1

/-- Fixed-key direct independent-sampling game on the common split-cache surface. -/
noncomputable def ctxDirectSampleIndependentTagBeforeVerifyInner
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × SplitCache) :=
  independentTrackedProjection key <$>
    (simulateQ (ctxDirectSampleIndependentTagImpl c key)
      adversary.main).run emptyCtxIndependentTagState

/-- Exposing fresh honest samples leaves the fixed-key independent-tag game unchanged. -/
theorem ctxIndependentTagBeforeVerifyInner_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ctxIndependentTagBeforeVerifyInner c adversary key =
      ctxDirectSampleIndependentTagBeforeVerifyInner c adversary key := by
  unfold ctxIndependentTagBeforeVerifyInner
    ctxDirectSampleIndependentTagBeforeVerifyInner
  rw [ctxIndependentTagImpl_run_eq_directSample]

/-- Uniform-key game with one explicit independent digest sample per successful seal. -/
noncomputable def ctxDirectSampleIndependentTagGame
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × SplitCache) := do
  let key ← $ᵗ CtxKey
  ctxDirectSampleIndependentTagBeforeVerifyInner c adversary key

/-- Lazy suffix-ROM and explicit independent-sampling games are exactly equal. -/
theorem ctxIndependentTagGame_eq_directSampleIndependentTagGame
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    ctxIndependentTagGame c adversary =
      ctxDirectSampleIndependentTagGame c adversary := by
  unfold ctxIndependentTagGame ctxDirectSampleIndependentTagGame
  apply bind_congr
  intro key
  exact ctxIndependentTagBeforeVerifyInner_eq_directSample
    c key adversary

/-- Canonical split tags differ from explicit independent samples only on prefix-bad. -/
theorem tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    tvDist (ctxSplitBeforeVerifyGame c adversary)
        (ctxDirectSampleIndependentTagGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
  rw [← ctxIndependentTagGame_eq_directSampleIndependentTagGame]
  exact tvDist_ctxSplitBeforeVerifyGame_independentTagGame_le_secretPrefixQueried
    c adversary

end BeaconcryptCore.Computational.CtxHonestTagSampling
