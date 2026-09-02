import BeaconcryptCore.Computational.CtxSealSampling
import BeaconcryptCore.Computational.CtxSplitCache

/-!
# Key-free independent outer tags for modified CTX

This module projects the prefix-isolated modified-CTX handler onto a split random-oracle state.
Public non-prefix queries retain their complete inputs, while honest outer tags use only the key-free suffix `N ‖ AD ‖ T ‖ LE64(seq) ‖ LE64(sid)`.
The projection is exact after prefix isolation, so the real-to-independent-tag hop charges the public secret-prefix event exactly once.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxIndependentTags

open CtxRomAuth CtxPrefixIsolation CtxSealSampling CtxSplitCache

/-- The handler state after replacing the canonical ROM cache by its split representation. -/
structure CtxIndependentTagState where
  cache : SplitCache
  usedNonces : List CtxNonce
  successfulSeals : List CtxSuccessfulSeal
  publicInputs : List Pqxdh.Bytes

/-- Project the canonical handler state into public-input and key-free suffix caches. -/
def splitHandlerState (key : CtxKey) (state : CtxHandlerState) :
    CtxIndependentTagState :=
  ⟨splitCtxCache key state.cache, state.usedNonces, state.successfulSeals,
    state.publicInputs⟩

/-- Merge a split handler state back into the canonical handler representation. -/
def CtxIndependentTagState.merge (key : CtxKey)
    (state : CtxIndependentTagState) : CtxHandlerState :=
  ⟨state.cache.merge key, state.usedNonces, state.successfulSeals,
    state.publicInputs⟩

/-- The split handler starts with two empty caches and empty histories. -/
def emptyCtxIndependentTagState : CtxIndependentTagState :=
  ⟨⟨∅, ∅⟩, [], [], []⟩

/-- Project a flagged canonical state without changing its bad flag. -/
def splitFlaggedHandlerState (key : CtxKey)
    (state : CtxHandlerState × Bool) : CtxIndependentTagState × Bool :=
  (splitHandlerState key state.1, state.2)

/-- Merging a projected canonical handler state recovers that state exactly. -/
@[simp] theorem merge_splitHandlerState (key : CtxKey)
    (state : CtxHandlerState) :
    (splitHandlerState key state).merge key = state := by
  cases state
  simp [splitHandlerState, CtxIndependentTagState.merge, merge_splitCtxCache]

/-- The empty canonical handler projects to the empty split handler. -/
@[simp] theorem splitHandlerState_empty (key : CtxKey) :
    splitHandlerState key emptyCtxHandlerState = emptyCtxIndependentTagState := by
  simp [splitHandlerState, emptyCtxHandlerState, emptyCtxIndependentTagState]

/-- Install an answer at one complete public input. -/
def cachePublic (cache : SplitCache) (query : CtxRO.Domain)
    (digest : CtxDigest) : SplitCache :=
  { cache with publicCache := cache.publicCache.cacheQuery query digest }

/-- Install an answer at one key-free secret-prefix suffix. -/
def cacheSuffix (cache : SplitCache) (suffix : Pqxdh.Bytes)
    (digest : CtxDigest) : SplitCache :=
  { cache with suffixCache := cache.suffixCache.cacheQuery suffix digest }

/-- Projecting a canonical hidden-prefix cache update changes only the suffix cache. -/
theorem splitCtxCache_cacheQuery_prefix (key : CtxKey)
    (cache : CtxRO.QueryCache) (query : CtxRO.Domain) (digest : CtxDigest)
    (hprefix : SecretPrefixQuery key query.2) :
    splitCtxCache key (cache.cacheQuery query digest) =
      cacheSuffix (splitCtxCache key cache) (secretSuffix query.2) digest := by
  rcases query with ⟨⟨⟩, input⟩
  apply SplitCache.ext
  · funext candidate
    simp only [splitCtxCache, cacheSuffix]
    by_cases hcand : SecretPrefixQuery key candidate.2
    · simp [hcand]
    · have hne : candidate ≠ ((), input) := by
        intro heq
        apply hcand
        simpa [heq] using hprefix
      simp [hcand, QueryCache.cacheQuery_of_ne cache digest hne]
  · funext suffix
    simp only [splitCtxCache, cacheSuffix]
    by_cases heq : suffix = secretSuffix input
    · subst suffix
      rw [secretAddress_secretSuffix key input hprefix]
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · have haddr : ((), secretAddress key suffix) ≠ ((), input) := by
        intro h
        apply heq
        have hinput : secretAddress key suffix = input := congrArg Prod.snd h
        rw [← hinput, secretSuffix_secretAddress]
      rw [QueryCache.cacheQuery_of_ne cache digest haddr,
        QueryCache.cacheQuery_of_ne (spec := CtxSuffixRO)
          (fun suffix => cache ((), secretAddress key suffix)) digest heq]

/-- Projecting a canonical non-prefix cache update changes only the public cache. -/
theorem splitCtxCache_cacheQuery_public (key : CtxKey)
    (cache : CtxRO.QueryCache) (query : CtxRO.Domain) (digest : CtxDigest)
    (hpublic : ¬SecretPrefixQuery key query.2) :
    splitCtxCache key (cache.cacheQuery query digest) =
      cachePublic (splitCtxCache key cache) query digest := by
  rcases query with ⟨⟨⟩, input⟩
  apply SplitCache.ext
  · funext candidate
    simp only [splitCtxCache, cachePublic]
    by_cases heq : candidate = ((), input)
    · subst candidate
      simp [hpublic]
    · by_cases hcand : SecretPrefixQuery key candidate.2
      · simp [hcand, QueryCache.cacheQuery_of_ne _ _ heq]
      · simp [hcand, QueryCache.cacheQuery_of_ne _ _ heq]
  · funext suffix
    simp only [splitCtxCache, cachePublic]
    have haddr : ((), secretAddress key suffix) ≠ ((), input) := by
      intro h
      apply hpublic
      have hinput : secretAddress key suffix = input := congrArg Prod.snd h
      simp [← hinput]
    rw [QueryCache.cacheQuery_of_ne cache digest haddr]

/-- Route one canonical query to the public or key-free suffix component. -/
def cacheCanonical (key : CtxKey) (cache : SplitCache)
    (query : CtxRO.Domain) (digest : CtxDigest) : SplitCache :=
  if SecretPrefixQuery key query.2 then
    cacheSuffix cache (secretSuffix query.2) digest
  else
    cachePublic cache query digest

/-- Canonical cache installation commutes exactly with split-cache projection. -/
theorem splitCtxCache_cacheQuery (key : CtxKey) (cache : CtxRO.QueryCache)
    (query : CtxRO.Domain) (digest : CtxDigest) :
    splitCtxCache key (cache.cacheQuery query digest) =
      cacheCanonical key (splitCtxCache key cache) query digest := by
  by_cases hprefix : SecretPrefixQuery key query.2
  · simp [cacheCanonical, hprefix,
      splitCtxCache_cacheQuery_prefix key cache query digest hprefix]
  · simp [cacheCanonical, hprefix,
      splitCtxCache_cacheQuery_public key cache query digest hprefix]

/-- Record one public query after updating the relevant split cache. -/
def CtxIndependentTagState.addPublic (state : CtxIndependentTagState)
    (input : Pqxdh.Bytes) (cache : SplitCache) : CtxIndependentTagState :=
  { state with cache := cache, publicInputs := input :: state.publicInputs }

/-- Record one successful seal after installing its independently sampled outer tag. -/
def CtxIndependentTagState.addSeal (state : CtxIndependentTagState)
    (entry : CtxSuccessfulSeal) (cache : SplitCache) : CtxIndependentTagState :=
  { state with
    cache := cache
    usedNonces := entry.input.nonce :: state.usedNonces
    successfulSeals := entry :: state.successfulSeals }

/-- Public-history updates commute with handler-state projection. -/
@[simp] theorem splitHandlerState_addPublic (key : CtxKey)
    (state : CtxHandlerState) (input : Pqxdh.Bytes)
    (cache : CtxRO.QueryCache) :
    splitHandlerState key (state.addPublic input cache) =
      (splitHandlerState key state).addPublic input (splitCtxCache key cache) := by
  rfl

/-- Successful-seal updates commute with handler-state projection. -/
@[simp] theorem splitHandlerState_addSeal (key : CtxKey)
    (state : CtxHandlerState) (entry : CtxSuccessfulSeal)
    (cache : CtxRO.QueryCache) :
    splitHandlerState key (state.addSeal entry cache) =
      (splitHandlerState key state).addSeal entry (splitCtxCache key cache) := by
  rfl

/-- Lazy random function on key-free CTX suffixes. -/
@[inline, reducible] noncomputable def ctxSuffixRandomOracle :
    QueryImpl CtxSuffixRO (StateT CtxSuffixRO.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

/-- One lazy suffix-ROM step that updates only the suffix component. -/
noncomputable def ctxKeyFreeSuffixStep (suffix : Pqxdh.Bytes)
    (cache : SplitCache) : ProbComp (CtxDigest × SplitCache) :=
  match cache.suffixCache suffix with
  | some digest => pure (digest, cache)
  | none => do
      let digest ← $ᵗ CtxDigest
      pure (digest, cacheSuffix cache suffix digest)

/-- The canonical lazy ROM routed through a split cache. -/
noncomputable def ctxSplitRandomOracle (key : CtxKey) :
    QueryImpl CtxRO (StateT SplitCache ProbComp) := fun query cache =>
  if SecretPrefixQuery key query.2 then
    ctxKeyFreeSuffixStep (secretSuffix query.2) cache
  else
    match cache.publicCache query with
    | some digest => pure (digest, cache)
    | none => do
        let digest ← $ᵗ CtxDigest
        pure (digest, cachePublic cache query digest)

/-- One canonical lazy-ROM step commutes exactly with split-cache projection. -/
theorem ctxRandomOracle_split_projection (key : CtxKey)
    (query : CtxRO.Domain) (cache : CtxRO.QueryCache) :
    Prod.map id (splitCtxCache key) <$> (ctxRandomOracle query).run cache =
      (ctxSplitRandomOracle key query).run (splitCtxCache key cache) := by
  rcases query with ⟨⟨⟩, input⟩
  by_cases hprefix : SecretPrefixQuery key input
  · cases hcache : cache ((), input) with
    | none =>
        have hsuffix :
            (splitCtxCache key cache).suffixCache (secretSuffix input) = none := by
          change cache ((), secretAddress key (secretSuffix input)) = none
          rw [secretAddress_secretSuffix key input hprefix]
          exact hcache
        rw [ctxRandomOracle,
          QueryImpl.withCaching_run_none uniformSampleImpl hcache]
        unfold ctxSplitRandomOracle
        unfold ctxKeyFreeSuffixStep
        simp only [StateT.run, hprefix, if_pos]
        rw [hsuffix]
        simp only
        simp only [uniformSampleImpl, Functor.map_map]
        change (fun digest : CtxDigest =>
            (digest, splitCtxCache key (cache.cacheQuery ((), input) digest))) <$>
              ($ᵗ CtxDigest) =
          (fun digest : CtxDigest =>
            (digest, cacheSuffix (splitCtxCache key cache)
              (secretSuffix input) digest)) <$> ($ᵗ CtxDigest)
        apply congrArg (fun f : CtxDigest → CtxDigest × SplitCache =>
          f <$> ($ᵗ CtxDigest))
        funext digest
        congr 1
        exact splitCtxCache_cacheQuery_prefix key cache ((), input) digest hprefix
    | some digest =>
        have hsuffix :
            (splitCtxCache key cache).suffixCache (secretSuffix input) =
              some digest := by
          change cache ((), secretAddress key (secretSuffix input)) = some digest
          rw [secretAddress_secretSuffix key input hprefix]
          exact hcache
        rw [ctxRandomOracle,
          QueryImpl.withCaching_run_some uniformSampleImpl hcache]
        unfold ctxSplitRandomOracle
        unfold ctxKeyFreeSuffixStep
        simp [StateT.run, hprefix, hsuffix]
  · cases hcache : cache ((), input) with
    | none =>
        have hsplit :
            (splitCtxCache key cache).publicCache ((), input) = none := by
          simp [splitCtxCache, hprefix, hcache]
        rw [ctxRandomOracle,
          QueryImpl.withCaching_run_none uniformSampleImpl hcache]
        unfold ctxSplitRandomOracle
        simp only [StateT.run, hprefix]
        rw [hsplit]
        simp only [if_false]
        simp only [uniformSampleImpl, Functor.map_map]
        change (fun digest : CtxDigest =>
            (digest, splitCtxCache key (cache.cacheQuery ((), input) digest))) <$>
              ($ᵗ CtxDigest) =
          (fun digest : CtxDigest =>
            (digest, cachePublic (splitCtxCache key cache) ((), input) digest)) <$>
              ($ᵗ CtxDigest)
        apply congrArg (fun f : CtxDigest → CtxDigest × SplitCache =>
          f <$> ($ᵗ CtxDigest))
        funext digest
        congr 1
        exact splitCtxCache_cacheQuery_public key cache ((), input) digest hprefix
    | some digest =>
        have hsplit :
            (splitCtxCache key cache).publicCache ((), input) = some digest := by
          simp [splitCtxCache, hprefix, hcache]
        rw [ctxRandomOracle,
          QueryImpl.withCaching_run_some uniformSampleImpl hcache]
        unfold ctxSplitRandomOracle
        simp [StateT.run, hprefix, hsplit]

/-- Lazy ROM access to the secret-prefix component by its key-free suffix only. -/
noncomputable def ctxKeyFreeSuffixOracle :
    QueryImpl CtxSuffixRO (StateT SplitCache ProbComp) := fun suffix cache =>
  ctxKeyFreeSuffixStep suffix cache

/-- Routed access at an honest outer input is exactly key-free suffix access. -/
theorem ctxSplitRandomOracle_outerInput_eq_keyFreeSuffix
    (key : CtxKey) (nonce : CtxNonce) (context : CtxRecordContext)
    (tag : Pqxdh.Bytes) (cache : SplitCache) :
    (ctxSplitRandomOracle key
      ((), outerInput key nonce context tag)).run cache =
        (ctxKeyFreeSuffixOracle (outerSuffix nonce context tag)).run cache := by
  unfold ctxSplitRandomOracle ctxKeyFreeSuffixOracle
  simp only [StateT.run, secretPrefixQuery_outerInput, if_pos]
  rw [secretSuffix_outerInput]

/-- Public canonical queries routed through the split representation. -/
noncomputable def ctxSplitRoutedPublicOracle (key : CtxKey) :
    QueryImpl CtxRO (StateT CtxIndependentTagState ProbComp) :=
  fun query state => do
    let (digest, cache) ← (ctxSplitRandomOracle key query).run state.cache
    pure (digest, state.addPublic query.2 cache)

/-- Canonical public-query handling projects exactly to routed split-cache handling. -/
theorem ctxPublicOracle_split_projection (key : CtxKey)
    (query : CtxRO.Domain) (state : CtxHandlerState) :
    Prod.map id (splitHandlerState key) <$>
        (ctxPublicOracle query).run state =
      (ctxSplitRoutedPublicOracle key query).run (splitHandlerState key state) := by
  unfold ctxPublicOracle ctxSplitRoutedPublicOracle
  simp only [StateT.run, map_bind, map_pure]
  change ((ctxRandomOracle query).run state.cache >>= fun result =>
      pure (result.1,
        splitHandlerState key (state.addPublic query.2 result.2))) =
    ((ctxSplitRandomOracle key query).run (splitCtxCache key state.cache) >>= fun result =>
      pure (result.1,
        (splitHandlerState key state).addPublic query.2 result.2))
  simp only [splitHandlerState_addPublic]
  rw [← bind_map_left]
  simp only [bind_pure]
  rw [bind_pure_comp]
  rw [← ctxRandomOracle_split_projection key query state.cache]
  rw [Functor.map_map]
  rfl

/-- Public queries in the independent-tag game use only the complete-input public cache. -/
noncomputable def ctxIndependentPublicOracle :
    QueryImpl CtxRO (StateT CtxIndependentTagState ProbComp) :=
  fun query state => do
    let (digest, publicCache) ←
      (ctxRandomOracle query).run state.cache.publicCache
    let cache := { state.cache with publicCache := publicCache }
    pure (digest, state.addPublic query.2 cache)

/-- Nonce-respecting CTX sealing whose outer tag is addressed only by the key-free suffix. -/
noncomputable def ctxKeyFreeSealOracle (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxSealSpec (StateT CtxIndependentTagState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let base := c.aeadSeal key.toList input.nonce.toList
        input.context.ad.bytes input.plaintext
      let suffix := outerSuffix input.nonce input.context base.2
      let (commit, cache) ← (ctxKeyFreeSuffixOracle suffix).run state.cache
      let record : CtxRomRecord :=
        ⟨base.1, base.2, c.aeadSeal_tag_length _ _ _ _, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- Canonical nonce-respecting sealing projects exactly to key-free suffix sealing. -/
theorem ctxSealOracle_split_projection (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : CtxHandlerState) :
    Prod.map id (splitHandlerState key) <$>
        (ctxSealOracle c key input).run state =
      (ctxKeyFreeSealOracle c key input).run (splitHandlerState key state) := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxSealOracle ctxKeyFreeSealOracle
    simp [StateT.run, hused, splitHandlerState]
  · unfold ctxSealOracle ctxKeyFreeSealOracle
    simp only [StateT.run]
    simp only [hused, if_false, splitHandlerState]
    simp only [map_bind, map_pure]
    simp only [Prod.map, id_eq, splitHandlerState_addSeal]
    rw [← bind_map_left]
    simp only [bind_pure]
    rw [bind_pure_comp]
    have hsuffix :
        ctxKeyFreeSuffixOracle
            (outerSuffix input.nonce input.context
              (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                input.plaintext).2)
            (splitCtxCache key state.cache) =
          ctxSplitRandomOracle key
            ((), outerInput key input.nonce input.context
              (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                input.plaintext).2)
            (splitCtxCache key state.cache) :=
      (ctxSplitRandomOracle_outerInput_eq_keyFreeSuffix key input.nonce
        input.context
        (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
          input.plaintext).2
        (splitCtxCache key state.cache)).symm
    rw [hsuffix]
    have hprojection :
        Prod.map id (splitCtxCache key) <$>
            ctxRandomOracle
              ((), outerInput key input.nonce input.context
                (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                  input.plaintext).2)
              state.cache =
          ctxSplitRandomOracle key
            ((), outerInput key input.nonce input.context
              (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
                input.plaintext).2)
            (splitCtxCache key state.cache) :=
      ctxRandomOracle_split_projection key
        ((), outerInput key input.nonce input.context
          (c.aeadSeal key.toList input.nonce.toList input.context.ad.bytes
            input.plaintext).2)
        state.cache
    rw [← hprojection]
    rw [Functor.map_map]
    rfl

/-- The canonical adversary handler routed through the exact split-cache state. -/
noncomputable def ctxSplitRoutedImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT CtxIndependentTagState ProbComp) :=
  ctxSplitRoutedPublicOracle key + ctxKeyFreeSealOracle c key

/-- The independent-tag handler keeps all adversary ROM traffic in the public cache. -/
noncomputable def ctxIndependentTagImpl (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl CtxAdversarySpec (StateT CtxIndependentTagState ProbComp) :=
  ctxIndependentPublicOracle + ctxKeyFreeSealOracle c key

/-- Every canonical adversary step projects exactly to its routed split-cache step. -/
theorem ctxAdversaryImpl_split_projection_step (c : Pqxdh.Crypto)
    (key : CtxKey) (query : CtxAdversarySpec.Domain)
    (state : CtxHandlerState) :
    Prod.map id (splitHandlerState key) <$>
        (ctxAdversaryImpl c key query).run state =
      (ctxSplitRoutedImpl c key query).run (splitHandlerState key state) := by
  rcases query with query | input
  · exact ctxPublicOracle_split_projection key query state
  · exact ctxSealOracle_split_projection c key input state

/-- Every complete adaptive canonical run projects exactly to the routed split game. -/
theorem ctxAdversaryImpl_split_projection_run (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : CtxAdversary) :
    Prod.map id (splitHandlerState key) <$>
        (simulateQ (ctxAdversaryImpl c key) adversary.main).run
          emptyCtxHandlerState =
      (simulateQ (ctxSplitRoutedImpl c key) adversary.main).run
        emptyCtxIndependentTagState := by
  simpa using OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxAdversaryImpl c key) (ctxSplitRoutedImpl c key)
    (splitHandlerState key)
    (ctxAdversaryImpl_split_projection_step c key)
    adversary.main emptyCtxHandlerState

/-- Every complete canonical run, for an arbitrary result type, projects exactly to the routed split game. -/
theorem ctxAdversaryImpl_split_projection_run_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    Prod.map id (splitHandlerState key) <$>
        (simulateQ (ctxAdversaryImpl c key) main).run
          emptyCtxHandlerState =
      (simulateQ (ctxSplitRoutedImpl c key) main).run
        emptyCtxIndependentTagState := by
  simpa using OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxAdversaryImpl c key) (ctxSplitRoutedImpl c key)
    (splitHandlerState key)
    (ctxAdversaryImpl_split_projection_step c key)
    main emptyCtxHandlerState

/-- Projecting an underlying stateful step commutes with the sticky-bad wrapper. -/
theorem withStickyBad_projection {m : Type → Type} [Monad m] [LawfulMonad m]
    {α σ τ : Type} (fires : Bool) (source : StateT σ m α)
    (target : StateT τ m α) (project : σ → τ) (state : σ × Bool)
    (hstep : Prod.map id project <$> source.run state.1 =
      target.run (project state.1)) :
    Prod.map id (fun result => (project result.1, result.2)) <$>
        (withStickyBad fires source).run state =
      (withStickyBad fires target).run (project state.1, state.2) := by
  rcases state with ⟨state, bad⟩
  unfold withStickyBad
  simp only [StateT.run, map_bind, map_pure, Prod.map, id_eq]
  change (source.run state >>= fun result =>
      pure (result.1, project result.2, bad || fires)) =
    (target.run (project state) >>= fun result =>
      pure (result.1, result.2, bad || fires))
  rw [← hstep]
  simp

/-- Routed split-cache game with the exact public secret-prefix bad flag. -/
noncomputable def ctxSplitRoutedWithPrefixFlagImpl (c : Pqxdh.Crypto)
    (key : CtxKey) :
    QueryImpl CtxAdversarySpec
      (StateT (CtxIndependentTagState × Bool) ProbComp) := fun query =>
  match query with
  | .inl input =>
      withStickyBad (decide (SecretPrefixQuery key input.2))
        (ctxSplitRoutedPublicOracle key input)
  | .inr input => withStickyBad false (ctxKeyFreeSealOracle c key input)

/-- Key-free independent-tag game carrying the same analysis-only prefix flag. -/
noncomputable def ctxIndependentWithPrefixFlagImpl (c : Pqxdh.Crypto)
    (key : CtxKey) :
    QueryImpl CtxAdversarySpec
      (StateT (CtxIndependentTagState × Bool) ProbComp) := fun query =>
  match query with
  | .inl input =>
      withStickyBad (decide (SecretPrefixQuery key input.2))
        (ctxIndependentPublicOracle input)
  | .inr input => withStickyBad false (ctxKeyFreeSealOracle c key input)

/-- One flagged canonical step projects exactly to the flagged routed split step. -/
theorem ctxRealWithPrefixFlagImpl_split_projection_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxHandlerState × Bool) :
    Prod.map id (splitFlaggedHandlerState key) <$>
        (ctxRealWithPrefixFlagImpl c key query).run state =
      (ctxSplitRoutedWithPrefixFlagImpl c key query).run
        (splitFlaggedHandlerState key state) := by
  rcases query with query | input
  · change Prod.map id
        (fun result : CtxHandlerState × Bool =>
          (splitHandlerState key result.1, result.2)) <$>
          (withStickyBad (decide (SecretPrefixQuery key query.2))
            (ctxPublicOracle query)).run state =
        (withStickyBad (decide (SecretPrefixQuery key query.2))
          (ctxSplitRoutedPublicOracle key query)).run
            (splitHandlerState key state.1, state.2)
    exact withStickyBad_projection
      (decide (SecretPrefixQuery key query.2))
      (ctxPublicOracle query) (ctxSplitRoutedPublicOracle key query)
      (splitHandlerState key) state
      (ctxPublicOracle_split_projection key query state.1)
  · change Prod.map id
        (fun result : CtxHandlerState × Bool =>
          (splitHandlerState key result.1, result.2)) <$>
          (withStickyBad false (ctxSealOracle c key input)).run state =
        (withStickyBad false (ctxKeyFreeSealOracle c key input)).run
          (splitHandlerState key state.1, state.2)
    exact withStickyBad_projection false
      (ctxSealOracle c key input) (ctxKeyFreeSealOracle c key input)
      (splitHandlerState key) state
      (ctxSealOracle_split_projection c key input state.1)

/-- The complete flagged canonical run projects exactly to the flagged routed split run. -/
theorem ctxRealWithPrefixFlagImpl_split_projection_run
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Prod.map id (splitFlaggedHandlerState key) <$>
        (simulateQ (ctxRealWithPrefixFlagImpl c key) adversary.main).run
          (emptyCtxHandlerState, false) =
      (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key)
        adversary.main).run (emptyCtxIndependentTagState, false) := by
  simpa [splitFlaggedHandlerState] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ctxRealWithPrefixFlagImpl c key)
      (ctxSplitRoutedWithPrefixFlagImpl c key)
      (splitFlaggedHandlerState key)
      (ctxRealWithPrefixFlagImpl_split_projection_step c key)
      adversary.main (emptyCtxHandlerState, false)

/-- Every complete flagged canonical run, for an arbitrary result type, projects exactly to the flagged routed split run. -/
theorem ctxRealWithPrefixFlagImpl_split_projection_run_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    Prod.map id (splitFlaggedHandlerState key) <$>
        (simulateQ (ctxRealWithPrefixFlagImpl c key) main).run
          (emptyCtxHandlerState, false) =
      (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key) main).run
        (emptyCtxIndependentTagState, false) := by
  simpa [splitFlaggedHandlerState] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (ctxRealWithPrefixFlagImpl c key)
      (ctxSplitRoutedWithPrefixFlagImpl c key)
      (splitFlaggedHandlerState key)
      (ctxRealWithPrefixFlagImpl_split_projection_step c key)
      main (emptyCtxHandlerState, false)

/-- Away from the hidden prefix, routed and independent public ROM steps coincide. -/
theorem ctxSplitRoutedPublicOracle_eq_independent_of_not_prefix
    (key : CtxKey) (query : CtxRO.Domain)
    (state : CtxIndependentTagState)
    (hprefix : ¬SecretPrefixQuery key query.2) :
    (ctxSplitRoutedPublicOracle key query).run state =
      (ctxIndependentPublicOracle query).run state := by
  cases hcache : state.cache.publicCache query with
  | none =>
      unfold ctxSplitRoutedPublicOracle ctxIndependentPublicOracle
      unfold ctxSplitRandomOracle
      simp only [StateT.run, hprefix, if_false, hcache]
      have horacle :
          ctxRandomOracle query state.cache.publicCache =
            (fun digest =>
              (digest, state.cache.publicCache.cacheQuery query digest)) <$>
                ($ᵗ CtxDigest) :=
        QueryImpl.withCaching_run_none uniformSampleImpl hcache
      rw [horacle]
      simp [cachePublic]
  | some digest =>
      unfold ctxSplitRoutedPublicOracle ctxIndependentPublicOracle
      unfold ctxSplitRandomOracle
      simp only [StateT.run, hprefix, if_false, hcache]
      have horacle :
          ctxRandomOracle query state.cache.publicCache =
            pure (digest, state.cache.publicCache) :=
        QueryImpl.withCaching_run_some uniformSampleImpl hcache
      rw [horacle]
      rfl

/-- Routed and independent split handlers agree on every transition that stays non-bad. -/
theorem ctxSplitRouted_independent_agree_good
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState)
    (output : CtxAdversarySpec.Range query)
    (state' : CtxIndependentTagState) :
    Pr[= (output, (state', false)) |
      (ctxSplitRoutedWithPrefixFlagImpl c key query).run (state, false)] =
    Pr[= (output, (state', false)) |
      (ctxIndependentWithPrefixFlagImpl c key query).run (state, false)] := by
  rcases query with query | input
  · by_cases hprefix : SecretPrefixQuery key query.2
    · rw [probOutput_eq_zero_of_not_mem_support,
        probOutput_eq_zero_of_not_mem_support]
      · intro hsupport
        let step : StateT CtxIndependentTagState ProbComp
            (CtxAdversarySpec.Range (.inl query)) :=
          ctxIndependentPublicOracle query
        have hsupport' : (output, (state', false)) ∈
            support ((withStickyBad true step).run (state, false)) := by
          simpa [ctxIndependentWithPrefixFlagImpl, hprefix, step] using hsupport
        have htrue := withStickyBad_true step
          (state, false) (output, state', false) hsupport'
        simp at htrue
      · intro hsupport
        let step : StateT CtxIndependentTagState ProbComp
            (CtxAdversarySpec.Range (.inl query)) :=
          ctxSplitRoutedPublicOracle key query
        have hsupport' : (output, (state', false)) ∈
            support ((withStickyBad true step).run (state, false)) := by
          simpa [ctxSplitRoutedWithPrefixFlagImpl, hprefix, step] using hsupport
        have htrue := withStickyBad_true step
          (state, false) (output, state', false) hsupport'
        simp at htrue
    · have hstep :=
        ctxSplitRoutedPublicOracle_eq_independent_of_not_prefix
          key query state hprefix
      simp only [ctxSplitRoutedWithPrefixFlagImpl,
        ctxIndependentWithPrefixFlagImpl, hprefix, decide_false]
      unfold withStickyBad
      simp only [StateT.run, Bool.false_or]
      change ctxSplitRoutedPublicOracle key query state =
        ctxIndependentPublicOracle query state at hstep
      rw [hstep]
  · rfl

/-- The routed split handler never clears its prefix-bad flag. -/
theorem ctxSplitRoutedWithPrefixFlagImpl_bad_mono
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState × Bool) (hbad : state.2 = true)
    (result : CtxAdversarySpec.Range query ×
      (CtxIndependentTagState × Bool))
    (hresult : result ∈ support
      ((ctxSplitRoutedWithPrefixFlagImpl c key query).run state)) :
    result.2.2 = true := by
  rcases query with query | input
  · exact withStickyBad_mono _ _ state hbad result hresult
  · exact withStickyBad_mono _ _ state hbad result hresult

/-- The independent-tag handler never clears its prefix-bad flag. -/
theorem ctxIndependentWithPrefixFlagImpl_bad_mono
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState × Bool) (hbad : state.2 = true)
    (result : CtxAdversarySpec.Range query ×
      (CtxIndependentTagState × Bool))
    (hresult : result ∈ support
      ((ctxIndependentWithPrefixFlagImpl c key query).run state)) :
    result.2.2 = true := by
  rcases query with query | input
  · exact withStickyBad_mono _ _ state hbad result hresult
  · exact withStickyBad_mono _ _ state hbad result hresult

/-- Fixed-key flagged transcript of the routed split-cache handler. -/
noncomputable def ctxSplitRoutedFlaggedBeforeVerify
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ProbComp (CtxAliasTarget × (CtxIndependentTagState × Bool)) :=
  (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key)
    adversary.main).run (emptyCtxIndependentTagState, false)

/-- Fixed-key flagged transcript of the key-free independent-tag handler. -/
noncomputable def ctxIndependentTagFlaggedBeforeVerify
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ProbComp (CtxAliasTarget × (CtxIndependentTagState × Bool)) :=
  (simulateQ (ctxIndependentWithPrefixFlagImpl c key)
    adversary.main).run (emptyCtxIndependentTagState, false)

/-- Split-cache projection preserves the exact canonical prefix-bad probability. -/
theorem ctxSplitRouted_badProbability_eq_prefixBad
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Pr[fun result => result.2.2 = true |
      ctxSplitRoutedFlaggedBeforeVerify c key adversary] =
      ctxPrefixBadProbability c key adversary := by
  unfold ctxSplitRoutedFlaggedBeforeVerify ctxPrefixBadProbability
    ctxRealWithPrefixFlagBeforeVerify
  rw [← ctxRealWithPrefixFlagImpl_split_projection_run c key adversary,
    probEvent_map]
  rfl

/-- Split-cache projection preserves the canonical bad-event probability for an arbitrary result type. -/
theorem ctxSplitRouted_badProbability_eq_real_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    Pr[fun result : α × (CtxIndependentTagState × Bool) =>
        result.2.2 = true |
      (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key) main).run
        (emptyCtxIndependentTagState, false)] =
      Pr[fun result : α × (CtxHandlerState × Bool) =>
          result.2.2 = true |
        (simulateQ (ctxRealWithPrefixFlagImpl c key) main).run
          (emptyCtxHandlerState, false)] := by
  rw [← ctxRealWithPrefixFlagImpl_split_projection_run_of_main c key main,
    probEvent_map]
  rfl

/-- The routed and key-free independent-tag games differ only on prefix-bad. -/
theorem tvDist_ctxSplitRouted_independentTag_le_prefixBad
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxSplitRoutedFlaggedBeforeVerify c key adversary)
        (ctxIndependentTagFlaggedBeforeVerify c key adversary) ≤
      (ctxPrefixBadProbability c key adversary).toReal := by
  calc
    tvDist (ctxSplitRoutedFlaggedBeforeVerify c key adversary)
        (ctxIndependentTagFlaggedBeforeVerify c key adversary) ≤
        Pr[fun result => result.2.2 = true |
          ctxSplitRoutedFlaggedBeforeVerify c key adversary].toReal :=
      OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
        (ctxSplitRoutedWithPrefixFlagImpl c key)
        (ctxIndependentWithPrefixFlagImpl c key)
        adversary.main emptyCtxIndependentTagState
        (ctxSplitRouted_independent_agree_good c key)
        (ctxSplitRoutedWithPrefixFlagImpl_bad_mono c key)
        (ctxIndependentWithPrefixFlagImpl_bad_mono c key)
    _ = (ctxPrefixBadProbability c key adversary).toReal :=
      congrArg ENNReal.toReal
        (ctxSplitRouted_badProbability_eq_prefixBad c key adversary)

/-- For an arbitrary result type, routed and key-free independent-tag full runs differ only on the single prefix-bad event. -/
theorem tvDist_ctxSplitRouted_independentTag_le_prefixBad_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    tvDist
        ((simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key) main).run
          (emptyCtxIndependentTagState, false))
        ((simulateQ (ctxIndependentWithPrefixFlagImpl c key) main).run
          (emptyCtxIndependentTagState, false)) ≤
      Pr[fun result : α × (CtxIndependentTagState × Bool) =>
        result.2.2 = true |
        (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key) main).run
          (emptyCtxIndependentTagState, false)].toReal := by
  exact
    OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
      (ctxSplitRoutedWithPrefixFlagImpl c key)
      (ctxIndependentWithPrefixFlagImpl c key)
      main emptyCtxIndependentTagState
      (ctxSplitRouted_independent_agree_good c key)
      (ctxSplitRoutedWithPrefixFlagImpl_bad_mono c key)
      (ctxIndependentWithPrefixFlagImpl_bad_mono c key)

/-- Dropping the routed split flag recovers the unflagged routed handler. -/
theorem ctxSplitRoutedWithPrefixFlagImpl_proj_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState × Bool) :
    Prod.map id Prod.fst <$>
        (ctxSplitRoutedWithPrefixFlagImpl c key query).run state =
      (ctxSplitRoutedImpl c key query).run state.1 := by
  rcases query with query | input
  · exact withStickyBad_fst_map_run _ _ state
  · exact withStickyBad_fst_map_run _ _ state

/-- Dropping the independent-game flag recovers the unflagged independent handler. -/
theorem ctxIndependentWithPrefixFlagImpl_proj_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState × Bool) :
    Prod.map id Prod.fst <$>
        (ctxIndependentWithPrefixFlagImpl c key query).run state =
      (ctxIndependentTagImpl c key query).run state.1 := by
  rcases query with query | input
  · exact withStickyBad_fst_map_run _ _ state
  · exact withStickyBad_fst_map_run _ _ state

/-- Dropping the flag from the complete routed run is exact. -/
theorem ctxSplitRoutedWithPrefixFlagImpl_proj_run
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Prod.map id Prod.fst <$>
        ctxSplitRoutedFlaggedBeforeVerify c key adversary =
      (simulateQ (ctxSplitRoutedImpl c key) adversary.main).run
        emptyCtxIndependentTagState := by
  unfold ctxSplitRoutedFlaggedBeforeVerify
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxSplitRoutedWithPrefixFlagImpl c key) (ctxSplitRoutedImpl c key)
    Prod.fst (ctxSplitRoutedWithPrefixFlagImpl_proj_step c key)
    adversary.main (emptyCtxIndependentTagState, false)

/-- Dropping the flag from an arbitrary-result routed run is exact. -/
theorem ctxSplitRoutedWithPrefixFlagImpl_proj_run_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    Prod.map id Prod.fst <$>
        (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key) main).run
          (emptyCtxIndependentTagState, false) =
      (simulateQ (ctxSplitRoutedImpl c key) main).run
        emptyCtxIndependentTagState := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxSplitRoutedWithPrefixFlagImpl c key) (ctxSplitRoutedImpl c key)
    Prod.fst (ctxSplitRoutedWithPrefixFlagImpl_proj_step c key)
    main (emptyCtxIndependentTagState, false)

/-- Dropping the flag from the complete independent-tag run is exact. -/
theorem ctxIndependentWithPrefixFlagImpl_proj_run
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Prod.map id Prod.fst <$>
        ctxIndependentTagFlaggedBeforeVerify c key adversary =
      (simulateQ (ctxIndependentTagImpl c key) adversary.main).run
        emptyCtxIndependentTagState := by
  unfold ctxIndependentTagFlaggedBeforeVerify
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxIndependentWithPrefixFlagImpl c key) (ctxIndependentTagImpl c key)
    Prod.fst (ctxIndependentWithPrefixFlagImpl_proj_step c key)
    adversary.main (emptyCtxIndependentTagState, false)

/-- Dropping the flag from an arbitrary-result independent-tag run is exact. -/
theorem ctxIndependentWithPrefixFlagImpl_proj_run_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {α : Type}
    (main : OracleComp CtxAdversarySpec α) :
    Prod.map id Prod.fst <$>
        (simulateQ (ctxIndependentWithPrefixFlagImpl c key) main).run
          (emptyCtxIndependentTagState, false) =
      (simulateQ (ctxIndependentTagImpl c key) main).run
        emptyCtxIndependentTagState := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (ctxIndependentWithPrefixFlagImpl c key)
    (ctxIndependentTagImpl c key)
    Prod.fst (ctxIndependentWithPrefixFlagImpl_proj_step c key)
    main (emptyCtxIndependentTagState, false)

/-- Convert an independent-tag handler state to the common pre-verification view. -/
def independentHandlerStateToBeforeVerify (key : CtxKey)
    (target : CtxAliasTarget) (state : CtxIndependentTagState) :
    CtxBeforeVerify :=
  ⟨key, target, state.successfulSeals, state.usedNonces, state.publicInputs⟩

/-- Retain the full split cache with the common pre-verification view. -/
def independentTrackedProjection (key : CtxKey)
    (result : CtxAliasTarget × CtxIndependentTagState) :
    CtxBeforeVerify × SplitCache :=
  (independentHandlerStateToBeforeVerify key result.1 result.2,
    result.2.cache)

/-- Drop a flagged independent state onto the common split-cache surface. -/
def independentFlaggedProjection (key : CtxKey)
    (result : CtxAliasTarget × (CtxIndependentTagState × Bool)) :
    CtxBeforeVerify × SplitCache :=
  independentTrackedProjection key (result.1, result.2.1)

/-- Fixed-key routed split-cache game on the common pre-verification surface. -/
noncomputable def ctxSplitRoutedBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × SplitCache) :=
  independentTrackedProjection key <$>
    (simulateQ (ctxSplitRoutedImpl c key) adversary.main).run
      emptyCtxIndependentTagState

/-- Fixed-key key-free independent-tag game on the common pre-verification surface. -/
noncomputable def ctxIndependentTagBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × SplitCache) :=
  independentTrackedProjection key <$>
    (simulateQ (ctxIndependentTagImpl c key) adversary.main).run
      emptyCtxIndependentTagState

/-- Flag erasure and common-output projection recover the routed inner game exactly. -/
theorem independentFlaggedProjection_splitRouted
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    independentFlaggedProjection key <$>
        ctxSplitRoutedFlaggedBeforeVerify c key adversary =
      ctxSplitRoutedBeforeVerifyInner c adversary key := by
  unfold ctxSplitRoutedBeforeVerifyInner
  calc
    independentFlaggedProjection key <$>
        ctxSplitRoutedFlaggedBeforeVerify c key adversary =
      independentTrackedProjection key <$>
        (Prod.map id Prod.fst <$>
          ctxSplitRoutedFlaggedBeforeVerify c key adversary) := by
            rw [Functor.map_map]
            rfl
    _ = independentTrackedProjection key <$>
        (simulateQ (ctxSplitRoutedImpl c key) adversary.main).run
          emptyCtxIndependentTagState := by
      rw [ctxSplitRoutedWithPrefixFlagImpl_proj_run]

/-- Flag erasure and common-output projection recover the independent inner game exactly. -/
theorem independentFlaggedProjection_independent
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    independentFlaggedProjection key <$>
        ctxIndependentTagFlaggedBeforeVerify c key adversary =
      ctxIndependentTagBeforeVerifyInner c adversary key := by
  unfold ctxIndependentTagBeforeVerifyInner
  calc
    independentFlaggedProjection key <$>
        ctxIndependentTagFlaggedBeforeVerify c key adversary =
      independentTrackedProjection key <$>
        (Prod.map id Prod.fst <$>
          ctxIndependentTagFlaggedBeforeVerify c key adversary) := by
            rw [Functor.map_map]
            rfl
    _ = independentTrackedProjection key <$>
        (simulateQ (ctxIndependentTagImpl c key) adversary.main).run
          emptyCtxIndependentTagState := by
      rw [ctxIndependentWithPrefixFlagImpl_proj_run]

/-- Fixed-key routed and independent-tag views differ by at most one prefix-bad charge. -/
theorem tvDist_ctxSplitRoutedBeforeVerifyInner_independentTag_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxSplitRoutedBeforeVerifyInner c adversary key)
        (ctxIndependentTagBeforeVerifyInner c adversary key) ≤
      (ctxSecretPrefixQueriedProbabilityInner c key adversary).toReal := by
  rw [← independentFlaggedProjection_splitRouted,
    ← independentFlaggedProjection_independent]
  refine (tvDist_map_le (m := ProbComp)
    (independentFlaggedProjection key)
    (ctxSplitRoutedFlaggedBeforeVerify c key adversary)
    (ctxIndependentTagFlaggedBeforeVerify c key adversary)).trans ?_
  rw [← ctxPrefixBadProbability_eq_secretPrefixQueriedProbabilityInner]
  exact tvDist_ctxSplitRouted_independentTag_le_prefixBad c key adversary

/-- Project the canonical pre-verification cache to its exact split representation. -/
def splitBeforeVerifyProjection (key : CtxKey)
    (result : CtxBeforeVerify × CtxRO.QueryCache) :
    CtxBeforeVerify × SplitCache :=
  (result.1, splitCtxCache key result.2)

/-- Fixed-key canonical game presented on the common split-cache surface. -/
noncomputable def ctxSplitBeforeVerifyInner (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) (key : CtxKey) :
    ProbComp (CtxBeforeVerify × SplitCache) :=
  splitBeforeVerifyProjection key <$> ctxBeforeVerifyInner c adversary key

/-- Exact full-run projection identifies canonical and routed split inner games. -/
theorem ctxSplitRoutedBeforeVerifyInner_eq_ctxSplitBeforeVerifyInner
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ctxSplitRoutedBeforeVerifyInner c adversary key =
      ctxSplitBeforeVerifyInner c adversary key := by
  unfold ctxSplitRoutedBeforeVerifyInner ctxSplitBeforeVerifyInner
  rw [← ctxAdversaryImpl_split_projection_run c key adversary,
    Functor.map_map]
  have hcurrent :
      ctxBeforeVerifyInner c adversary key =
        trackedProjection key <$>
          (simulateQ (ctxAdversaryImpl c key) adversary.main).run
            emptyCtxHandlerState := by
    rfl
  rw [hcurrent, Functor.map_map]
  apply congrArg (fun f => f <$>
    (simulateQ (ctxAdversaryImpl c key) adversary.main).run
      emptyCtxHandlerState)
  funext result
  rcases result with ⟨target, state⟩
  rfl

/-- Fixed-key canonical split and independent-tag games charge prefix-bad once. -/
theorem tvDist_ctxSplitBeforeVerifyInner_independentTag_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    tvDist (ctxSplitBeforeVerifyInner c adversary key)
        (ctxIndependentTagBeforeVerifyInner c adversary key) ≤
      (ctxSecretPrefixQueriedProbabilityInner c key adversary).toReal := by
  rw [← ctxSplitRoutedBeforeVerifyInner_eq_ctxSplitBeforeVerifyInner]
  exact tvDist_ctxSplitRoutedBeforeVerifyInner_independentTag_le_secretPrefixQueried
    c key adversary

/-- Uniform-key canonical game on the exact split-cache surface. -/
noncomputable def ctxSplitBeforeVerifyGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × SplitCache) := do
  let key ← $ᵗ CtxKey
  ctxSplitBeforeVerifyInner c adversary key

/-- Uniform-key game with public and honest outer-tag caches physically independent. -/
noncomputable def ctxIndependentTagGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) :
    ProbComp (CtxBeforeVerify × SplitCache) := do
  let key ← $ᵗ CtxKey
  ctxIndependentTagBeforeVerifyInner c adversary key

/-- The key-free independent-tag hop charges the secret-prefix event exactly once. -/
theorem tvDist_ctxSplitBeforeVerifyGame_independentTagGame_le_secretPrefixQueried
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    tvDist (ctxSplitBeforeVerifyGame c adversary)
        (ctxIndependentTagGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
  rw [ctxSecretPrefixQueriedProbability_toReal_eq_tsum]
  unfold ctxSplitBeforeVerifyGame ctxIndependentTagGame
  refine (tvDist_bind_left_le ($ᵗ CtxKey) _ _).trans ?_
  refine Summable.tsum_le_tsum (fun key => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left
      (tvDist_ctxSplitBeforeVerifyInner_independentTag_le_secretPrefixQueried
        c key adversary) ENNReal.toReal_nonneg
  · refine Summable.of_nonneg_of_le
      (fun key => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun key => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (tvDist_le_one _ _)) ?_
    exact ENNReal.summable_toReal tsum_probOutput_ne_top
  · refine Summable.of_nonneg_of_le
      (fun key => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun key => mul_le_of_le_one_right ENNReal.toReal_nonneg ?_) ?_
    · exact ENNReal.toReal_mono one_ne_top probEvent_le_one
    · exact ENNReal.summable_toReal tsum_probOutput_ne_top

end BeaconcryptCore.Computational.CtxIndependentTags
