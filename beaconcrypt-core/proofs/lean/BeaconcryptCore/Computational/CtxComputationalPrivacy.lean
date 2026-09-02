import BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation

/-!
# Computational privacy of modified CTX

This module gives the confidentiality half of the modified-CTX component a bounded Boolean game.
The real experiment samples one uniform 256-bit CTX key and exposes the canonical shared lazy random oracle together with nonce-respecting sealing.
The ideal experiment keeps the public lazy random oracle and nonce-reuse leakage, but replaces every fresh record by an independently sampled length-matched body, 16-byte base tag, and 64-byte outer commitment.

The proof is deliberately component-local.
ProVerif remains responsible for protocol schedules, state, secrecy queries, and correspondence arguments.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxComputationalPrivacy

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling CtxNonceAeadIntCtxt CtxNonceAeadIndDollar
  CtxNonceAeadIndDollarValidation

/-- A Boolean CTX privacy adversary with separate public-ROM and sealing-query bounds. -/
structure CtxPrivacyAdversary (qH qE : ℕ) where
  /-- Adaptive public-ROM and nonce-respecting chosen-plaintext computation. -/
  main : OracleComp CtxAdversarySpec Bool
  /-- At most `qH` public random-oracle queries are made. -/
  publicQueryBound : main.IsQueryBoundP IsCtxPublicQuery qH
  /-- At most `qE` chosen-plaintext sealing queries are made. -/
  sealQueryBound : main.IsQueryBoundP IsCtxSealQuery qE

/-- Fixed-key real privacy experiment over the canonical shared lazy random oracle. -/
noncomputable def ctxPrivacyRealExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let result ←
    (simulateQ (ctxAdversaryImpl c key) adversary.main).run
      emptyCtxHandlerState
  pure result.1

/-- Real modified-CTX privacy game with one uniform hidden 256-bit key. -/
noncomputable def ctxPrivacyRealGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxPrivacyRealExpInner c key adversary

/-- Ideal nonce-respecting CTX sealing.

Repeated nonces are rejected before any sample is drawn.
A fresh request receives one uniform body with the plaintext length, one independent uniform 16-byte tag, and one independent uniform 64-byte outer commitment.
The suffix-cache update is private bookkeeping used by later exact-game projections; public random-oracle calls use the disjoint canonical public cache.
-/
noncomputable def ctxPrivacyIdealSealOracle :
    QueryImpl CtxSealSpec (StateT CtxIndependentTagState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commit ← $ᵗ CtxDigest
      let suffix := outerSuffix input.nonce input.context tag.toList
      let cache := cacheSuffix state.cache suffix commit
      let record : CtxRomRecord :=
        ⟨body.toList, tag.toList, tag.toList_length, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)

/-- Ideal CTX interface: a consistent public lazy random oracle plus ideal fresh records. -/
noncomputable def ctxPrivacyIdealImpl :
    QueryImpl CtxAdversarySpec
      (StateT CtxIndependentTagState ProbComp) :=
  ctxIndependentPublicOracle + ctxPrivacyIdealSealOracle

/-- Explicit ideal CTX privacy game. -/
noncomputable def ctxPrivacyIdealGame
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp Bool := do
  let result ←
    (simulateQ ctxPrivacyIdealImpl adversary.main).run
      emptyCtxIndependentTagState
  pure result.1

/-- Modified-CTX privacy advantage on the final Boolean decision. -/
noncomputable def ctxPrivacyAdvantage
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ℝ :=
  (ctxPrivacyRealGame c adversary).boolDistAdvantage
    (ctxPrivacyIdealGame adversary)

/-- Fixed-key canonical execution carrying the analysis-only public-prefix flag. -/
noncomputable def ctxPrivacyRealFlaggedExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp (Bool × (CtxHandlerState × Bool)) :=
  (simulateQ (ctxRealWithPrefixFlagImpl c key) adversary.main).run
    (emptyCtxHandlerState, false)

/-- Fixed-key probability that a public query begins with the hidden CTX key. -/
noncomputable def ctxPrivacySecretPrefixProbabilityInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ℝ≥0∞ :=
  Pr[fun result => result.2.2 = true |
    ctxPrivacyRealFlaggedExpInner c key adversary]

/-- Uniform-key flagged execution used to expose the single public-prefix event. -/
noncomputable def ctxPrivacyRealFlaggedGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp (Bool × (CtxHandlerState × Bool)) := do
  let key ← $ᵗ CtxKey
  ctxPrivacyRealFlaggedExpInner c key adversary

/-- Probability of the public hidden-key-prefix event in the real privacy execution. -/
noncomputable def ctxPrivacySecretPrefixProbability
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ℝ≥0∞ :=
  Pr[fun result => result.2.2 = true |
    ctxPrivacyRealFlaggedGame c adversary]

/-- Fixed-key flagged execution after exact split-cache routing. -/
noncomputable def ctxPrivacySplitRoutedFlaggedExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp (Bool × (CtxIndependentTagState × Bool)) :=
  (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key)
    adversary.main).run (emptyCtxIndependentTagState, false)

/-- Fixed-key flagged execution with public and honest-tag caches independent. -/
noncomputable def ctxPrivacyIndependentTagFlaggedExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ProbComp (Bool × (CtxIndependentTagState × Bool)) :=
  (simulateQ (ctxIndependentWithPrefixFlagImpl c key)
    adversary.main).run (emptyCtxIndependentTagState, false)

/-- Boolean output of the fixed-key routed split-cache execution. -/
noncomputable def ctxPrivacySplitRoutedExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool :=
  Prod.fst <$> ctxPrivacySplitRoutedFlaggedExpInner c key adversary

/-- Boolean output of the fixed-key lazy independent-tag execution. -/
noncomputable def ctxPrivacyIndependentTagExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool :=
  Prod.fst <$> ctxPrivacyIndependentTagFlaggedExpInner c key adversary

/-- Fixed-key privacy execution with exactly one direct `CtxDigest` sample per fresh seal. -/
noncomputable def ctxPrivacyDirectSampleExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool :=
  Prod.fst <$>
    (simulateQ (ctxDirectSampleIndependentTagImpl c key)
      adversary.main).run emptyCtxIndependentTagState

/-- Uniform-key lazy independent-tag privacy game. -/
noncomputable def ctxPrivacyIndependentTagGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxPrivacyIndependentTagExpInner c key adversary

/-- Uniform-key direct independent-tag privacy game. -/
noncomputable def ctxPrivacyDirectSampleGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxPrivacyDirectSampleExpInner c key adversary

/-- The analysis flag is exactly the public hidden-key-prefix event on every supported result. -/
theorem ctxPrivacyRealFlaggedExpInner_prefix_flag
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE)
    (result : Bool × (CtxHandlerState × Bool))
    (hresult : result ∈ support
      (ctxPrivacyRealFlaggedExpInner c key adversary)) :
    CtxPrefixFlagInvariant key result.2 := by
  exact ctxRealWithPrefixFlag_run_prefix_flag_of_main
    c key adversary.main result hresult

/-- The fixed-key bad probability is exactly membership of a hidden-prefix query in the public trace. -/
theorem ctxPrivacySecretPrefixProbabilityInner_eq_publicInputs
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacySecretPrefixProbabilityInner c key adversary =
      Pr[fun result =>
          ∃ input ∈ result.2.1.publicInputs,
            SecretPrefixQuery key input |
        ctxPrivacyRealFlaggedExpInner c key adversary] := by
  unfold ctxPrivacySecretPrefixProbabilityInner
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  exact ctxPrivacyRealFlaggedExpInner_prefix_flag
    c key adversary result hresult

/-- Exact split-cache projection preserves the fixed-key Boolean real experiment. -/
theorem ctxPrivacyRealExpInner_eq_splitRouted
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyRealExpInner c key adversary =
      ctxPrivacySplitRoutedExpInner c key adversary := by
  unfold ctxPrivacyRealExpInner ctxPrivacySplitRoutedExpInner
    ctxPrivacySplitRoutedFlaggedExpInner
  simp only [bind_pure_comp]
  calc
    Prod.fst <$>
        (simulateQ (ctxAdversaryImpl c key) adversary.main).run
          emptyCtxHandlerState =
      Prod.fst <$>
        (simulateQ (ctxSplitRoutedImpl c key) adversary.main).run
          emptyCtxIndependentTagState := by
        have hprojection := congrArg
          (fun run : ProbComp (Bool × CtxIndependentTagState) =>
            Prod.fst <$> run)
          (ctxAdversaryImpl_split_projection_run_of_main
            c key adversary.main)
        simpa [Functor.map_map] using hprojection
    _ = Prod.fst <$>
        (simulateQ (ctxSplitRoutedWithPrefixFlagImpl c key)
          adversary.main).run (emptyCtxIndependentTagState, false) := by
      have hdrop := congrArg
        (fun run : ProbComp (Bool × CtxIndependentTagState) =>
          Prod.fst <$> run)
        (ctxSplitRoutedWithPrefixFlagImpl_proj_run_of_main
          c key adversary.main)
      simpa [Functor.map_map] using hdrop.symm

/-- Split-cache projection preserves the exact fixed-key public-prefix probability. -/
theorem ctxPrivacySplitRouted_badProbability_eq_secretPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    Pr[fun result => result.2.2 = true |
        ctxPrivacySplitRoutedFlaggedExpInner c key adversary] =
      ctxPrivacySecretPrefixProbabilityInner c key adversary := by
  unfold ctxPrivacySplitRoutedFlaggedExpInner
    ctxPrivacySecretPrefixProbabilityInner
    ctxPrivacyRealFlaggedExpInner
  exact ctxSplitRouted_badProbability_eq_real_of_main
    c key adversary.main

/-- Routed and key-free Boolean executions differ only on the single public-prefix event. -/
theorem tvDist_ctxPrivacySplitRouted_independentTag_le_secretPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    tvDist (ctxPrivacySplitRoutedExpInner c key adversary)
        (ctxPrivacyIndependentTagExpInner c key adversary) ≤
      (ctxPrivacySecretPrefixProbabilityInner c key adversary).toReal := by
  unfold ctxPrivacySplitRoutedExpInner
    ctxPrivacyIndependentTagExpInner
  calc
    tvDist
        (Prod.fst <$>
          ctxPrivacySplitRoutedFlaggedExpInner c key adversary)
        (Prod.fst <$>
          ctxPrivacyIndependentTagFlaggedExpInner c key adversary) ≤
      tvDist
        (ctxPrivacySplitRoutedFlaggedExpInner c key adversary)
        (ctxPrivacyIndependentTagFlaggedExpInner c key adversary) := by
          exact tvDist_map_le (m := ProbComp) Prod.fst _ _
    _ ≤ Pr[fun result => result.2.2 = true |
          ctxPrivacySplitRoutedFlaggedExpInner c key adversary].toReal := by
      unfold ctxPrivacySplitRoutedFlaggedExpInner
        ctxPrivacyIndependentTagFlaggedExpInner
      exact tvDist_ctxSplitRouted_independentTag_le_prefixBad_of_main
        c key adversary.main
    _ = (ctxPrivacySecretPrefixProbabilityInner
          c key adversary).toReal := by
      exact congrArg ENNReal.toReal
        (ctxPrivacySplitRouted_badProbability_eq_secretPrefix
          c key adversary)

/-- Lazy honest suffix lookup is exactly one direct digest sample per successful fresh seal. -/
theorem ctxPrivacyIndependentTagExpInner_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyIndependentTagExpInner c key adversary =
      ctxPrivacyDirectSampleExpInner c key adversary := by
  unfold ctxPrivacyIndependentTagExpInner
    ctxPrivacyIndependentTagFlaggedExpInner
    ctxPrivacyDirectSampleExpInner
  calc
    Prod.fst <$>
        (simulateQ (ctxIndependentWithPrefixFlagImpl c key)
          adversary.main).run (emptyCtxIndependentTagState, false) =
      Prod.fst <$>
        (simulateQ (ctxIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState := by
      have hdrop := congrArg
        (fun run : ProbComp (Bool × CtxIndependentTagState) =>
          Prod.fst <$> run)
        (ctxIndependentWithPrefixFlagImpl_proj_run_of_main
          c key adversary.main)
      simpa [Functor.map_map] using hdrop
    _ = Prod.fst <$>
        (simulateQ (ctxDirectSampleIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState := by
      rw [ctxIndependentTagImpl_run_eq_directSample_of_main]

/-- Honest-tag lazy sampling and direct sampling are exactly equal after uniform key sampling. -/
theorem ctxPrivacyIndependentTagGame_eq_directSampleGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyIndependentTagGame c adversary =
      ctxPrivacyDirectSampleGame c adversary := by
  unfold ctxPrivacyIndependentTagGame ctxPrivacyDirectSampleGame
  apply bind_congr
  intro key
  exact ctxPrivacyIndependentTagExpInner_eq_directSample
    c key adversary

/-- At fixed key, replacing the canonical shared ROM by direct independent tags charges prefix-bad once. -/
theorem tvDist_ctxPrivacyRealExpInner_directSample_le_secretPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    tvDist (ctxPrivacyRealExpInner c key adversary)
        (ctxPrivacyDirectSampleExpInner c key adversary) ≤
      (ctxPrivacySecretPrefixProbabilityInner c key adversary).toReal := by
  rw [ctxPrivacyRealExpInner_eq_splitRouted,
    ← ctxPrivacyIndependentTagExpInner_eq_directSample]
  exact tvDist_ctxPrivacySplitRouted_independentTag_le_secretPrefix
    c key adversary

/-- Expand the uniform-key privacy prefix event into its fixed-key average. -/
theorem ctxPrivacySecretPrefixProbability_toReal_eq_tsum
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacySecretPrefixProbability c adversary).toReal =
      ∑' key : CtxKey,
        Pr[= key | $ᵗ CtxKey].toReal *
          (ctxPrivacySecretPrefixProbabilityInner
            c key adversary).toReal := by
  unfold ctxPrivacySecretPrefixProbability
    ctxPrivacyRealFlaggedGame
    ctxPrivacySecretPrefixProbabilityInner
  rw [probEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun key =>
    ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  refine tsum_congr fun key => ?_
  rw [ENNReal.toReal_mul]

/-- Canonical shared-ROM privacy and direct independent-tag privacy differ by one prefix charge. -/
theorem tvDist_ctxPrivacyRealGame_directSample_le_secretPrefix
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    tvDist (ctxPrivacyRealGame c adversary)
        (ctxPrivacyDirectSampleGame c adversary) ≤
      (ctxPrivacySecretPrefixProbability c adversary).toReal := by
  rw [ctxPrivacySecretPrefixProbability_toReal_eq_tsum]
  unfold ctxPrivacyRealGame ctxPrivacyDirectSampleGame
  refine (tvDist_bind_left_le ($ᵗ CtxKey) _ _).trans ?_
  refine Summable.tsum_le_tsum (fun key => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left
      (tvDist_ctxPrivacyRealExpInner_directSample_le_secretPrefix
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

/-- The real public branch is exactly the canonical shared lazy-ROM handler. -/
theorem ctxPrivacyRealImpl_public
    (c : Pqxdh.Crypto) (key : CtxKey) (query : CtxRO.Domain) :
    ctxAdversaryImpl c key (.inl query) = ctxPublicOracle query := by
  rfl

/-- The real sealing branch is exactly modeled nonce-AEAD sealing followed by the shared ROM. -/
theorem ctxPrivacyRealImpl_seal
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) :
    ctxAdversaryImpl c key (.inr input) = ctxSealOracle c key input := by
  rfl

/-- The ideal public branch remains the canonical consistent lazy random oracle. -/
theorem ctxPrivacyIdealImpl_public (query : CtxRO.Domain) :
    ctxPrivacyIdealImpl (.inl query) = ctxIndependentPublicOracle query := by
  rfl

/-- A repeated ideal nonce is rejected before any body, tag, or commitment sample. -/
theorem ctxPrivacyIdealSealOracle_run_of_used
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (hused : input.nonce ∈ state.usedNonces) :
    (ctxPrivacyIdealSealOracle input).run state = pure (none, state) := by
  unfold ctxPrivacyIdealSealOracle
  simp [StateT.run, hused]

/-- A fresh ideal nonce draws the length-matched body, tag, and commitment exactly once each. -/
theorem ctxPrivacyIdealSealOracle_run_of_fresh
    (input : CtxSealInput) (state : CtxIndependentTagState)
    (hfresh : input.nonce ∉ state.usedNonces) :
    (ctxPrivacyIdealSealOracle input).run state = (do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let commit ← $ᵗ CtxDigest
      let suffix := outerSuffix input.nonce input.context tag.toList
      let cache := cacheSuffix state.cache suffix commit
      let record : CtxRomRecord :=
        ⟨body.toList, tag.toList, tag.toList_length, commit⟩
      pure (some record, state.addSeal ⟨input, record⟩ cache)) := by
  unfold ctxPrivacyIdealSealOracle
  simp [StateT.run, hfresh]

/-- The real game samples its hidden key once, outside the complete adaptive execution. -/
theorem ctxPrivacyRealGame_eq
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyRealGame c adversary =
      ($ᵗ CtxKey >>= fun key => ctxPrivacyRealExpInner c key adversary) := by
  rfl

/-- The ideal game exposes only the adversary's final Boolean result. -/
theorem ctxPrivacyIdealGame_eq
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacyIdealGame adversary =
      Prod.fst <$>
        (simulateQ ctxPrivacyIdealImpl adversary.main).run
          emptyCtxIndependentTagState := by
  simp [ctxPrivacyIdealGame, bind_pure_comp]

/-- Boolean view reduction from the CTX interface to modified nonce-AEAD IND$.

The reduction retains the adversary's Boolean decision and discards its private CTX bookkeeping.
Public-ROM and outer-commitment randomness are generated inside the reduction, while every fresh seal is forwarded to the primitive challenger.
-/
noncomputable def ctxPrivacyViewReduction
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ModifiedNonceAeadINDDollarAdversary where
  main := Prod.fst <$>
    (simulateQ ctxRetainedBaseReductionImpl adversary.main).run
      emptyCtxIndependentTagState

/-- Flatten the Boolean view reduction against the random nonce-AEAD challenger. -/
noncomputable def ctxPrivacyRandomCombinedImpl :
    QueryImpl CtxAdversarySpec
      (StateT (CtxIndependentTagState × ModifiedNonceAeadHandlerState)
        ProbComp) :=
  (modifiedNonceAeadINDDollarRandomImpl.mapStateTBase
    ctxRetainedBaseReductionImpl).flattenStateT

/-- Interpreting the reduction's private digest sample in the IND$ random world leaves the primitive state unchanged. -/
theorem simulateQ_modifiedNonceAeadDigest_random :
    simulateQ modifiedNonceAeadINDDollarRandomImpl
        modifiedNonceAeadDigest =
      (liftM ($ᵗ CtxDigest) :
        StateT ModifiedNonceAeadHandlerState ProbComp CtxDigest) := by
  unfold modifiedNonceAeadINDDollarRandomImpl modifiedNonceAeadDigest
  rw [QueryImpl.simulateQ_add_liftComp_left]
  simp

/-- Public CTX queries preserve the synchronized source and random-challenger histories. -/
theorem ctxPrivacyRandomPublicOracle_projection
    (query : CtxRO.Domain) (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxIndependentPublicOracle query).run state =
      (ctxPrivacyRandomCombinedImpl (.inl query)).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  unfold ctxPrivacyRandomCombinedImpl ctxRetainedBaseReductionImpl
    ctxRetainedBasePublicOracle
  change _ =
    (fun result => (result.1.1, result.1.2, result.2)) <$>
      (simulateQ modifiedNonceAeadINDDollarRandomImpl
        (liftM ((ctxIndependentPublicOracle query).run state))).run
          (ctxIndependentTagStateToModifiedNonceAead state)
  unfold modifiedNonceAeadINDDollarRandomImpl
  rw [QueryImpl.simulateQ_add_liftM_left]
  unfold ctxIndependentPublicOracle
  rw [simulateQ_liftTarget]
  rw [simulateQ_ofLift_eq_self]
  rw [OracleComp.liftM_run_StateT]
  simp only [bind_pure_comp]
  simp only [StateT.run, Functor.map_map]
  change
    (fun result : CtxDigest × CtxRO.QueryCache =>
      let next := state.addPublic query.2
        { state.cache with publicCache := result.2 }
      (result.1, next,
        ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxRandomOracle query).run state.cache.publicCache =
      (fun result : CtxDigest × CtxRO.QueryCache =>
        let next := state.addPublic query.2
          { state.cache with publicCache := result.2 }
        (result.1, next,
          ctxIndependentTagStateToModifiedNonceAead state)) <$>
        (ctxRandomOracle query).run state.cache.publicCache
  congr 1

/-- An ideal CTX seal is exactly a random primitive body/tag followed by the reduction's private outer-commitment sample, with both nonce histories synchronized. -/
theorem ctxPrivacyRandomSealOracle_projection
    (input : CtxSealInput) (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxPrivacyIdealSealOracle input).run state =
      (ctxPrivacyRandomCombinedImpl (.inr input)).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  unfold ctxPrivacyRandomCombinedImpl ctxRetainedBaseReductionImpl
  change _ =
    (fun result => (result.1.1, result.1.2, result.2)) <$>
      (simulateQ modifiedNonceAeadINDDollarRandomImpl
        ((ctxRetainedBaseSealOracle input).run state)).run
          (ctxIndependentTagStateToModifiedNonceAead state)
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxPrivacyIdealSealOracle ctxRetainedBaseSealOracle
    simp [StateT.run, hused]
    rfl
  · unfold ctxPrivacyIdealSealOracle ctxRetainedBaseSealOracle
    simp only [StateT.run, hused, if_false]
    rw [simulateQ_bind, simulateQ_queryModifiedNonceAeadSeal_random]
    change _ = _ <$>
      ((modifiedNonceAeadINDDollarRandomSealOracle
        (CtxSealInput.toModifiedNonceAeadSealInput input)).run
          (ctxIndependentTagStateToModifiedNonceAead state) >>= fun result => _)
    unfold modifiedNonceAeadINDDollarRandomSealOracle
    simp only [StateT.run, ctxIndependentTagStateToModifiedNonceAead,
      toModifiedNonceAeadSealInput_nonce, hused, if_false]
    simp only [bind_assoc, pure_bind]
    simp_rw [simulateQ_bind, simulateQ_modifiedNonceAeadDigest_random]
    simp_rw [simulateQ_pure]
    simp only [bind_pure_comp]
    simp_rw [map_lift_ctxDigest_apply]
    simp only [map_bind, Functor.map_map]
    apply bind_congr
    intro body
    apply bind_congr
    intro tag
    apply congrArg (fun f : CtxDigest →
        Option CtxRomRecord ×
          (CtxIndependentTagState × ModifiedNonceAeadHandlerState) =>
      f <$> ($ᵗ CtxDigest))
    funext commit
    rfl

/-- Every explicit ideal CTX query projects to the flattened random IND$ execution. -/
theorem ctxPrivacyRandomCombinedImpl_projection
    (query : CtxAdversarySpec.Domain)
    (state : CtxIndependentTagState) :
    Prod.map id
        (fun next =>
          (next, ctxIndependentTagStateToModifiedNonceAead next)) <$>
        (ctxPrivacyIdealImpl query).run state =
      (ctxPrivacyRandomCombinedImpl query).run
        (state, ctxIndependentTagStateToModifiedNonceAead state) := by
  rcases query with query | input
  · exact ctxPrivacyRandomPublicOracle_projection query state
  · exact ctxPrivacyRandomSealOracle_projection input state

/-- The complete adaptive ideal execution is the exact source-state projection of the flattened random IND$ execution. -/
theorem ctxPrivacyRandomCombinedImpl_run_projection_of_main
    {output : Type} (main : OracleComp CtxAdversarySpec output) :
    Prod.map id
        (fun state =>
          (state, ctxIndependentTagStateToModifiedNonceAead state)) <$>
        (simulateQ ctxPrivacyIdealImpl main).run
          emptyCtxIndependentTagState =
      (simulateQ ctxPrivacyRandomCombinedImpl main).run
        (emptyCtxIndependentTagState,
          emptyModifiedNonceAeadHandlerState) := by
  simpa [ctxIndependentTagStateToModifiedNonceAead,
    emptyCtxIndependentTagState,
    emptyModifiedNonceAeadHandlerState] using
    OracleComp.map_run_simulateQ_eq_of_query_map_eq
      ctxPrivacyIdealImpl
      ctxPrivacyRandomCombinedImpl
      (fun state =>
        (state, ctxIndependentTagStateToModifiedNonceAead state))
      ctxPrivacyRandomCombinedImpl_projection
      main emptyCtxIndependentTagState

/-- Interpreting the Boolean view reduction against random IND$ yields the exact explicit ideal CTX transcript, including both private handler states. -/
theorem ctxPrivacyRandomNestedRun_eq_ideal_of_main
    {output : Type} (main : OracleComp CtxAdversarySpec output) :
    (simulateQ modifiedNonceAeadINDDollarRandomImpl
      ((simulateQ ctxRetainedBaseReductionImpl main).run
        emptyCtxIndependentTagState)).run
        emptyModifiedNonceAeadHandlerState =
      (fun result : output × CtxIndependentTagState =>
        ((result.1, result.2),
          ctxIndependentTagStateToModifiedNonceAead result.2)) <$>
        (simulateQ ctxPrivacyIdealImpl main).run
          emptyCtxIndependentTagState := by
  calc
    _ = (fun result : output ×
          (CtxIndependentTagState × ModifiedNonceAeadHandlerState) =>
          ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ ctxPrivacyRandomCombinedImpl main).run
          (emptyCtxIndependentTagState,
            emptyModifiedNonceAeadHandlerState) :=
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
        modifiedNonceAeadINDDollarRandomImpl
        ctxRetainedBaseReductionImpl main
        emptyCtxIndependentTagState
        emptyModifiedNonceAeadHandlerState
    _ = _ := by
      rw [← ctxPrivacyRandomCombinedImpl_run_projection_of_main main]
      simp only [Functor.map_map]
      apply congrArg (fun f :
          (output × CtxIndependentTagState) →
            ((output × CtxIndependentTagState) ×
              ModifiedNonceAeadHandlerState) =>
        f <$> (simulateQ ctxPrivacyIdealImpl main).run
          emptyCtxIndependentTagState)
      funext result
      rfl

/-- The view reduction's random IND$ experiment is definitionally the explicit ideal CTX privacy game after the exact nested-state projection. -/
theorem modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    modifiedNonceAeadINDDollarRandomExp
        (ctxPrivacyViewReduction adversary) =
      ctxPrivacyIdealGame adversary := by
  unfold modifiedNonceAeadINDDollarRandomExp
    ctxPrivacyViewReduction ctxPrivacyIdealGame
  simp only [simulateQ_map, StateT.run_map, bind_pure_comp,
    Functor.map_map]
  rw [ctxPrivacyRandomNestedRun_eq_ideal_of_main adversary.main]
  simp only [Functor.map_map]

/-- The view reduction's real IND$ experiment is exactly the direct independent-tag CTX privacy game. -/
theorem modifiedNonceAeadINDDollarRealExp_viewReduction_eq_directSampleGame
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    modifiedNonceAeadINDDollarRealExp c
        (ctxPrivacyViewReduction adversary) =
      ctxPrivacyDirectSampleGame c adversary := by
  unfold modifiedNonceAeadINDDollarRealExp
    ctxPrivacyViewReduction ctxPrivacyDirectSampleGame
    ctxPrivacyDirectSampleExpInner
  apply bind_congr
  intro key
  simp only [simulateQ_map, StateT.run_map, bind_pure_comp,
    Functor.map_map]
  rw [ctxRetainedBaseNestedRun_eq_direct_of_main
    c key adversary.main]
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.CtxComputationalPrivacy
