import BeaconcryptCore.Computational.CtxComputationalSecurity

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
  CtxNonceAeadIndDollarValidation CtxComputationalSecurity

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

/-- The view reduction's random IND$ experiment is exactly the explicit ideal CTX privacy game after the exact nested-state projection. -/
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

/-- Fixed-key public-prefix probability in the Boolean direct-sampling privacy execution. -/
noncomputable def ctxPrivacyDirectSamplePublicPrefixProbabilityInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ℝ≥0∞ :=
  Pr[fun result : Bool × CtxIndependentTagState =>
      ∃ input ∈ result.2.publicInputs, SecretPrefixQuery key input |
    (simulateQ (ctxDirectSampleIndependentTagImpl c key)
      adversary.main).run emptyCtxIndependentTagState]

/-- The independent Boolean privacy execution preserves the canonical prefix-event probability. -/
theorem ctxPrivacyIndependent_badProbability_eq_secretPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    Pr[fun result => result.2.2 = true |
      ctxPrivacyIndependentTagFlaggedExpInner c key adversary] =
      ctxPrivacySecretPrefixProbabilityInner c key adversary := by
  calc
    Pr[fun result => result.2.2 = true |
        ctxPrivacyIndependentTagFlaggedExpInner c key adversary] =
        Pr[fun result => result.2.2 = true |
          ctxPrivacySplitRoutedFlaggedExpInner c key adversary] :=
      (OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
        (ctxSplitRoutedWithPrefixFlagImpl c key)
        (ctxIndependentWithPrefixFlagImpl c key)
        (ctxSplitRouted_independent_agree_good c key)
        (ctxSplitRoutedWithPrefixFlagImpl_bad_mono c key)
        (ctxIndependentWithPrefixFlagImpl_bad_mono c key)
        adversary.main emptyCtxIndependentTagState).symm
    _ = ctxPrivacySecretPrefixProbabilityInner c key adversary :=
      ctxPrivacySplitRouted_badProbability_eq_secretPrefix
        c key adversary

/-- In the independent Boolean execution, the sticky flag is exactly the public trace event. -/
theorem ctxPrivacyIndependent_badProbability_eq_publicPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    Pr[fun result => result.2.2 = true |
      ctxPrivacyIndependentTagFlaggedExpInner c key adversary] =
      Pr[fun result : Bool × CtxIndependentTagState =>
          ∃ input ∈ result.2.publicInputs, SecretPrefixQuery key input |
        (simulateQ (ctxIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState] := by
  unfold ctxPrivacyIndependentTagFlaggedExpInner
  rw [← ctxIndependentWithPrefixFlagImpl_proj_run_of_main
    c key adversary.main, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  exact ctxIndependentTagFlagged_run_prefix_flag_of_main
    c key adversary.main result hresult

/-- The canonical fixed-key privacy prefix event is exactly the direct public-trace event. -/
theorem ctxPrivacySecretPrefixProbabilityInner_eq_directSamplePublicPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacySecretPrefixProbabilityInner c key adversary =
      ctxPrivacyDirectSamplePublicPrefixProbabilityInner
        c key adversary := by
  calc
    ctxPrivacySecretPrefixProbabilityInner c key adversary =
        Pr[fun result => result.2.2 = true |
          ctxPrivacyIndependentTagFlaggedExpInner c key adversary] :=
      (ctxPrivacyIndependent_badProbability_eq_secretPrefix
        c key adversary).symm
    _ = Pr[fun result : Bool × CtxIndependentTagState =>
          ∃ input ∈ result.2.publicInputs, SecretPrefixQuery key input |
        (simulateQ (ctxIndependentTagImpl c key)
          adversary.main).run emptyCtxIndependentTagState] :=
      ctxPrivacyIndependent_badProbability_eq_publicPrefix
        c key adversary
    _ = ctxPrivacyDirectSamplePublicPrefixProbabilityInner
          c key adversary := by
      unfold ctxPrivacyDirectSamplePublicPrefixProbabilityInner
      exact ctxIndependentPublicPrefixProbability_eq_directSample_of_main
        c key adversary.main

/-- Fixed-key direct privacy experiment returning whether the bounded probe vector hits the key. -/
noncomputable def ctxPrivacyDirectSamplePrefixProbeExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := by
  classical
  exact do
    let result ←
      (simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState
    pure (decide (CtxKeyProbeHit key
      (ctxPrefixProbeVector qH result.2.publicInputs)))

/-- Under the public-query bound, direct privacy probe success is exactly the direct public-prefix event. -/
theorem ctxPrivacyDirectSamplePrefixProbeExpInner_probability
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    Pr[= true |
      ctxPrivacyDirectSamplePrefixProbeExpInner c key adversary] =
      ctxPrivacyDirectSamplePublicPrefixProbabilityInner
        c key adversary := by
  classical
  unfold ctxPrivacyDirectSamplePrefixProbeExpInner
    ctxPrivacyDirectSamplePublicPrefixProbabilityInner
  rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  simpa [Function.comp_def] using
    (ctxPrefixProbeVector_hit_iff_of_length_le
      result.2.publicInputs key
      (ctxDirectSampleIndependentTag_run_publicInputs_length_le_qH_of_main
        c key adversary.main adversary.publicQueryBound result hresult))

/-- Uniform-key direct Boolean privacy prefix-probe experiment. -/
noncomputable def ctxPrivacyDirectSamplePrefixProbeExp
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxPrivacyDirectSamplePrefixProbeExpInner c key adversary

/-- The canonical privacy prefix probability is exactly the direct bounded-probe experiment. -/
theorem ctxPrivacySecretPrefixProbability_eq_directSampleProbe
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacySecretPrefixProbability c adversary =
      Pr[= true |
        ctxPrivacyDirectSamplePrefixProbeExp c adversary] := by
  classical
  unfold ctxPrivacySecretPrefixProbability
    ctxPrivacyRealFlaggedGame
    ctxPrivacyDirectSamplePrefixProbeExp
  rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro key
  congr 1
  rw [ctxPrivacyDirectSamplePrefixProbeExpInner_probability]
  exact ctxPrivacySecretPrefixProbabilityInner_eq_directSamplePublicPrefix
    c key adversary

/-- Privacy-native key-probe reduction retaining only bounded public key candidates. -/
noncomputable def ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    ModifiedNonceAeadINDDollarProbeAdversary qH where
  main := (fun result =>
      ctxPrefixProbeVector qH result.2.publicInputs) <$>
    (simulateQ ctxRetainedBaseReductionImpl adversary.main).run
      emptyCtxIndependentTagState

/-- The privacy key-probe reduction forwards at most the source's `qE` primitive seals. -/
theorem ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary).MakesAtMostSealQueries
      qE := by
  unfold ModifiedNonceAeadINDDollarProbeAdversary.MakesAtMostSealQueries
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact adversary.sealQueryBound.simulateQ_run_StateT_of_step
    ctxRetainedBaseReductionImpl_seal_query_bound_step
    emptyCtxIndependentTagState

/-- At fixed key, the real primitive probe reduction is exactly the direct Boolean privacy probe. -/
theorem ctxPrivacyPrefixReduction_realProbeExpInner_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    modifiedNonceAeadINDDollarRealProbeExpInner c key
        (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary) =
      ctxPrivacyDirectSamplePrefixProbeExpInner
        c key adversary := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExpInner
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
    ctxPrivacyDirectSamplePrefixProbeExpInner
  simp only [simulateQ_map, StateT.run_map, bind_pure_comp,
    Functor.map_map]
  rw [ctxRetainedBaseNestedRun_eq_direct_of_main
    c key adversary.main]
  rw [Functor.map_map]

/-- The complete real privacy key-probe reduction equals the direct probe experiment. -/
theorem modifiedNonceAeadINDDollarRealProbeExp_privacyReduction_eq_directSample
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    modifiedNonceAeadINDDollarRealProbeExp c
        (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary) =
      ctxPrivacyDirectSamplePrefixProbeExp c adversary := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExp
    ctxPrivacyDirectSamplePrefixProbeExp
  apply bind_congr
  intro key
  change modifiedNonceAeadINDDollarRealProbeExpInner c key
      (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary) = _
  exact ctxPrivacyPrefixReduction_realProbeExpInner_eq_directSample
    c key adversary

/-- The canonical privacy prefix event is exactly real privacy key-probe success. -/
theorem ctxPrivacySecretPrefixProbability_eq_realProbeReduction
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacySecretPrefixProbability c adversary =
      Pr[= true |
        modifiedNonceAeadINDDollarRealProbeExp c
          (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
            adversary)] := by
  rw [ctxPrivacySecretPrefixProbability_eq_directSampleProbe]
  rw [modifiedNonceAeadINDDollarRealProbeExp_privacyReduction_eq_directSample]

/-- Privacy prefix bound with one specialized probe IND$ charge and exact `qH / 2^256` guessing loss. -/
theorem ctxPrivacySecretPrefixProbability_le_probeINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ctxPrivacySecretPrefixProbability c adversary ≤
      ENNReal.ofReal
        (modifiedNonceAeadINDDollarProbeAdvantage c
          (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
            adversary)) +
      (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ := by
  let reduction :=
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary
  calc
    ctxPrivacySecretPrefixProbability c adversary =
        Pr[= true |
          modifiedNonceAeadINDDollarRealProbeExp c reduction] := by
      exact ctxPrivacySecretPrefixProbability_eq_realProbeReduction
        c adversary
    _ ≤ Pr[= true |
          modifiedNonceAeadINDDollarRandomProbeExp reduction] +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c reduction) := by
      exact ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        (modifiedNonceAeadINDDollarRealProbeExp c reduction)
        (modifiedNonceAeadINDDollarRandomProbeExp reduction)
    _ ≤ (qH : ℝ≥0∞) * (Fintype.card CtxKey : ℝ≥0∞)⁻¹ +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c reduction) := by
      gcongr
      exact modifiedNonceAeadINDDollarRandomProbe_le reduction
    _ = ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c reduction) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [ctxKey_card, add_comm]

/-- Privacy-native conventional IND$ reduction validating bounded key candidates with one fresh seal. -/
noncomputable def ctxPrivacyPrefixToBooleanINDDollarReduction
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ModifiedNonceAeadINDDollarAdversary := by
  classical
  exact
    { main := do
        let result ←
          (simulateQ ctxRetainedBaseReductionImpl adversary.main).run
            emptyCtxIndependentTagState
        let probes := ctxPrefixProbeVector qH result.2.publicInputs
        let nonce := chooseFreshCtxNonce result.2.usedNonces
        let response ← queryModifiedNonceAeadSeal (ctxValidationInput nonce)
        pure (ctxValidationAccept c nonce probes response) }

/-- The privacy validation reduction makes at most `qE + 1` primitive sealing queries. -/
theorem ctxPrivacyPrefixToBooleanINDDollarReduction_seal_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery (qE + 1) := by
  unfold ctxPrivacyPrefixToBooleanINDDollarReduction
  refine OracleComp.isQueryBoundP_bind (n := qE) (m := 1) ?_ ?_
  · exact adversary.sealQueryBound.simulateQ_run_StateT_of_step
      ctxRetainedBaseReductionImpl_seal_query_bound_step
      emptyCtxIndependentTagState
  · intro result _
    simp only
    unfold queryModifiedNonceAeadSeal
    refine OracleComp.isQueryBoundP_bind (n := 1) (m := 0) ?_ ?_
    · exact (OracleComp.isQueryBoundP_query_iff
        (spec := ModifiedNonceAeadAdversarySpec)
        (p := IsModifiedNonceAeadSealQuery)
        (.inr (ctxValidationInput
          (chooseFreshCtxNonce result.2.usedNonces))) 1).2
          (fun _ => by omega)
    · intro response _
      cases response <;> simp

/-- Random-world validation success for the privacy reduction costs at most `qH / 2^128`. -/
theorem ctxPrivacyPrefixBooleanReduction_random_le
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    Pr[= true |
      modifiedNonceAeadINDDollarRandomExp
        (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)] ≤
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold modifiedNonceAeadINDDollarRandomExp
    ctxPrivacyPrefixToBooleanINDDollarReduction
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [← probEvent_eq_eq_probOutput]
  simp_rw [simulateQ_queryModifiedNonceAeadSeal_random]
  simp_rw [simulateQ_pure, StateT.run_pure]
  simp only [pure_bind]
  refine probEvent_bind_le_of_forall_le
    (mx := (simulateQ modifiedNonceAeadINDDollarRandomImpl
      ((simulateQ ctxRetainedBaseReductionImpl adversary.main).run
        emptyCtxIndependentTagState)).run
          emptyModifiedNonceAeadHandlerState) ?_
  rintro ⟨⟨decision, state⟩, primitiveState⟩ _
  simpa [probEvent_eq_eq_probOutput] using
    (randomValidationContinuation_le c
      (chooseFreshCtxNonce state.usedNonces)
      (ctxPrefixProbeVector qH state.publicInputs) primitiveState)

/-- Fixed-key direct privacy probe success is contained in real validation success. -/
theorem ctxPrivacyDirectProbe_le_booleanRealInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    Pr[= true |
      ctxPrivacyDirectSamplePrefixProbeExpInner c key adversary] ≤
      Pr[= true |
        modifiedNonceAeadINDDollarRealExpInner c key
          (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)] := by
  unfold ctxPrivacyDirectSamplePrefixProbeExpInner
    modifiedNonceAeadINDDollarRealExpInner
    ctxPrivacyPrefixToBooleanINDDollarReduction
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [ctxRetainedBaseNestedRun_eq_direct_of_main
    c key adversary.main]
  simp_rw [simulateQ_queryModifiedNonceAeadSeal,
    simulateQ_pure, StateT.run_pure]
  simp only [pure_bind]
  rw [← bind_pure_comp]
  simp only [bind_assoc, pure_bind]
  refine probOutput_bind_mono ?_
  intro result hresult
  by_cases hhit : CtxKeyProbeHit key
      (ctxPrefixProbeVector qH result.2.publicInputs)
  · have hfresh := chooseFreshCtxNonce_fresh_of_direct_support_of_main
      c key adversary.main adversary.sealQueryBound hqE result hresult
    rw [modifiedNonceAeadSealOracle_validation_run_of_fresh
      c key (chooseFreshCtxNonce result.2.usedNonces)
      (ctxIndependentTagStateToModifiedNonceAead result.2) hfresh]
    simp only [pure_bind]
    have haccept := keyProbeHit_implies_realValidationCiphertextHit
      c key (chooseFreshCtxNonce result.2.usedNonces)
      (ctxPrefixProbeVector qH result.2.publicInputs) hhit
    simp [hhit, ctxValidationAccept, haccept]
  · simp [hhit]

/-- The canonical privacy prefix event is contained in real conventional validation success. -/
theorem ctxPrivacySecretPrefixProbability_le_booleanReal
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ctxPrivacySecretPrefixProbability c adversary ≤
      Pr[= true |
        modifiedNonceAeadINDDollarRealExp c
          (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)] := by
  rw [ctxPrivacySecretPrefixProbability_eq_directSampleProbe]
  unfold ctxPrivacyDirectSamplePrefixProbeExp
    modifiedNonceAeadINDDollarRealExp
  refine probOutput_bind_mono ?_
  intro key _
  change Pr[= true |
      ctxPrivacyDirectSamplePrefixProbeExpInner c key adversary] ≤
    Pr[= true |
      modifiedNonceAeadINDDollarRealExpInner c key
        (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)]
  exact ctxPrivacyDirectProbe_le_booleanRealInner
    c key adversary hqE

/-- Conventional Boolean IND$ bound for the privacy prefix event with exact `qH / 2^128` validation loss. -/
theorem ctxPrivacySecretPrefixProbability_le_booleanINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ctxPrivacySecretPrefixProbability c adversary ≤
      ENNReal.ofReal
        (modifiedNonceAeadINDDollarAdvantage c
          (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)) +
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  let reduction :=
    ctxPrivacyPrefixToBooleanINDDollarReduction c adversary
  calc
    ctxPrivacySecretPrefixProbability c adversary ≤
        Pr[= true |
          modifiedNonceAeadINDDollarRealExp c reduction] := by
      exact ctxPrivacySecretPrefixProbability_le_booleanReal
        c adversary hqE
    _ ≤ Pr[= true |
          modifiedNonceAeadINDDollarRandomExp reduction] +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c reduction) := by
      exact ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        (modifiedNonceAeadINDDollarRealExp c reduction)
        (modifiedNonceAeadINDDollarRandomExp reduction)
    _ ≤ (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c reduction) := by
      gcongr
      exact ctxPrivacyPrefixBooleanReduction_random_le c adversary
    _ = ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c reduction) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [add_comm]

/-- Structural modified-CTX privacy bound: one view IND$ advantage plus one public-prefix event. -/
theorem ofReal_ctxPrivacyAdvantage_le_viewAdvantage_add_secretPrefix
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
      ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyViewReduction adversary)) +
        ctxPrivacySecretPrefixProbability c adversary := by
  have hdirect :
      (ctxPrivacyRealGame c adversary).boolDistAdvantage
          (ctxPrivacyDirectSampleGame c adversary) ≤
        (ctxPrivacySecretPrefixProbability c adversary).toReal := by
    refine (show
      |(Pr[= true | ctxPrivacyRealGame c adversary]).toReal -
        (Pr[= true |
          ctxPrivacyDirectSampleGame c adversary]).toReal| ≤
          tvDist (ctxPrivacyRealGame c adversary)
            (ctxPrivacyDirectSampleGame c adversary) from ?_).trans ?_
    · exact abs_probOutput_toReal_sub_le_tvDist _ _
    · exact tvDist_ctxPrivacyRealGame_directSample_le_secretPrefix
        c adversary
  have hview :
      (ctxPrivacyDirectSampleGame c adversary).boolDistAdvantage
          (ctxPrivacyIdealGame adversary) =
        modifiedNonceAeadINDDollarAdvantage c
          (ctxPrivacyViewReduction adversary) := by
    unfold modifiedNonceAeadINDDollarAdvantage
    rw [modifiedNonceAeadINDDollarRealExp_viewReduction_eq_directSampleGame,
      modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame]
  have hreal :
      ctxPrivacyAdvantage c adversary ≤
        modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyViewReduction adversary) +
          (ctxPrivacySecretPrefixProbability c adversary).toReal := by
    unfold ctxPrivacyAdvantage
    calc
      _ ≤ (ctxPrivacyRealGame c adversary).boolDistAdvantage
            (ctxPrivacyDirectSampleGame c adversary) +
          (ctxPrivacyDirectSampleGame c adversary).boolDistAdvantage
            (ctxPrivacyIdealGame adversary) :=
        ProbComp.boolDistAdvantage_triangle _ _ _
      _ ≤ (ctxPrivacySecretPrefixProbability c adversary).toReal +
          (ctxPrivacyDirectSampleGame c adversary).boolDistAdvantage
            (ctxPrivacyIdealGame adversary) :=
        add_le_add hdirect (le_refl _)
      _ = _ := by rw [hview, add_comm]
  have hprefix_ne_top :
      ctxPrivacySecretPrefixProbability c adversary ≠ ∞ := by
    unfold ctxPrivacySecretPrefixProbability
    exact probEvent_ne_top
  calc
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
              (ctxPrivacyViewReduction adversary) +
            (ctxPrivacySecretPrefixProbability c adversary).toReal) :=
      ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyViewReduction adversary)) +
        ENNReal.ofReal
          (ctxPrivacySecretPrefixProbability c adversary).toReal :=
      ENNReal.ofReal_add_le
    _ = _ := by
      rw [ENNReal.ofReal_toReal hprefix_ne_top]

/-- Specialized privacy capstone with distinct view and hidden-key-probe IND$ reductions. -/
theorem ctxPrivacyAdvantage_le_viewINDDollar_add_probeINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
      ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyViewReduction adversary)) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarProbeAdvantage c
            (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
              adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
        ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c
              (ctxPrivacyViewReduction adversary)) +
          ctxPrivacySecretPrefixProbability c adversary :=
      ofReal_ctxPrivacyAdvantage_le_viewAdvantage_add_secretPrefix
        c adversary
    _ ≤ ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c
              (ctxPrivacyViewReduction adversary)) +
          (ENNReal.ofReal
              (modifiedNonceAeadINDDollarProbeAdvantage c
                (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
                  adversary)) +
            (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹) :=
      add_le_add_right
        (ctxPrivacySecretPrefixProbability_le_probeINDDollar
          c adversary) _
    _ = _ := by ac_rfl

/-- Conventional privacy capstone with distinct view and fresh-nonce validation IND$ reductions. -/
theorem ctxPrivacyAdvantage_le_viewINDDollar_add_booleanINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
      ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyViewReduction adversary)) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    ENNReal.ofReal (ctxPrivacyAdvantage c adversary) ≤
        ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c
              (ctxPrivacyViewReduction adversary)) +
          ctxPrivacySecretPrefixProbability c adversary :=
      ofReal_ctxPrivacyAdvantage_le_viewAdvantage_add_secretPrefix
        c adversary
    _ ≤ ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c
              (ctxPrivacyViewReduction adversary)) +
          (ENNReal.ofReal
              (modifiedNonceAeadINDDollarAdvantage c
                (ctxPrivacyPrefixToBooleanINDDollarReduction
                  c adversary)) +
            (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹) :=
      add_le_add_right
        (ctxPrivacySecretPrefixProbability_le_booleanINDDollar
          c adversary hqE) _
    _ = _ := by ac_rfl

/-- Separate privacy query budgets give the exact combined source-query cap. -/
theorem CtxPrivacyAdversary.totalQueryBound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    adversary.main.IsTotalQueryBound (qH + qE) :=
  isTotalQueryBound_of_ctx_public_and_seal_bounds
    adversary.publicQueryBound adversary.sealQueryBound

/-- The privacy view reduction forwards at most the source's `qE` primitive seals. -/
theorem ctxPrivacyViewReduction_seal_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyViewReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery qE := by
  unfold ctxPrivacyViewReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact ctxRetainedBaseReduction_seal_query_bound_of_main
    adversary.sealQueryBound

/-- The privacy view reduction uses at most 64 uniform-byte calls per source query. -/
theorem ctxPrivacyViewReduction_uniform_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyViewReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery (64 * (qH + qE)) := by
  unfold ctxPrivacyViewReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact ctxRetainedBaseReduction_uniform_query_bound_of_main
    adversary.publicQueryBound adversary.sealQueryBound

/-- The privacy view reduction makes at most `64qH + 65qE` total primitive-interface calls. -/
theorem ctxPrivacyViewReduction_total_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyViewReduction adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE) := by
  unfold ctxPrivacyViewReduction
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  exact ctxRetainedBaseReduction_total_query_bound_of_main
    adversary.publicQueryBound adversary.sealQueryBound

/-- The privacy key-probe reduction uses at most 64 uniform-byte calls per source query. -/
theorem ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery (64 * (qH + qE)) := by
  unfold ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact ctxRetainedBaseReduction_uniform_query_bound_of_main
    adversary.publicQueryBound adversary.sealQueryBound

/-- The privacy key-probe reduction makes at most `64qH + 65qE` total primitive-interface calls. -/
theorem ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE) := by
  unfold ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  exact ctxRetainedBaseReduction_total_query_bound_of_main
    adversary.publicQueryBound adversary.sealQueryBound

/-- The privacy validation reduction adds no uniform-byte calls beyond the retained-base simulation. -/
theorem ctxPrivacyPrefixToBooleanINDDollarReduction_uniform_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery (64 * (qH + qE)) := by
  unfold ctxPrivacyPrefixToBooleanINDDollarReduction
  refine OracleComp.isQueryBoundP_bind
    (n := 64 * (qH + qE)) (m := 0) ?_ ?_
  · exact ctxRetainedBaseReduction_uniform_query_bound_of_main
      adversary.publicQueryBound adversary.sealQueryBound
  · intro result _
    simp only
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
      (queryModifiedNonceAeadSeal_no_uniform_queries
        (ctxValidationInput (chooseFreshCtxNonce result.2.usedNonces)))
      (fun _ _ => by trivial)

/-- The extra validation seal gives the privacy validation reduction total `64qH + 65qE + 1`. -/
theorem ctxPrivacyPrefixToBooleanINDDollarReduction_total_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE + 1) := by
  have htotal := isTotalQueryBound_of_modified_uniform_and_seal_bounds
    (ctxPrivacyPrefixToBooleanINDDollarReduction_uniform_query_bound
      c adversary)
    (ctxPrivacyPrefixToBooleanINDDollarReduction_seal_query_bound
      c adversary)
  exact htotal.mono (by omega)

/-- Complete source and reduction-side privacy query accounting.
The fixed reduction-side bounds count public-ROM and honest 64-byte outer-commitment randomness.
They exclude challenger-private variable-length body and 16-byte tag samples; bounding the complete ideal experiment also requires a plaintext-byte budget.
-/
structure CtxPrivacyQueryAccounting (c : Pqxdh.Crypto)
    {qH qE : ℕ} (adversary : CtxPrivacyAdversary qH qE) : Prop where
  sourceTotal : adversary.main.IsTotalQueryBound (qH + qE)
  viewSeals :
    (ctxPrivacyViewReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery qE
  viewUniform :
    (ctxPrivacyViewReduction adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery (64 * (qH + qE))
  viewTotal :
    (ctxPrivacyViewReduction adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE)
  probeSeals :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
      adversary).MakesAtMostSealQueries qE
  probeUniform :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
      adversary).main.IsQueryBoundP
        IsModifiedNonceAeadUniformQuery (64 * (qH + qE))
  probeTotal :
    (ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction
      adversary).main.IsTotalQueryBound (64 * qH + 65 * qE)
  validationSeals :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery (qE + 1)
  validationUniform :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery (64 * (qH + qE))
  validationTotal :
    (ctxPrivacyPrefixToBooleanINDDollarReduction c adversary).main.IsTotalQueryBound
      (64 * qH + 65 * qE + 1)

/-- Every bounded Boolean privacy adversary satisfies the complete reduction accounting record. -/
theorem ctxPrivacy_query_accounting
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxPrivacyAdversary qH qE) :
    CtxPrivacyQueryAccounting c adversary where
  sourceTotal := adversary.totalQueryBound
  viewSeals := ctxPrivacyViewReduction_seal_query_bound adversary
  viewUniform := ctxPrivacyViewReduction_uniform_query_bound adversary
  viewTotal := ctxPrivacyViewReduction_total_query_bound adversary
  probeSeals :=
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound
      adversary
  probeUniform :=
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_uniform_query_bound
      adversary
  probeTotal :=
    ctxPrivacyPrefixToModifiedNonceAeadINDDollarReduction_total_query_bound
      adversary
  validationSeals :=
    ctxPrivacyPrefixToBooleanINDDollarReduction_seal_query_bound
      c adversary
  validationUniform :=
    ctxPrivacyPrefixToBooleanINDDollarReduction_uniform_query_bound
      c adversary
  validationTotal :=
    ctxPrivacyPrefixToBooleanINDDollarReduction_total_query_bound
      c adversary

/--
info: 'BeaconcryptCore.Computational.CtxComputationalPrivacy.modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms modifiedNonceAeadINDDollarRandomExp_viewReduction_eq_idealGame

/--
info: 'BeaconcryptCore.Computational.CtxComputationalPrivacy.ctxPrivacyAdvantage_le_viewINDDollar_add_probeINDDollar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ctxPrivacyAdvantage_le_viewINDDollar_add_probeINDDollar

/--
info: 'BeaconcryptCore.Computational.CtxComputationalPrivacy.ctxPrivacyAdvantage_le_viewINDDollar_add_booleanINDDollar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ctxPrivacyAdvantage_le_viewINDDollar_add_booleanINDDollar

end BeaconcryptCore.Computational.CtxComputationalPrivacy
