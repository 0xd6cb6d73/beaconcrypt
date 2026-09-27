import BeaconcryptCore.Computational.CtxComputationalSecurity

/-!
# Modified CTX acceptance without an adversarial plaintext claim

The target contains only nonce, context and protected record. The actual optional opening is challenger-owned. Existing cache, retained-base and prefix reductions are reused through a public constant compatibility field, which no new winning event reads.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxUnclaimedAcceptance

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags CtxHonestTagSampling
  CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation CtxComputationalSecurity

/-- A ciphertext-only adversarial target; no proposed or recovered plaintext is supplied. -/
structure Target where
  nonce : CtxNonce
  context : CtxRecordContext
  record : CtxRomRecord

/-- Existing transcript machinery carries a public empty compatibility field, never a recovered plaintext. -/
def Target.toLegacy (target : Target) : CtxAliasTarget :=
  ⟨target.nonce, target.context, target.record, []⟩

structure Adversary where
  main : OracleComp CtxAdversarySpec Target

def Adversary.toLegacy (adversary : Adversary) : CtxAdversary :=
  ⟨Target.toLegacy <$> adversary.main⟩

/-- The genuine opening result after the actual outer commitment comparison. -/
def optionalOpen (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (expected : CtxDigest) : Option Pqxdh.Bytes :=
  if before.target.record.commit = expected then
    c.aeadOpen before.key.toList before.target.nonce.toList before.target.context.ad.bytes
      before.target.record.body before.target.record.tag
  else none

/-- The one-key retained branch is precisely the existing ordinary primitive winning event. -/
def RetainedWin (c : Pqxdh.Crypto) (before : CtxBeforeVerify) : Prop :=
  ModifiedNonceAeadINTCTXTWin c (ctxBeforeVerifyToModifiedNonceAead before)

/-- An alias charge needs only the outer commitment equality; dropping the opening requirement is an upper bound. -/
def AliasWin (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  CtxFullAliasShape before ∧ before.target.record.commit = expected

def ClassifiedAt (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  RetainedWin c before ∨ AliasWin before expected

/-- Full tuple freshness and actual optional opening, without consulting the legacy compatibility field. -/
def AcceptedAt (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (expected : CtxDigest) : Prop :=
  CtxTypedFullFresh before ∧ optionalOpen c before expected ≠ none

/-- The optional plaintext is exactly the challenger's output, subject to commitment validation. -/
theorem acceptedAt_iff (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (expected : CtxDigest) :
    AcceptedAt c before expected ↔ CtxTypedFullFresh before ∧
      before.target.record.commit = expected ∧
      c.aeadOpen before.key.toList before.target.nonce.toList before.target.context.ad.bytes
        before.target.record.body before.target.record.tag ≠ none := by
  by_cases equal : before.target.record.commit = expected <;> simp [AcceptedAt, optionalOpen, equal]

theorem acceptedAt_implies_classified_of_cache_sound
    (c : Pqxdh.Crypto) (before : CtxBeforeVerify) (cache next : SplitCache)
    (expected : CtxDigest)
    (hsound : CtxHonestCommitmentsCached before cache)
    (horacle : (expected, next) ∈ support
      (ctxKeyFreeSuffixStep
        (outerSuffix before.target.nonce before.target.context
          before.target.record.tag) cache))
    (haccepted : AcceptedAt c before expected) :
    ClassifiedAt c before expected := by
  classical
  have haccepted := (acceptedAt_iff c before expected).mp haccepted
  unfold ClassifiedAt
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
      haccepted.2.1⟩


/-- Final classified verifier over the key-free suffix cache. -/
noncomputable def classifiedVerifier (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × SplitCache) : ProbComp Bool := by
  classical
  exact do
    let suffix := outerSuffix result.1.target.nonce result.1.target.context
      result.1.target.record.tag
    let oracleResult ← ctxKeyFreeSuffixStep suffix result.2
    pure (decide (ClassifiedAt c result.1 oracleResult.1))

/-- Canonical split-cache classified modified-CTX game. -/
noncomputable def classifiedGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxSplitBeforeVerifyGame c adversary >>= classifiedVerifier c

/-- Direct independent-tag classified modified-CTX game. -/
noncomputable def directClassifiedGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxDirectSampleIndependentTagGame c adversary >>= classifiedVerifier c

/-- Final verifier for the actual typed full-fresh event. -/
noncomputable def acceptedVerifier (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × SplitCache) : ProbComp Bool := by
  classical
  exact do
    let suffix := outerSuffix result.1.target.nonce result.1.target.context
      result.1.target.record.tag
    let oracleResult ← ctxKeyFreeSuffixStep suffix result.2
    pure (decide (AcceptedAt c result.1 oracleResult.1))

/-- Canonical split-cache game for actual typed full-fresh modified-CTX acceptance. -/
noncomputable def acceptedGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxSplitBeforeVerifyGame c adversary >>= acceptedVerifier c

/-- Direct independent-tag game for actual typed full-fresh modified-CTX acceptance. -/
noncomputable def directAcceptedGame (c : Pqxdh.Crypto)
    (adversary : CtxAdversary) : ProbComp Bool :=
  ctxDirectSampleIndependentTagGame c adversary >>=
    acceptedVerifier c

/-- The classified verifier pays one inverse digest factor off the retained-base branch. -/
theorem classifiedVerifier_le_inv_of_direct_support
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (target : CtxAliasTarget) (state : CtxIndependentTagState)
    (hresult : (target, state) ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState))
    (hnotRetained : ¬ RetainedWin c
      (independentHandlerStateToBeforeVerify key target state)) :
    Pr[= true | classifiedVerifier c
      (independentTrackedProjection key (target, state))] ≤
        (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  by_cases halias : CtxFullAliasShape
    (independentHandlerStateToBeforeVerify key target state)
  · have hfresh := ctxDirectSample_alias_suffix_fresh
      c key adversary target state hresult halias
    unfold classifiedVerifier
    simp only [independentTrackedProjection,
      independentHandlerStateToBeforeVerify]
    unfold ctxKeyFreeSuffixStep
    rw [hfresh]
    simp only [bind_assoc, pure_bind]
    rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
    refine (probEvent_mono''
      (q := fun x : CtxDigest => x = target.record.commit) ?_).trans ?_
    · intro expected haccepted
      simp only [Function.comp_apply] at haccepted
      have hclassified := @of_decide_eq_true _ (Classical.propDecidable _) haccepted
      unfold ClassifiedAt at hclassified
      rcases hclassified with hretained | haliasAccepted
      · exact (hnotRetained hretained).elim
      · exact haliasAccepted.2.symm
    · rw [probEvent_eq_eq_probOutput,
        probOutput_uniformSample CtxDigest target.record.commit]
  · unfold classifiedVerifier
    unfold independentHandlerStateToBeforeVerify at hnotRetained halias
    simp only [independentTrackedProjection,
      independentHandlerStateToBeforeVerify]
    simp [ClassifiedAt, AliasWin,
      hnotRetained, halias]


/-- On a cache-sound transcript, typed full-fresh verification is contained in the classified verifier. -/
theorem acceptedVerifier_le_classified_of_cache_sound
    (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache)
    (hsound : CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | acceptedVerifier c result] ≤
      Pr[= true | classifiedVerifier c result] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  unfold acceptedVerifier classifiedVerifier
  simp only [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  intro oracleResult horacle haccepted
  simp only [Function.comp_apply, decide_eq_true_eq] at haccepted ⊢
  exact acceptedAt_implies_classified_of_cache_sound
    c result.1 result.2 oracleResult.2 oracleResult.1 hsound horacle haccepted

/-- A cache-sound direct pre-verification distribution lifts the pointwise typed-to-classified bridge. -/
theorem directAcceptedGame_le_classified_of_cache_sound
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (hsound : ∀ result ∈ support
      (ctxDirectSampleIndependentTagGame c adversary),
      CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | directAcceptedGame c adversary] ≤
      Pr[= true | directClassifiedGame c adversary] := by
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  unfold directAcceptedGame
    directClassifiedGame
  apply probEvent_bind_mono
  intro result hresult
  simpa [probEvent_eq_eq_probOutput] using
    (acceptedVerifier_le_classified_of_cache_sound
      c result (hsound result hresult))

/-- The direct classified game is bounded by retained-base integrity plus one fresh digest. -/
theorem directClassifiedGame_le_retained_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | directClassifiedGame c adversary] ≤
      Pr[fun result : CtxBeforeVerify × SplitCache =>
          RetainedWin c result.1 |
        ctxDirectSampleIndependentTagGame c adversary] +
      (Fintype.card CtxDigest : ℝ≥0∞)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput]
  unfold directClassifiedGame
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
    (classifiedVerifier_le_inv_of_direct_support
      c key adversary target state hsource hnotRetained)


/-- The actual typed full-fresh game pays the same single canonical-to-direct prefix charge. -/
theorem acceptedGame_le_direct_add_prefix
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | acceptedGame c adversary] ≤
      Pr[= true | directAcceptedGame c adversary] +
        ctxSecretPrefixQueriedProbability c adversary := by
  have htv : tvDist (acceptedGame c adversary)
      (directAcceptedGame c adversary) ≤
      (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    unfold acceptedGame
      directAcceptedGame
    exact (tvDist_bind_right_le (acceptedVerifier c)
      (ctxSplitBeforeVerifyGame c adversary)
      (ctxDirectSampleIndependentTagGame c adversary)).trans
        (tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried
          c adversary)
  have hdiff := abs_probOutput_toReal_sub_le_tvDist
    (acceptedGame c adversary)
    (directAcceptedGame c adversary)
  have hadv :
      (acceptedGame c adversary).boolDistAdvantage
          (directAcceptedGame c adversary) ≤
        (ctxSecretPrefixQueriedProbability c adversary).toReal := by
    simpa [ProbComp.boolDistAdvantage] using hdiff.trans htv
  calc
    Pr[= true | acceptedGame c adversary] ≤
        Pr[= true | directAcceptedGame c adversary] +
          ENNReal.ofReal
            ((acceptedGame c adversary).boolDistAdvantage
              (directAcceptedGame c adversary)) :=
      ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _ _
    _ ≤ Pr[= true | directAcceptedGame c adversary] +
          ENNReal.ofReal
            (ctxSecretPrefixQueriedProbability c adversary).toReal := by
      gcongr
    _ = Pr[= true | directAcceptedGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary := by
      have hprefix : ctxSecretPrefixQueriedProbability c adversary ≠ ⊤ := by
        unfold ctxSecretPrefixQueriedProbability
        exact probEvent_ne_top
      rw [ENNReal.ofReal_toReal hprefix]


/-- Exact retained-base reduction equality applies to acceptance of any optional plaintext. -/
theorem retainedProbability_eq_intctxtAdvantage (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[fun result : CtxBeforeVerify × SplitCache => RetainedWin c result.1 |
      ctxDirectSampleIndependentTagGame c adversary] =
      modifiedNonceAeadINTCTXTAdvantage c (ctxRetainedBaseReduction adversary) := by
  unfold modifiedNonceAeadINTCTXTAdvantage
  rw [modifiedNonceAeadINTCTXTGame_reduction_eq_direct, probEvent_map]
  rfl

/-- Actual typed full-fresh security follows from the classified core whenever direct honest cache values are sound. -/
theorem acceptedProbability_le_intCtxt_add_prefix_add_inv_of_cache_sound
    (c : Pqxdh.Crypto) (adversary : CtxAdversary)
    (hsound : ∀ result ∈ support
      (ctxDirectSampleIndependentTagGame c adversary),
      CtxHonestCommitmentsCached result.1 result.2) :
    Pr[= true | acceptedGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true | acceptedGame c adversary] ≤
        Pr[= true | directAcceptedGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary :=
      acceptedGame_le_direct_add_prefix c adversary
    _ ≤ Pr[= true | directClassifiedGame c adversary] +
          ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact directAcceptedGame_le_classified_of_cache_sound
        c adversary hsound
    _ ≤ (Pr[fun result : CtxBeforeVerify × SplitCache =>
            RetainedWin c result.1 |
          ctxDirectSampleIndependentTagGame c adversary] +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact directClassifiedGame_le_retained_add_inv c adversary
    _ ≤ (modifiedNonceAeadINTCTXTAdvantage c
            (ctxRetainedBaseReduction adversary) +
          (Fintype.card CtxDigest : ℝ≥0∞)⁻¹) +
        ctxSecretPrefixQueriedProbability c adversary := by
      gcongr
      exact (retainedProbability_eq_intctxtAdvantage c adversary).le
    _ = modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [ctxDigest_card]
      ac_rfl

/-- Unconditional actual typed full-fresh core bound from the reachable direct cache invariant. -/
theorem acceptedProbability_le_intCtxt_add_prefix_add_inv
    (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    Pr[= true | acceptedGame c adversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary) +
        ctxSecretPrefixQueriedProbability c adversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  exact acceptedProbability_le_intCtxt_add_prefix_add_inv_of_cache_sound
    c adversary (ctxDirectSampleIndependentTagGame_commitmentsCached
      c adversary)


/-- The challenger returns its actual optional opening and retains the final ROM cache. -/
noncomputable def openAndRetain (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × SplitCache) : ProbComp (Option Pqxdh.Bytes × SplitCache) := do
  let oracleResult ← ctxKeyFreeSuffixStep
    (outerSuffix result.1.target.nonce result.1.target.context result.1.target.record.tag) result.2
  pure (optionalOpen c result.1 oracleResult.1, oracleResult.2)

/-- The integrity event tests the returned optional opening; it never constructs a plaintext-bearing target. -/
theorem acceptedVerifier_eq_openAndRetain (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache) :
    acceptedVerifier c result = (do
      let opened ← openAndRetain c result
      pure (@decide (CtxTypedFullFresh result.1 ∧ opened.1 ≠ none) (Classical.propDecidable _))) := by
  simp only [acceptedVerifier, openAndRetain, AcceptedAt, bind_assoc, pure_bind]
  rfl

structure QueryBoundedAdversary (qH qE : ℕ) extends Adversary where
  publicQueryBound : main.IsQueryBoundP IsCtxPublicQuery qH
  sealQueryBound : main.IsQueryBoundP IsCtxSealQuery qE

/-- The compatibility map is pure and preserves both public-hash and sealing caps exactly. -/
def QueryBoundedAdversary.toLegacy {qH qE : ℕ} (adversary : QueryBoundedAdversary qH qE) :
    CtxQueryBoundedAdversary qH qE where
  main := Target.toLegacy <$> adversary.main
  publicQueryBound := (isQueryBoundP_map_iff adversary.main Target.toLegacy qH).mpr adversary.publicQueryBound
  sealQueryBound := (isQueryBoundP_map_iff adversary.main Target.toLegacy qE).mpr adversary.sealQueryBound

/-- Complete one-key ciphertext-only integrity game, in the same canonical split-cache experiment. -/
noncomputable def game (c : Pqxdh.Crypto) (adversary : Adversary) : ProbComp Bool :=
  acceptedGame c adversary.toLegacy

/-- Final conventional Boolean IND$ bound, using one fresh validation encryption and a 128-bit random-world tag check. -/
theorem acceptedProbability_le_intCtxt_add_booleanIndDollar_add_guesses
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    Pr[= true |
        acceptedGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c
            (ctxPrefixToBooleanINDDollarReduction c adversary)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  calc
    Pr[= true |
        acceptedGame c adversary.toCtxAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c
          (ctxRetainedBaseReduction adversary.toCtxAdversary) +
        ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ :=
      acceptedProbability_le_intCtxt_add_prefix_add_inv
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

/-- The unclaimed endpoint has the existing primitive reductions and losses, with no plaintext guess factor. -/
theorem game_le_intctxt_add_booleanIndDollar_add_guesses (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : QueryBoundedAdversary qH qE) (nonceSpace : qE < 2 ^ 96) :
    Pr[= true | game c adversary.toAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c (ctxRetainedBaseReduction adversary.toLegacy.toCtxAdversary) +
        ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
          (ctxPrefixToBooleanINDDollarReduction c adversary.toLegacy)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ :=
  acceptedProbability_le_intCtxt_add_booleanIndDollar_add_guesses c adversary.toLegacy nonceSpace

/-- The same optional opening performed against the actual shared ROM at the exact secret-prefixed input. -/
noncomputable def canonicalOpenAndRetain (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × CtxRO.QueryCache) : ProbComp (Option Pqxdh.Bytes × CtxRO.QueryCache) := do
  let oracleResult ← (ctxRandomOracle ((), result.1.targetInput)).run result.2
  pure (optionalOpen c result.1 oracleResult.1, oracleResult.2)

/-- Exact split-cache projection retains the actual optional plaintext and complete final cache. -/
theorem canonicalOpenAndRetain_split (c : Pqxdh.Crypto) (result : CtxBeforeVerify × CtxRO.QueryCache) :
    Prod.map id (splitCtxCache result.1.key) <$> canonicalOpenAndRetain c result =
      openAndRetain c (result.1, splitCtxCache result.1.key result.2) := by
  have step := ctxRandomOracle_split_projection result.1.key ((), result.1.targetInput) result.2
  unfold CtxBeforeVerify.targetInput at step
  rw [ctxSplitRandomOracle_outerInput_eq_keyFreeSuffix] at step
  have observed := congrArg (fun computation => do
    let oracleResult ← computation
    pure (optionalOpen c result.1 oracleResult.1, oracleResult.2)) step
  simpa only [canonicalOpenAndRetain, openAndRetain, ctxKeyFreeSuffixOracle,
    StateT.run, map_bind, map_pure, bind_map_left, Function.comp_def, Prod.map, CtxBeforeVerify.targetInput, id_eq] using observed

/-- Actual shared-ROM final verification tests the genuine returned optional opening. -/
noncomputable def canonicalAcceptedVerifier (c : Pqxdh.Crypto)
    (result : CtxBeforeVerify × CtxRO.QueryCache) : ProbComp Bool := do
  let opened ← canonicalOpenAndRetain c result
  pure (@decide (CtxTypedFullFresh result.1 ∧ opened.1 ≠ none) (Classical.propDecidable _))

/-- Splitting the cache changes neither full freshness nor the actual optional-opening acceptance event. -/
theorem canonicalAcceptedVerifier_eq_split (c : Pqxdh.Crypto) (result : CtxBeforeVerify × CtxRO.QueryCache) :
    canonicalAcceptedVerifier c result =
      acceptedVerifier c (result.1, splitCtxCache result.1.key result.2) := by
  rw [acceptedVerifier_eq_openAndRetain]
  have projected := canonicalOpenAndRetain_split c result
  have observed := congrArg (fun computation => do
    let opened ← computation
    pure (@decide (CtxTypedFullFresh result.1 ∧ opened.1 ≠ none) (Classical.propDecidable _))) projected
  simp only [canonicalAcceptedVerifier, bind_map_left, Prod.map, id_eq] at observed ⊢
  convert observed using 1

/-- The pre-verification split is exactly the original shared-ROM game, with its own sampled key retained. -/
theorem splitBeforeVerifyGame_eq_map (c : Pqxdh.Crypto) (adversary : CtxAdversary) :
    ctxSplitBeforeVerifyGame c adversary =
      (fun result : CtxBeforeVerify × CtxRO.QueryCache =>
        (result.1, splitCtxCache result.1.key result.2)) <$> ctxBeforeVerifyGame c adversary := by
  unfold ctxSplitBeforeVerifyGame ctxBeforeVerifyGame
  rw [map_bind]
  apply bind_congr
  intro key
  unfold ctxSplitBeforeVerifyInner ctxBeforeVerifyInner
  simp only [map_bind, map_pure, splitBeforeVerifyProjection]

/-- A ciphertext-only final forgery in the actual shared-ROM experiment. -/
noncomputable def canonicalGame (c : Pqxdh.Crypto) (adversary : Adversary) : ProbComp Bool :=
  ctxBeforeVerifyGame c adversary.toLegacy >>= canonicalAcceptedVerifier c

/-- Exact correspondence connects the shared-ROM optional-opening experiment to the checked component bound. -/
theorem canonicalGame_eq_game (c : Pqxdh.Crypto) (adversary : Adversary) :
    canonicalGame c adversary = game c adversary := by
  unfold game acceptedGame
  rw [splitBeforeVerifyGame_eq_map, bind_map_left]
  unfold canonicalGame
  apply bind_congr
  intro result
  exact canonicalAcceptedVerifier_eq_split c result

/-- The final private hash call samples at most one complete 64-byte digest, even on rejection. -/
theorem suffixStep_uniform_query_bound (suffix : Pqxdh.Bytes) (cache : SplitCache) :
    (ctxKeyFreeSuffixStep suffix cache).IsTotalQueryBound 64 := by
  cases entry : cache.suffixCache suffix with
  | none =>
      unfold ctxKeyFreeSuffixStep
      rw [entry]
      simpa using OracleComp.isTotalQueryBound_bind (n₁ := 64) (n₂ := 0)
        (uniformFixedBytes_isTotalQueryBound 64)
        (fun digest => show IsTotalQueryBound (pure (digest, cacheSuffix cache suffix digest)) 0 by trivial)
  | some digest =>
      unfold ctxKeyFreeSuffixStep
      rw [entry]
      trivial

/-- Actual optional-opening verification retains the complete private hash cost. -/
theorem openAndRetain_uniform_query_bound (c : Pqxdh.Crypto) (result : CtxBeforeVerify × SplitCache) :
    (openAndRetain c result).IsTotalQueryBound 64 := by
  unfold openAndRetain
  simpa using OracleComp.isTotalQueryBound_bind (n₁ := 64) (n₂ := 0)
    (suffixStep_uniform_query_bound
      (outerSuffix result.1.target.nonce result.1.target.context result.1.target.record.tag) result.2)
    (fun oracleResult => show IsTotalQueryBound
      (pure (optionalOpen c result.1 oracleResult.1, oracleResult.2)) 0 by trivial)

/-- The same constructed reductions retain all source hash/seal costs and the validation seal. -/
theorem reduction_query_bounds (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : QueryBoundedAdversary qH qE) :
    (ctxRetainedBaseReduction adversary.toLegacy.toCtxAdversary).main.IsQueryBoundP IsModifiedNonceAeadSealQuery qE ∧
    (ctxRetainedBaseReduction adversary.toLegacy.toCtxAdversary).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64) ∧
    (ctxPrefixToBooleanINDDollarReduction c adversary.toLegacy).main.IsQueryBoundP IsModifiedNonceAeadSealQuery (qE + 1) ∧
    (ctxPrefixToBooleanINDDollarReduction c adversary.toLegacy).main.IsQueryBoundP
      IsModifiedNonceAeadUniformQuery ((qH + qE) * 64) :=
  ⟨ctxRetainedBaseReduction_seal_query_bound adversary.toLegacy.toCtxAdversary qE adversary.toLegacy.sealQueryBound,
    ctxRetainedBaseReduction_uniform_query_bound adversary.toLegacy,
    ctxPrefixToBooleanINDDollarReduction_seal_query_bound c adversary.toLegacy,
    ctxPrefixToBooleanINDDollarReduction_uniform_query_bound c adversary.toLegacy⟩

/-- The actual shared-ROM ciphertext-only game has the stated ordinary primitive reductions and losses. -/
theorem canonicalGame_le_intctxt_add_booleanIndDollar_add_guesses (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : QueryBoundedAdversary qH qE) (nonceSpace : qE < 2 ^ 96) :
    Pr[= true | canonicalGame c adversary.toAdversary] ≤
      modifiedNonceAeadINTCTXTAdvantage c (ctxRetainedBaseReduction adversary.toLegacy.toCtxAdversary) +
        ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
          (ctxPrefixToBooleanINDDollarReduction c adversary.toLegacy)) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
        (((2 ^ 512 : ℕ) : ℝ≥0∞))⁻¹ := by
  rw [canonicalGame_eq_game]
  exact game_le_intctxt_add_booleanIndDollar_add_guesses c adversary nonceSpace

end BeaconcryptCore.Computational.CtxUnclaimedAcceptance

/--
info: 'BeaconcryptCore.Computational.CtxUnclaimedAcceptance.canonicalGame_le_intctxt_add_booleanIndDollar_add_guesses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxUnclaimedAcceptance.canonicalGame_le_intctxt_add_booleanIndDollar_add_guesses

/--
info: 'BeaconcryptCore.Computational.CtxUnclaimedAcceptance.canonicalOpenAndRetain_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxUnclaimedAcceptance.canonicalOpenAndRetain_split

/--
info: 'BeaconcryptCore.Computational.CtxUnclaimedAcceptance.reduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxUnclaimedAcceptance.reduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.CtxUnclaimedAcceptance.openAndRetain_uniform_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CtxUnclaimedAcceptance.openAndRetain_uniform_query_bound
