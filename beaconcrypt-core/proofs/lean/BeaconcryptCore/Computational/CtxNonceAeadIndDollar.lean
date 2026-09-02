import BeaconcryptCore.Computational.CtxNonceAeadIntCtxt
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Modified nonce-AEAD IND$ reduction for the CTX secret-prefix event

This module packages every public random-oracle input as one optional candidate for the hidden 256-bit CTX key. The real primitive experiment reproduces the direct independent-tag CTX game exactly. In the random primitive experiment the candidate list is independent of a ghost key sampled after the adversary finishes, so a union bound contributes exactly `qH / 2^256`.

The challenger itself tests the returned candidates against the real or ghost key. This specialized key-probe IND$ notion is strictly stronger than conventional Boolean nonce-AEAD IND$ for an arbitrary `Pqxdh.Crypto`; no standard-game wrapper is claimed here.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxNonceAeadIndDollar

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling CtxNonceAeadIntCtxt

/-- A fixed-width list of optional key guesses, one slot per public hash query. -/
abbrev CtxKeyProbes (qH : ℕ) := List.Vector (Option CtxKey) qH

/-- Some candidate slot contains the hidden key. -/
def CtxKeyProbeHit {qH : ℕ} (key : CtxKey)
    (probes : CtxKeyProbes qH) : Prop :=
  ∃ i : Fin qH, probes.get i = some key

/-- Interpret the first 32 bytes of an input as a key candidate when they exist. -/
def prefixCandidate? (input : Pqxdh.Bytes) : Option CtxKey :=
  if h : (input.take 32).length = 32 then
    some ⟨input.take 32, h⟩
  else
    none

theorem prefixCandidate?_eq_some_iff (input : Pqxdh.Bytes) (key : CtxKey) :
    prefixCandidate? input = some key ↔ SecretPrefixQuery key input := by
  unfold prefixCandidate? SecretPrefixQuery
  split
  · rename_i h
    constructor
    · intro heq
      exact congrArg List.Vector.toList (Option.some.inj heq)
    · intro heq
      congr 1
      exact List.Vector.toList_injective heq
  · rename_i h
    constructor
    · simp
    · intro heq
      have hlength : (input.take 32).length = 32 := by
        rw [heq]
        exact key.toList_length
      exact (h hlength).elim

/-- Pad the public-query trace to exactly `qH` optional key candidates. -/
def ctxPrefixProbeVector (qH : ℕ) (inputs : List Pqxdh.Bytes) :
    CtxKeyProbes qH :=
  List.Vector.ofFn fun i => (inputs[i.val]?).bind prefixCandidate?

theorem ctxPrefixProbeVector_hit_of_prefix {qH : ℕ}
    (inputs : List Pqxdh.Bytes) (key : CtxKey)
    (hlen : inputs.length ≤ qH)
    (hbad : ∃ input ∈ inputs, SecretPrefixQuery key input) :
    CtxKeyProbeHit key (ctxPrefixProbeVector qH inputs) := by
  obtain ⟨i, hi, hprefix⟩ := List.exists_mem_iff_getElem.mp hbad
  let j : Fin qH := ⟨i, lt_of_lt_of_le hi hlen⟩
  refine ⟨j, ?_⟩
  simp [ctxPrefixProbeVector, j, List.getElem?_eq_getElem hi,
    prefixCandidate?_eq_some_iff, hprefix]

theorem ctxPrefixProbeVector_prefix_of_hit {qH : ℕ}
    (inputs : List Pqxdh.Bytes) (key : CtxKey)
    (hhit : CtxKeyProbeHit key (ctxPrefixProbeVector qH inputs)) :
    ∃ input ∈ inputs, SecretPrefixQuery key input := by
  obtain ⟨i, hi⟩ := hhit
  simp only [ctxPrefixProbeVector, List.Vector.get_ofFn] at hi
  cases hget : inputs[i.val]? with
  | none => simp [hget] at hi
  | some input =>
      refine ⟨input, ?_, ?_⟩
      · exact List.mem_iff_getElem?.mpr ⟨i.val, hget⟩
      · exact (prefixCandidate?_eq_some_iff input key).mp (by
          simpa [hget] using hi)

theorem ctxPrefixProbeVector_hit_iff_of_length_le {qH : ℕ}
    (inputs : List Pqxdh.Bytes) (key : CtxKey)
    (hlen : inputs.length ≤ qH) :
    CtxKeyProbeHit key (ctxPrefixProbeVector qH inputs) ↔
      ∃ input ∈ inputs, SecretPrefixQuery key input := by
  exact ⟨ctxPrefixProbeVector_prefix_of_hit inputs key,
    ctxPrefixProbeVector_hit_of_prefix inputs key hlen⟩

/-- The independent-tag game preserves the same sticky secret-prefix event as the split-cache game. -/
theorem ctxIndependent_badProbability_eq_prefixBad
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Pr[fun result => result.2.2 = true |
      ctxIndependentTagFlaggedBeforeVerify c key adversary] =
      ctxPrefixBadProbability c key adversary := by
  calc
    Pr[fun result => result.2.2 = true |
        ctxIndependentTagFlaggedBeforeVerify c key adversary] =
        Pr[fun result => result.2.2 = true |
          ctxSplitRoutedFlaggedBeforeVerify c key adversary] :=
      (OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
        (ctxSplitRoutedWithPrefixFlagImpl c key)
        (ctxIndependentWithPrefixFlagImpl c key)
        (ctxSplitRouted_independent_agree_good c key)
        (ctxSplitRoutedWithPrefixFlagImpl_bad_mono c key)
        (ctxIndependentWithPrefixFlagImpl_bad_mono c key)
        adversary.main emptyCtxIndependentTagState).symm
    _ = ctxPrefixBadProbability c key adversary :=
      ctxSplitRouted_badProbability_eq_prefixBad c key adversary

theorem ctxIndependentPublicOracle_publicInputs
    (query : CtxRO.Domain) (state : CtxIndependentTagState)
    (result : CtxDigest × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxIndependentPublicOracle query).run state)) :
    result.2.publicInputs = query.2 :: state.publicInputs := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache.publicCache >>= fun oracleResult =>
      let cache := { state.cache with publicCache := oracleResult.2 }
      pure (oracleResult.1, state.addPublic query.2 cache)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rfl

theorem ctxKeyFreeSealOracle_publicInputs
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxKeyFreeSealOracle c key input).run state)) :
    result.2.publicInputs = state.publicInputs := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    rfl
  · unfold ctxKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_false] at hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨oracleResult, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    rfl

/-- The independent game's sticky bit is exactly membership in its public-input trace. -/
def CtxIndependentPrefixFlagInvariant (key : CtxKey)
    (state : CtxIndependentTagState × Bool) : Prop :=
  state.2 = true ↔
    ∃ input ∈ state.1.publicInputs, SecretPrefixQuery key input

@[simp] theorem emptyCtxIndependentPrefixFlagInvariant (key : CtxKey) :
    CtxIndependentPrefixFlagInvariant key
      (emptyCtxIndependentTagState, false) := by
  simp [CtxIndependentPrefixFlagInvariant, emptyCtxIndependentTagState]

theorem ctxIndependentWithPrefixFlagImpl_preserves_prefix_flag
    (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (ctxIndependentWithPrefixFlagImpl c key)
      (CtxIndependentPrefixFlagInvariant key) := by
  intro query state hinvariant result hresult
  cases query with
  | inl publicQuery =>
      obtain ⟨intermediate, hintermediate, rfl⟩ :=
        withStickyBad_result_state
          (decide (SecretPrefixQuery key publicQuery.2))
          (ctxIndependentPublicOracle publicQuery) state result hresult
      have hpublic := ctxIndependentPublicOracle_publicInputs publicQuery state.1
        intermediate hintermediate
      unfold CtxIndependentPrefixFlagInvariant at hinvariant ⊢
      rw [hpublic]
      simp only [List.mem_cons, exists_eq_or_imp]
      simp [Bool.or_eq_true, hinvariant, or_comm]
  | inr sealInput =>
      obtain ⟨intermediate, hintermediate, rfl⟩ :=
        withStickyBad_result_state false (ctxKeyFreeSealOracle c key sealInput)
          state result hresult
      have hpublic := ctxKeyFreeSealOracle_publicInputs c key sealInput state.1
        intermediate hintermediate
      unfold CtxIndependentPrefixFlagInvariant at hinvariant ⊢
      rw [hpublic]
      simpa using hinvariant

theorem ctxIndependentTagFlagged_run_prefix_flag
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary)
    (result : CtxAliasTarget × (CtxIndependentTagState × Bool))
    (hresult : result ∈ support
      (ctxIndependentTagFlaggedBeforeVerify c key adversary)) :
    CtxIndependentPrefixFlagInvariant key result.2 := by
  exact OracleComp.simulateQ_run_preservesInv
    (ctxIndependentWithPrefixFlagImpl c key)
    (CtxIndependentPrefixFlagInvariant key)
    (ctxIndependentWithPrefixFlagImpl_preserves_prefix_flag c key)
    adversary.main (emptyCtxIndependentTagState, false)
    (emptyCtxIndependentPrefixFlagInvariant key) result hresult

/-- Fixed-key secret-prefix probability read directly from the independent public-input trace. -/
noncomputable def ctxIndependentPublicPrefixProbability
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ℝ≥0∞ :=
  Pr[fun result =>
      ∃ input ∈ result.2.publicInputs, SecretPrefixQuery key input |
    (simulateQ (ctxIndependentTagImpl c key) adversary.main).run
      emptyCtxIndependentTagState]

theorem ctxIndependent_badProbability_eq_publicPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    Pr[fun result => result.2.2 = true |
      ctxIndependentTagFlaggedBeforeVerify c key adversary] =
      ctxIndependentPublicPrefixProbability c key adversary := by
  unfold ctxIndependentPublicPrefixProbability
  rw [← ctxIndependentWithPrefixFlagImpl_proj_run c key adversary,
    probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  exact ctxIndependentTagFlagged_run_prefix_flag
    c key adversary result hresult

/-- Predicate selecting public CTX random-oracle queries. -/
def IsCtxPublicQuery : CtxAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsCtxPublicQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- A CTX adversary with separate public-hash and honest-seal budgets. -/
structure CtxQueryBoundedAdversary (qH qE : ℕ) extends CtxAdversary where
  publicQueryBound : main.IsQueryBoundP IsCtxPublicQuery qH
  sealQueryBound : main.IsQueryBoundP IsCtxSealQuery qE

theorem ctxDirectSampleKeyFreeSealOracle_publicInputs
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleKeyFreeSealOracle c key input).run state)) :
    result.2.publicInputs = state.publicInputs := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    rfl
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_false] at hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨commit, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    rfl

theorem ctxDirectSampleIndependentTagImpl_publicInputs_length_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState)
    (result : CtxAdversarySpec.Range query × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleIndependentTagImpl c key query).run state)) :
    result.2.publicInputs.length = state.publicInputs.length +
      if IsCtxPublicQuery query then 1 else 0 := by
  rcases query with query | input
  · have hpublic := ctxIndependentPublicOracle_publicInputs query state result hresult
    simp only [IsCtxPublicQuery, if_true]
    rw [hpublic, List.length_cons]
  · have hpublic := ctxDirectSampleKeyFreeSealOracle_publicInputs
      c key input state result hresult
    simp [IsCtxPublicQuery, hpublic]

theorem ctxDirectSampleIndependentTag_run_publicInputs_length_le
    (c : Pqxdh.Crypto) (key : CtxKey)
    {oa : OracleComp CtxAdversarySpec CtxAliasTarget} {n : ℕ}
    (hbound : oa.IsQueryBoundP IsCtxPublicQuery n)
    (state : CtxIndependentTagState)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key) oa).run state)) :
    result.2.publicInputs.length ≤ state.publicInputs.length + n := by
  induction oa using OracleComp.inductionOn generalizing n state result with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      rcases hresult with rfl
      exact Nat.le_add_right state.publicInputs.length n
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hresult
      obtain ⟨stepResult, hstep, hrest⟩ := hresult
      have hstepLength :=
        ctxDirectSampleIndependentTagImpl_publicInputs_length_step
          c key query state stepResult hstep
      have hrec := ih stepResult.1 (hbound.2 stepResult.1)
        stepResult.2 result hrest
      by_cases hpublic : IsCtxPublicQuery query
      · simp only [hpublic, if_true] at hstepLength hrec
        have hn : 0 < n := hbound.1.resolve_left (not_not.mpr hpublic)
        omega
      · simp only [hpublic, if_false] at hstepLength hrec
        omega

theorem ctxDirectSampleIndependentTag_run_publicInputs_length_le_qH
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    result.2.publicInputs.length ≤ qH := by
  simpa [emptyCtxIndependentTagState] using
    ctxDirectSampleIndependentTag_run_publicInputs_length_le
      c key adversary.publicQueryBound emptyCtxIndependentTagState result hresult

/-- Fixed-key public-prefix probability in the explicit honest-tag sampling game. -/
noncomputable def ctxDirectSamplePublicPrefixProbability
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ℝ≥0∞ :=
  Pr[fun result =>
      ∃ input ∈ result.2.publicInputs, SecretPrefixQuery key input |
    (simulateQ (ctxDirectSampleIndependentTagImpl c key) adversary.main).run
      emptyCtxIndependentTagState]

theorem ctxIndependentPublicPrefixProbability_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ctxIndependentPublicPrefixProbability c key adversary =
      ctxDirectSamplePublicPrefixProbability c key adversary := by
  unfold ctxIndependentPublicPrefixProbability
    ctxDirectSamplePublicPrefixProbability
  rw [ctxIndependentTagImpl_run_eq_directSample]

/-- The canonical fixed-key bad event is exactly the direct game's public-prefix event. -/
theorem ctxSecretPrefixQueriedProbabilityInner_eq_directSamplePublicPrefix
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : CtxAdversary) :
    ctxSecretPrefixQueriedProbabilityInner c key adversary =
      ctxDirectSamplePublicPrefixProbability c key adversary := by
  calc
    ctxSecretPrefixQueriedProbabilityInner c key adversary =
        ctxPrefixBadProbability c key adversary :=
      (ctxPrefixBadProbability_eq_secretPrefixQueriedProbabilityInner
        c key adversary).symm
    _ = Pr[fun result => result.2.2 = true |
          ctxIndependentTagFlaggedBeforeVerify c key adversary] :=
      (ctxIndependent_badProbability_eq_prefixBad c key adversary).symm
    _ = ctxIndependentPublicPrefixProbability c key adversary :=
      ctxIndependent_badProbability_eq_publicPrefix c key adversary
    _ = ctxDirectSamplePublicPrefixProbability c key adversary :=
      ctxIndependentPublicPrefixProbability_eq_directSample c key adversary

/-- A modified nonce-AEAD distinguisher that returns at most `qH` key candidates. -/
structure ModifiedNonceAeadINDDollarProbeAdversary (qH : ℕ) where
  main : OracleComp ModifiedNonceAeadAdversarySpec (CtxKeyProbes qH)

/-- Primitive-side shorthand for the encryption-query budget of a probe adversary. -/
def ModifiedNonceAeadINDDollarProbeAdversary.MakesAtMostSealQueries
    {qH : ℕ} (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH)
    (qE : ℕ) : Prop :=
  adversary.main.IsQueryBoundP IsModifiedNonceAeadSealQuery qE

/-- Run the CTX adversary through the retained-base adapter and return its public key candidates. -/
noncomputable def ctxPrefixToModifiedNonceAeadINDDollarReduction
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    ModifiedNonceAeadINDDollarProbeAdversary qH where
  main := (fun result => ctxPrefixProbeVector qH result.2.publicInputs) <$>
    (simulateQ ctxRetainedBaseReductionImpl adversary.main).run
      emptyCtxIndependentTagState

/-- The probe reduction forwards at most the original `qE` primitive encryption queries. -/
theorem ctxPrefixToModifiedNonceAeadINDDollarReduction_seal_query_bound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary).MakesAtMostSealQueries qE := by
  unfold ModifiedNonceAeadINDDollarProbeAdversary.MakesAtMostSealQueries
    ctxPrefixToModifiedNonceAeadINDDollarReduction
  rw [OracleComp.isQueryBoundP_map_iff]
  exact adversary.sealQueryBound.simulateQ_run_StateT_of_step
    ctxRetainedBaseReductionImpl_seal_query_bound_step
    emptyCtxIndependentTagState

/-- Separate `qH` and `qE` bounds imply an exact `qH + qE` total source-query bound. -/
theorem isTotalQueryBound_of_ctx_public_and_seal_bounds {alpha : Type}
    {oa : OracleComp CtxAdversarySpec alpha} {qH qE : ℕ}
    (hpublic : oa.IsQueryBoundP IsCtxPublicQuery qH)
    (hseal : oa.IsQueryBoundP IsCtxSealQuery qE) :
    oa.IsTotalQueryBound (qH + qE) := by
  induction oa using OracleComp.inductionOn generalizing qH qE with
  | pure x => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hpublic hseal
      rw [OracleComp.isTotalQueryBound_query_bind_iff]
      rcases query with publicQuery | sealInput
      · simp [IsCtxPublicQuery, IsCtxSealQuery] at hpublic hseal
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (hpublic.2 response) (hseal response)).mono
          (by omega)
      · simp [IsCtxPublicQuery, IsCtxSealQuery] at hpublic hseal
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (hpublic response) (hseal.2 response)).mono
          (by omega)

theorem CtxQueryBoundedAdversary.totalQueryBound
    {qH qE : ℕ} (adversary : CtxQueryBoundedAdversary qH qE) :
    adversary.main.IsTotalQueryBound (qH + qE) :=
  isTotalQueryBound_of_ctx_public_and_seal_bounds
    adversary.publicQueryBound adversary.sealQueryBound

/-- Random-world nonce-rejecting encryption returns fresh independent body and tag bytes. -/
noncomputable def modifiedNonceAeadINDDollarRandomSealOracle :
    QueryImpl ModifiedNonceAeadSealSpec
      (StateT ModifiedNonceAeadHandlerState ProbComp) :=
  fun input state =>
    if input.nonce ∈ state.usedNonces then
      pure (none, state)
    else do
      let body ← $ᵗ (FixedBytes input.plaintext.length)
      let tag ← $ᵗ (FixedBytes 16)
      let ciphertext : ModifiedNonceAeadCiphertext :=
        ⟨body.toList, tag.toList, tag.toList_length⟩
      pure (some ciphertext, state.addSeal ⟨input, ciphertext⟩)

/-- Modified nonce-AEAD IND$ random-world implementation. -/
noncomputable def modifiedNonceAeadINDDollarRandomImpl :
    QueryImpl ModifiedNonceAeadAdversarySpec
      (StateT ModifiedNonceAeadHandlerState ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT ModifiedNonceAeadHandlerState ProbComp) +
    modifiedNonceAeadINDDollarRandomSealOracle

/-- Real key-probe experiment: sample the primitive key, run real encryption, then test all probes. -/
noncomputable def modifiedNonceAeadINDDollarRealProbeExp
    (c : Pqxdh.Crypto) {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH) :
    ProbComp Bool := by
  classical
  exact do
    let key ← $ᵗ CtxKey
    let result ←
      (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        adversary.main).run emptyModifiedNonceAeadHandlerState
    pure (decide (CtxKeyProbeHit key result.1))

/-- Random key-probe experiment: run the key-free random world, then sample an independent ghost key. -/
noncomputable def modifiedNonceAeadINDDollarRandomProbeExp
    {qH : ℕ} (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH) :
    ProbComp Bool := by
  classical
  exact do
    let result ←
      (simulateQ modifiedNonceAeadINDDollarRandomImpl
        adversary.main).run emptyModifiedNonceAeadHandlerState
    let key ← $ᵗ CtxKey
    pure (decide (CtxKeyProbeHit key result.1))

/-- Advantage in the modified key-probe IND$ experiment. -/
noncomputable def modifiedNonceAeadINDDollarProbeAdvantage
    (c : Pqxdh.Crypto) {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH) : ℝ :=
  (modifiedNonceAeadINDDollarRealProbeExp c adversary).boolDistAdvantage
    (modifiedNonceAeadINDDollarRandomProbeExp adversary)

/-- The hidden CTX key space has exactly 256 bits. -/
theorem ctxKey_card : Fintype.card CtxKey = 2 ^ 256 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- A fixed vector of `qH` candidates hits an independent uniform key with probability at most `qH / |K|`. -/
theorem probEvent_uniformKey_probeHit_le {qH : ℕ}
    (probes : CtxKeyProbes qH) :
    Pr[fun key => CtxKeyProbeHit key probes | $ᵗ CtxKey] ≤
      (qH : ℝ≥0∞) * (Fintype.card CtxKey : ℝ≥0∞)⁻¹ := by
  classical
  calc
    Pr[fun key => CtxKeyProbeHit key probes | $ᵗ CtxKey] ≤
        ∑ i : Fin qH,
          Pr[fun key => probes.get i = some key | $ᵗ CtxKey] := by
      simpa [CtxKeyProbeHit] using
        (probEvent_exists_finset_le_sum
          (Finset.univ : Finset (Fin qH)) ($ᵗ CtxKey)
          (fun i key => probes.get i = some key))
    _ ≤ ∑ _i : Fin qH,
          (Fintype.card CtxKey : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases hprobe : probes.get i with
      | none => simp
      | some candidate =>
          simp
    _ = (qH : ℝ≥0∞) * (Fintype.card CtxKey : ℝ≥0∞)⁻¹ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- The random-world key-probe event costs only the `qH / |K|` guessing term. -/
theorem modifiedNonceAeadINDDollarRandomProbe_le {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH) :
    Pr[= true | modifiedNonceAeadINDDollarRandomProbeExp adversary] ≤
      (qH : ℝ≥0∞) * (Fintype.card CtxKey : ℝ≥0∞)⁻¹ := by
  classical
  unfold modifiedNonceAeadINDDollarRandomProbeExp
  rw [← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le (mx :=
    (simulateQ modifiedNonceAeadINDDollarRandomImpl
      adversary.main).run emptyModifiedNonceAeadHandlerState) ?_
  rintro ⟨probes, state⟩ hsupport
  rw [bind_pure_comp, probEvent_map]
  simpa [decide_eq_true_eq] using
    probEvent_uniformKey_probeHit_le probes

/-- Fixed-key direct CTX experiment returning whether the bounded probe vector hits the key. -/
noncomputable def ctxDirectSamplePrefixProbeExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) : ProbComp Bool := by
  classical
  exact do
    let result ←
      (simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState
    pure (decide (CtxKeyProbeHit key
      (ctxPrefixProbeVector qH result.2.publicInputs)))

/-- Under the `qH` bound, probe success is exactly the direct public-prefix event. -/
theorem ctxDirectSamplePrefixProbeExpInner_probability
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    Pr[= true | ctxDirectSamplePrefixProbeExpInner c key adversary] =
      ctxDirectSamplePublicPrefixProbability c key adversary.toCtxAdversary := by
  classical
  unfold ctxDirectSamplePrefixProbeExpInner
    ctxDirectSamplePublicPrefixProbability
  rw [← probEvent_eq_eq_probOutput, bind_pure_comp, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result hresult
  simpa [Function.comp_def] using
    (ctxPrefixProbeVector_hit_iff_of_length_le
      result.2.publicInputs key
      (ctxDirectSampleIndependentTag_run_publicInputs_length_le_qH
        c key adversary result hresult))

/-- Fixed-key real primitive probe experiment, before sampling the outer hidden key. -/
noncomputable def modifiedNonceAeadINDDollarRealProbeExpInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH : ℕ}
    (adversary : ModifiedNonceAeadINDDollarProbeAdversary qH) :
    ProbComp Bool := by
  classical
  exact do
    let result ←
      (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
        adversary.main).run emptyModifiedNonceAeadHandlerState
    pure (decide (CtxKeyProbeHit key result.1))

/-- The real primitive probe reduction is exactly the direct honest-tag CTX experiment. -/
theorem ctxPrefixReduction_realProbeExpInner_eq_directSample
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    modifiedNonceAeadINDDollarRealProbeExpInner c key
        (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary) =
      ctxDirectSamplePrefixProbeExpInner c key adversary := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExpInner
    ctxPrefixToModifiedNonceAeadINDDollarReduction
    ctxDirectSamplePrefixProbeExpInner
  simp only [simulateQ_map, StateT.run_map, bind_pure_comp,
    Functor.map_map]
  rw [ctxRetainedBaseNestedRun_eq_direct c key adversary.toCtxAdversary]
  rw [Functor.map_map]

/-- Sample the hidden key around the fixed-key direct probe experiment. -/
noncomputable def ctxDirectSamplePrefixProbeExp
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  ctxDirectSamplePrefixProbeExpInner c key adversary

/-- The canonical secret-prefix probability equals the direct bounded probe experiment. -/
theorem ctxSecretPrefixQueriedProbability_eq_directSampleProbe
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary =
      Pr[= true | ctxDirectSamplePrefixProbeExp c adversary] := by
  classical
  unfold ctxSecretPrefixQueriedProbability ctxBeforeVerifyGame
    ctxDirectSamplePrefixProbeExp
  rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro key
  congr 1
  rw [ctxDirectSamplePrefixProbeExpInner_probability]
  exact ctxSecretPrefixQueriedProbabilityInner_eq_directSamplePublicPrefix
    c key adversary.toCtxAdversary

/-- The complete real probe reduction equals the direct experiment, including key sampling. -/
theorem modifiedNonceAeadINDDollarRealProbeExp_reduction_eq_directSample
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    modifiedNonceAeadINDDollarRealProbeExp c
        (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary) =
      ctxDirectSamplePrefixProbeExp c adversary := by
  classical
  unfold modifiedNonceAeadINDDollarRealProbeExp
    ctxDirectSamplePrefixProbeExp
  apply bind_congr
  intro key
  change modifiedNonceAeadINDDollarRealProbeExpInner c key
      (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary) = _
  exact ctxPrefixReduction_realProbeExpInner_eq_directSample
    c key adversary

/-- The canonical secret-prefix event is exactly the real probe reduction's success event. -/
theorem ctxSecretPrefixQueriedProbability_eq_realProbeReduction
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary =
      Pr[= true |
        modifiedNonceAeadINDDollarRealProbeExp c
          (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)] := by
  rw [ctxSecretPrefixQueriedProbability_eq_directSampleProbe]
  rw [modifiedNonceAeadINDDollarRealProbeExp_reduction_eq_directSample]

/-- Final secret-prefix bound with one IND$ charge and the exact `qH / 2^256` guessing term. -/
theorem ctxSecretPrefixQueriedProbability_le_modifiedNonceAeadINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary ≤
      ENNReal.ofReal
        (modifiedNonceAeadINDDollarProbeAdvantage c
          (ctxPrefixToModifiedNonceAeadINDDollarReduction adversary)) +
      (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ := by
  let reduction := ctxPrefixToModifiedNonceAeadINDDollarReduction adversary
  calc
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary =
        Pr[= true | modifiedNonceAeadINDDollarRealProbeExp c reduction] := by
      exact ctxSecretPrefixQueriedProbability_eq_realProbeReduction c adversary
    _ ≤ Pr[= true | modifiedNonceAeadINDDollarRandomProbeExp reduction] +
          ENNReal.ofReal (modifiedNonceAeadINDDollarProbeAdvantage c reduction) := by
      exact ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        (modifiedNonceAeadINDDollarRealProbeExp c reduction)
        (modifiedNonceAeadINDDollarRandomProbeExp reduction)
    _ ≤ (qH : ℝ≥0∞) * (Fintype.card CtxKey : ℝ≥0∞)⁻¹ +
          ENNReal.ofReal (modifiedNonceAeadINDDollarProbeAdvantage c reduction) := by
      gcongr
      exact modifiedNonceAeadINDDollarRandomProbe_le reduction
    _ = ENNReal.ofReal (modifiedNonceAeadINDDollarProbeAdvantage c reduction) +
          (qH : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [ctxKey_card, add_comm]

end BeaconcryptCore.Computational.CtxNonceAeadIndDollar
