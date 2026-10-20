import BeaconcryptCore.Computational.CtxConstructiveNonce
import VCVio.CryptoFoundations.SecExp
import BeaconcryptCore.Computational.VCVioForwardProbabilityTheory
import BeaconcryptCore.Computational.VCVioLegacyBridge

/-!
# Conventional Boolean IND$ validation for modified CTX

This module converts bounded CTX secret-prefix probes into a conventional Boolean modified nonce-AEAD IND$ distinguisher using one fresh-nonce validation seal.
Under `qE < 2^96`, the reduction preserves real prefix hits, makes at most `qE + 1` primitive seal queries, and bounds random validation false positives by `qH / 2^128`.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation

open CtxRomAuth CtxPrefixIsolation CtxSplitCache CtxIndependentTags
  CtxHonestTagSampling CtxNonceAeadIntCtxt CtxNonceAeadIndDollar

/-- Conventional Boolean distinguisher for the modified nonce-AEAD IND$ interface. -/
structure ModifiedNonceAeadINDDollarAdversary where
  main : OracleComp ModifiedNonceAeadAdversarySpec Bool

/-- Conventional real modified nonce-AEAD IND$ experiment. -/
noncomputable def modifiedNonceAeadINDDollarRealExp
    (c : Pqxdh.Crypto)
    (adversary : ModifiedNonceAeadINDDollarAdversary) : ProbComp Bool := do
  let key ← $ᵗ CtxKey
  let result ←
    (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      adversary.main).run emptyModifiedNonceAeadHandlerState
  pure result.1

/-- Conventional random modified nonce-AEAD IND$ experiment. -/
noncomputable def modifiedNonceAeadINDDollarRandomExp
    (adversary : ModifiedNonceAeadINDDollarAdversary) : ProbComp Bool := do
  let result ←
    (simulateQ modifiedNonceAeadINDDollarRandomImpl
      adversary.main).run emptyModifiedNonceAeadHandlerState
  pure result.1

/-- Conventional Boolean modified nonce-AEAD IND$ advantage. -/
noncomputable def modifiedNonceAeadINDDollarAdvantage
    (c : Pqxdh.Crypto)
    (adversary : ModifiedNonceAeadINDDollarAdversary) : ℝ :=
  (modifiedNonceAeadINDDollarRealExp c adversary).boolDistAdvantage
    (modifiedNonceAeadINDDollarRandomExp adversary)

/-- The protocol nonce space has exactly 96 bits. -/
theorem ctxNonce_card : Fintype.card CtxNonce = 2 ^ 96 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 12 = (2 ^ 8) ^ 12 := by norm_num
    _ = 2 ^ (8 * 12) := by rw [pow_mul]
    _ = 2 ^ 96 := by norm_num

/-- Any list shorter than the nonce space omits at least one nonce. -/
theorem exists_ctxNonce_not_mem (used : List CtxNonce)
    (hlen : used.length < Fintype.card CtxNonce) :
    ∃ nonce : CtxNonce, nonce ∉ used := by
  by_contra hall
  push Not at hall
  have hsubset : (Finset.univ : Finset CtxNonce) ⊆ used.toFinset := by
    intro nonce _
    simpa using hall nonce
  have hcard : Fintype.card CtxNonce ≤ used.toFinset.card := by
    simpa using Finset.card_le_card hsubset
  have hlist : used.toFinset.card ≤ used.length :=
    List.toFinset_card_le used
  omega

/-- Executable bounded scan of one more candidate than the recorded used-nonce count. -/
def chooseFreshCtxNonce (used : List CtxNonce) : CtxNonce :=
  CtxConstructiveNonce.chooseNonce used

theorem chooseFreshCtxNonce_not_mem (used : List CtxNonce)
    (hlen : used.length < Fintype.card CtxNonce) :
    chooseFreshCtxNonce used ∉ used := by
  apply CtxConstructiveNonce.chooseNonce_not_mem_of_seal_bound used used.length (le_refl _)
  simpa only [ctxNonce_card] using hlen

theorem ctxIndependentPublicOracle_usedNonces
    (query : CtxRO.Domain) (state : CtxIndependentTagState)
    (result : CtxDigest × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxIndependentPublicOracle query).run state)) :
    result.2.usedNonces = state.usedNonces := by
  change result ∈ support
    ((ctxRandomOracle query).run state.cache.publicCache >>=
      fun oracleResult =>
        let cache := { state.cache with publicCache := oracleResult.2 }
        pure (oracleResult.1, state.addPublic query.2 cache)) at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨oracleResult, _, hresult⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rfl

theorem ctxDirectSampleKeyFreeSealOracle_usedNonces_length_le
    (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (state : CtxIndependentTagState)
    (result : Option CtxRomRecord × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleKeyFreeSealOracle c key input).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length + 1 := by
  by_cases hused : input.nonce ∈ state.usedNonces
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, ite_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    change state.usedNonces.length ≤ state.usedNonces.length + 1
    omega
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, ite_false] at hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨commit, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    simp [CtxIndependentTagState.addSeal]

theorem ctxDirectSampleIndependentTagImpl_usedNonces_length_step
    (c : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxAdversarySpec.Domain) (state : CtxIndependentTagState)
    (result : CtxAdversarySpec.Range query × CtxIndependentTagState)
    (hresult : result ∈ support
      ((ctxDirectSampleIndependentTagImpl c key query).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length +
      if IsCtxSealQuery query then 1 else 0 := by
  rcases query with query | input
  · have hused := ctxIndependentPublicOracle_usedNonces
      query state result hresult
    simp [IsCtxSealQuery, hused]
  · simpa [IsCtxSealQuery] using
      ctxDirectSampleKeyFreeSealOracle_usedNonces_length_le
        c key input state result hresult

/-- A direct-sampling run with arbitrary output records at most one nonce per sealing query. -/
theorem ctxDirectSampleIndependentTag_run_usedNonces_length_le_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {alpha : Type}
    {oa : OracleComp CtxAdversarySpec alpha} {n : ℕ}
    (hbound : oa.IsQueryBoundP IsCtxSealQuery n)
    (state : CtxIndependentTagState)
    (result : alpha × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key) oa).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length + n := by
  induction oa using OracleComp.inductionOn generalizing n state result with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      rcases hresult with rfl
      exact Nat.le_add_right state.usedNonces.length n
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind,
        mem_support_bind_iff] at hresult
      obtain ⟨stepResult, hstep, hrest⟩ := hresult
      have hstepLength :=
        ctxDirectSampleIndependentTagImpl_usedNonces_length_step
          c key query state stepResult hstep
      have hrec := ih stepResult.1 (hbound.2 stepResult.1)
        stepResult.2 result hrest
      by_cases hseal : IsCtxSealQuery query
      · simp only [hseal, ite_true] at hstepLength hrec
        have hn : 0 < n := hbound.1.resolve_left (not_not.mpr hseal)
        omega
      · simp only [hseal, ite_false] at hstepLength hrec
        omega

/-- Compatibility wrapper for the authenticity adversary output. -/
theorem ctxDirectSampleIndependentTag_run_usedNonces_length_le
    (c : Pqxdh.Crypto) (key : CtxKey)
    {oa : OracleComp CtxAdversarySpec CtxAliasTarget} {n : ℕ}
    (hbound : oa.IsQueryBoundP IsCtxSealQuery n)
    (state : CtxIndependentTagState)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key) oa).run state)) :
    result.2.usedNonces.length ≤ state.usedNonces.length + n := by
  exact ctxDirectSampleIndependentTag_run_usedNonces_length_le_of_main
    c key hbound state result hresult

/-- An arbitrary-output direct-sampling run satisfying the sealing-query bound records at most `qE` nonces. -/
theorem ctxDirectSampleIndependentTag_run_usedNonces_length_le_qE_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {alpha : Type} {qE : ℕ}
    (main : OracleComp CtxAdversarySpec alpha)
    (hbound : main.IsQueryBoundP IsCtxSealQuery qE)
    (result : alpha × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        main).run emptyCtxIndependentTagState)) :
    result.2.usedNonces.length ≤ qE := by
  simpa [emptyCtxIndependentTagState] using
    ctxDirectSampleIndependentTag_run_usedNonces_length_le_of_main
      c key hbound emptyCtxIndependentTagState result hresult

theorem ctxDirectSampleIndependentTag_run_usedNonces_length_le_qE
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    result.2.usedNonces.length ≤ qE := by
  exact ctxDirectSampleIndependentTag_run_usedNonces_length_le_qE_of_main
    c key adversary.main adversary.sealQueryBound result hresult

/-- If an arbitrary-output direct run uses fewer nonces than the nonce space, its chosen validation nonce is fresh. -/
theorem chooseFreshCtxNonce_fresh_of_direct_support_of_main
    (c : Pqxdh.Crypto) (key : CtxKey) {alpha : Type} {qE : ℕ}
    (main : OracleComp CtxAdversarySpec alpha)
    (hbound : main.IsQueryBoundP IsCtxSealQuery qE)
    (hqE : qE < 2 ^ 96)
    (result : alpha × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        main).run emptyCtxIndependentTagState)) :
    chooseFreshCtxNonce result.2.usedNonces ∉ result.2.usedNonces := by
  apply chooseFreshCtxNonce_not_mem
  rw [ctxNonce_card]
  exact lt_of_le_of_lt
    (ctxDirectSampleIndependentTag_run_usedNonces_length_le_qE_of_main
      c key main hbound result hresult) hqE

theorem chooseFreshCtxNonce_fresh_of_direct_support
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96)
    (result : CtxAliasTarget × CtxIndependentTagState)
    (hresult : result ∈ support
      ((simulateQ (ctxDirectSampleIndependentTagImpl c key)
        adversary.main).run emptyCtxIndependentTagState)) :
    chooseFreshCtxNonce result.2.usedNonces ∉ result.2.usedNonces := by
  exact chooseFreshCtxNonce_fresh_of_direct_support_of_main
    c key adversary.main adversary.sealQueryBound hqE result hresult

/-- Empty-message validation query used to test returned key candidates. -/
def ctxValidationInput (nonce : CtxNonce) : ModifiedNonceAeadSealInput :=
  ⟨nonce, [], []⟩

/-- Locally recomputed 128-bit validation tag under one candidate key. -/
def ctxValidationTag (c : Pqxdh.Crypto) (key : CtxKey)
    (nonce : CtxNonce) : FixedBytes 16 :=
  ⟨(c.aeadSeal key.toList nonce.toList [] []).2,
    c.aeadSeal_tag_length _ _ _ _⟩

/-- Map each optional key probe to its optional locally recomputed tag. -/
def ctxValidationTagProbeVector (c : Pqxdh.Crypto) (nonce : CtxNonce)
    {qH : ℕ} (probes : CtxKeyProbes qH) :
    List.Vector (Option (FixedBytes 16)) qH :=
  List.Vector.ofFn fun i => (probes.get i).map fun key =>
    ctxValidationTag c key nonce

/-- One optional validation-tag slot matches the challenger response. -/
def CtxValidationTagHit {qH : ℕ} (tag : FixedBytes 16)
    (probes : List.Vector (Option (FixedBytes 16)) qH) : Prop :=
  ∃ i : Fin qH, probes.get i = some tag

theorem ctxKeyProbeHit_implies_validationTagHit
    (c : Pqxdh.Crypto) (nonce : CtxNonce) {qH : ℕ}
    (key : CtxKey) (probes : CtxKeyProbes qH)
    (hhit : CtxKeyProbeHit key probes) :
    CtxValidationTagHit (ctxValidationTag c key nonce)
      (ctxValidationTagProbeVector c nonce probes) := by
  obtain ⟨i, hi⟩ := hhit
  refine ⟨i, ?_⟩
  simp [ctxValidationTagProbeVector, hi]

/-- A detached Poly1305-sized tag has exactly 128 bits. -/
theorem ctxValidationTag_card : Fintype.card (FixedBytes 16) = 2 ^ 128 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 16 = (2 ^ 8) ^ 16 := by norm_num
    _ = 2 ^ (8 * 16) := by rw [pow_mul]
    _ = 2 ^ 128 := by norm_num

/-- A fixed vector of `qH` candidate tags hits a fresh uniform tag with union-bound cost. -/
theorem probEvent_uniformValidationTag_hit_le {qH : ℕ}
    (probes : List.Vector (Option (FixedBytes 16)) qH) :
    Pr{let tag ← $ᵗ (FixedBytes 16)}[CtxValidationTagHit tag probes] ≤
      (qH : ℝ≥0∞) * (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    Pr{let tag ← $ᵗ (FixedBytes 16)}[CtxValidationTagHit tag probes] ≤
        ∑ i : Fin qH,
          Pr{let tag ← $ᵗ (FixedBytes 16)}[probes.get i = some tag] := by
      rw [prEvent_congr ($ᵗ (FixedBytes 16)) (fun tag => CtxValidationTagHit tag probes)
        (fun tag => ∃ i ∈ (Finset.univ : Finset (Fin qH)), probes.get i = some tag)
        (fun tag => by simp [CtxValidationTagHit])]
      exact prEvent_exists_finset_le (Finset.univ : Finset (Fin qH)) ($ᵗ (FixedBytes 16))
        (fun i tag => probes.get i = some tag)
    _ ≤ ∑ _i : Fin qH,
          (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases hprobe : probes.get i with
      | none =>
          rw [prEvent_eq_zero_of_forall_not ($ᵗ (FixedBytes 16))
            (fun tag : FixedBytes 16 => (none : Option (FixedBytes 16)) = some tag)
            (fun tag h => by simp at h)]
          exact zero_le
      | some candidate =>
          refine le_of_eq ?_
          rw [prEvent_congr ($ᵗ (FixedBytes 16)) (fun tag => some candidate = some tag)
              (fun tag => tag = candidate) (fun tag => by simp [eq_comm]),
            SampleableType.prEvent_uniformSample_eq_singleton]
    _ = (qH : ℝ≥0∞) *
          (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Interpret a returned detached tag as the fixed-width validation sample. -/
def modifiedNonceAeadCiphertextTag
    (ciphertext : ModifiedNonceAeadCiphertext) : FixedBytes 16 :=
  ⟨ciphertext.tag, ciphertext.tagLength⟩

/-- A validation ciphertext matches at least one locally tested candidate key. -/
def CtxValidationCiphertextHit (c : Pqxdh.Crypto) (nonce : CtxNonce)
    {qH : ℕ} (probes : CtxKeyProbes qH)
    (ciphertext : ModifiedNonceAeadCiphertext) : Prop :=
  CtxValidationTagHit (modifiedNonceAeadCiphertextTag ciphertext)
    (ctxValidationTagProbeVector c nonce probes)

/-- Boolean decision made from the optional validation response. -/
noncomputable def ctxValidationAccept (c : Pqxdh.Crypto)
    (nonce : CtxNonce) {qH : ℕ} (probes : CtxKeyProbes qH)
    (response : Option ModifiedNonceAeadCiphertext) : Bool := by
  classical
  exact match response with
    | none => false
    | some ciphertext =>
        decide (CtxValidationCiphertextHit c nonce probes ciphertext)

/-- Boolean conventional-IND$ reduction: run the source, choose an unused nonce, and validate every returned key candidate with one extra encryption. -/
noncomputable def ctxPrefixToBooleanINDDollarReduction
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
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

/-- The validation reduction makes one more primitive seal query than the source. -/
theorem ctxPrefixToBooleanINDDollarReduction_seal_query_bound
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    (ctxPrefixToBooleanINDDollarReduction c adversary).main.IsQueryBoundP
      IsModifiedNonceAeadSealQuery (qE + 1) := by
  unfold ctxPrefixToBooleanINDDollarReduction
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

/-- Exact real validation ciphertext under one candidate key. -/
def ctxRealValidationCiphertext (c : Pqxdh.Crypto) (key : CtxKey)
    (nonce : CtxNonce) : ModifiedNonceAeadCiphertext :=
  ⟨(c.aeadSeal key.toList nonce.toList [] []).1,
    (c.aeadSeal key.toList nonce.toList [] []).2,
    c.aeadSeal_tag_length _ _ _ _⟩

theorem modifiedNonceAeadSealOracle_validation_run_of_fresh
    (c : Pqxdh.Crypto) (key : CtxKey) (nonce : CtxNonce)
    (state : ModifiedNonceAeadHandlerState)
    (hfresh : nonce ∉ state.usedNonces) :
    (modifiedNonceAeadSealOracle c key
      (ctxValidationInput nonce)).run state =
        pure (some (ctxRealValidationCiphertext c key nonce),
          state.addSeal
            ⟨ctxValidationInput nonce,
              ctxRealValidationCiphertext c key nonce⟩) := by
  rw [modifiedNonceAeadSealOracle_run]
  simp [ctxValidationInput, ctxRealValidationCiphertext, hfresh]

theorem keyProbeHit_implies_realValidationCiphertextHit
    (c : Pqxdh.Crypto) (key : CtxKey) (nonce : CtxNonce)
    {qH : ℕ} (probes : CtxKeyProbes qH)
    (hhit : CtxKeyProbeHit key probes) :
    CtxValidationCiphertextHit c nonce probes
      (ctxRealValidationCiphertext c key nonce) := by
  simpa [CtxValidationCiphertextHit, modifiedNonceAeadCiphertextTag,
    ctxRealValidationCiphertext, ctxValidationTag] using
      ctxKeyProbeHit_implies_validationTagHit c nonce key probes hhit

theorem randomValidationContinuation_le
    (c : Pqxdh.Crypto) (nonce : CtxNonce) {qH : ℕ}
    (probes : CtxKeyProbes qH) (state : ModifiedNonceAeadHandlerState) :
    Pr{let x ← ((modifiedNonceAeadINDDollarRandomSealOracle
        (ctxValidationInput nonce)).run state >>= fun result =>
          pure (ctxValidationAccept c nonce probes result.1))}[x = true] ≤
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  rw [bind_pure_comp _ ((modifiedNonceAeadINDDollarRandomSealOracle
    (ctxValidationInput nonce)).run state), prEvent_map]
  by_cases hused : nonce ∈ state.usedNonces
  · unfold modifiedNonceAeadINDDollarRandomSealOracle
    simp only [StateT.run, ctxValidationInput, hused, ite_true]
    classical
    rw [prEvent_pure]
    simp [ctxValidationAccept]
  · unfold modifiedNonceAeadINDDollarRandomSealOracle
    simp only [StateT.run, ctxValidationInput, hused, ite_false]
    refine prEvent_bind_le_of_forall_le ($ᵗ (FixedBytes [].length) : ProbComp _) _ _ fun body => ?_
    rw [bind_pure_comp _ ($ᵗ (FixedBytes 16)), prEvent_map]
    calc
      Pr{let tag ← $ᵗ (FixedBytes 16)}[ctxValidationAccept c nonce probes
          (some ⟨body.toList, tag.toList, tag.toList_length⟩) = true] =
        Pr{let tag ← $ᵗ (FixedBytes 16)}[CtxValidationTagHit tag
            (ctxValidationTagProbeVector c nonce probes)] := by
            apply prEvent_congr
            intro tag
            classical
            simp [ctxValidationAccept,
              CtxValidationCiphertextHit,
              modifiedNonceAeadCiphertextTag]
      _ ≤ (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
        rw [← ctxValidationTag_card]
        exact probEvent_uniformValidationTag_hit_le
          (ctxValidationTagProbeVector c nonce probes)

theorem simulateQ_queryModifiedNonceAeadSeal_random
    (input : ModifiedNonceAeadSealInput) :
    simulateQ modifiedNonceAeadINDDollarRandomImpl
        (queryModifiedNonceAeadSeal input) =
      modifiedNonceAeadINDDollarRandomSealOracle input := by
  unfold modifiedNonceAeadINDDollarRandomImpl
    queryModifiedNonceAeadSeal
  simp

/-- Random-world success of the Boolean validation reduction costs at most `qH / 2^128`. -/
theorem ctxPrefixBooleanReduction_random_le
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE) :
    Pr{let x ← (modifiedNonceAeadINDDollarRandomExp
        (ctxPrefixToBooleanINDDollarReduction c adversary))}[x = true] ≤
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold modifiedNonceAeadINDDollarRandomExp
  rw [bind_pure_comp _ ((simulateQ modifiedNonceAeadINDDollarRandomImpl
    (ctxPrefixToBooleanINDDollarReduction c adversary).main).run emptyModifiedNonceAeadHandlerState),
    prEvent_map]
  unfold ctxPrefixToBooleanINDDollarReduction
  simp only [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun result => ?_
  rcases result with ⟨⟨target, state⟩, primitiveState⟩
  have bound := randomValidationContinuation_le c
    (chooseFreshCtxNonce state.usedNonces)
    (ctxPrefixProbeVector qH state.publicInputs) primitiveState
  rw [bind_pure_comp _ ((modifiedNonceAeadINDDollarRandomSealOracle
    (ctxValidationInput (chooseFreshCtxNonce state.usedNonces))).run primitiveState),
    prEvent_map] at bound
  simp only [simulateQ_queryModifiedNonceAeadSeal_random, simulateQ_pure, StateT.run_pure]
  rw [bind_pure_comp _ ((modifiedNonceAeadINDDollarRandomSealOracle
    (ctxValidationInput (chooseFreshCtxNonce state.usedNonces))).run primitiveState),
    prEvent_map]
  exact bound

/-- Fixed-key conventional real experiment. -/
noncomputable def modifiedNonceAeadINDDollarRealExpInner
    (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : ModifiedNonceAeadINDDollarAdversary) : ProbComp Bool := do
  let result ←
    (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      adversary.main).run emptyModifiedNonceAeadHandlerState
  pure result.1

theorem directProbe_le_booleanRealInner
    (c : Pqxdh.Crypto) (key : CtxKey) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    Pr{let x ← ctxDirectSamplePrefixProbeExpInner c key adversary}[x = true] ≤
      Pr{let x ← (modifiedNonceAeadINDDollarRealExpInner c key
        (ctxPrefixToBooleanINDDollarReduction c adversary))}[x = true] := by
  unfold ctxDirectSamplePrefixProbeExpInner
    modifiedNonceAeadINDDollarRealExpInner
    ctxPrefixToBooleanINDDollarReduction
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [ctxRetainedBaseNestedRun_eq_direct c key adversary.toCtxAdversary]
  simp_rw [simulateQ_queryModifiedNonceAeadSeal,
    simulateQ_pure, StateT.run_pure]
  simp only [pure_bind]
  rw [← bind_pure_comp]
  simp only [bind_assoc, pure_bind]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun result hresult => ?_
  by_cases hhit : CtxKeyProbeHit key
      (ctxPrefixProbeVector qH result.2.publicInputs)
  · have hfresh := chooseFreshCtxNonce_fresh_of_direct_support
      c key adversary hqE result hresult
    rw [modifiedNonceAeadSealOracle_validation_run_of_fresh
      c key (chooseFreshCtxNonce result.2.usedNonces)
      (ctxIndependentTagStateToModifiedNonceAead result.2) hfresh]
    simp only [pure_bind]
    have haccept := keyProbeHit_implies_realValidationCiphertextHit
      c key (chooseFreshCtxNonce result.2.usedNonces)
      (ctxPrefixProbeVector qH result.2.publicInputs) hhit
    simp [hhit, ctxValidationAccept, haccept, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
  · simp [hhit, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]

/-- The canonical secret-prefix event is contained in real Boolean validation success. -/
theorem ctxSecretPrefixQueriedProbability_le_booleanReal
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary ≤
      Pr{let x ← (modifiedNonceAeadINDDollarRealExp c
        (ctxPrefixToBooleanINDDollarReduction c adversary))}[x = true] := by
  rw [ctxSecretPrefixQueriedProbability_eq_directSampleProbe]
  unfold ctxDirectSamplePrefixProbeExp
    modifiedNonceAeadINDDollarRealExp
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun key => ?_
  change Pr{let x ← ctxDirectSamplePrefixProbeExpInner c key adversary}[x = true] ≤
    Pr{let x ← (modifiedNonceAeadINDDollarRealExpInner c key
      (ctxPrefixToBooleanINDDollarReduction c adversary))}[x = true]
  exact directProbe_le_booleanRealInner c key adversary hqE

/-- Conventional Boolean IND$ bound for the CTX secret-prefix event. -/
theorem ctxSecretPrefixQueriedProbability_le_booleanINDDollar
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary ≤
      ENNReal.ofReal
        (modifiedNonceAeadINDDollarAdvantage c
          (ctxPrefixToBooleanINDDollarReduction c adversary)) +
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  let reduction := ctxPrefixToBooleanINDDollarReduction c adversary
  calc
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary ≤
        Pr{let x ← modifiedNonceAeadINDDollarRealExp c reduction}[x = true] := by
      exact ctxSecretPrefixQueriedProbability_le_booleanReal
        c adversary hqE
    _ ≤ Pr{let x ← modifiedNonceAeadINDDollarRandomExp reduction}[x = true] +
          ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c reduction) := by
      have comparison := VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage
          (modifiedNonceAeadINDDollarRealExp c reduction)
          (modifiedNonceAeadINDDollarRandomExp reduction)
      rw [← prEvent_eq_evalDist_singleton (modifiedNonceAeadINDDollarRealExp c reduction) true,
        ← prEvent_eq_evalDist_singleton (modifiedNonceAeadINDDollarRandomExp reduction) true]
        at comparison
      exact comparison
    _ ≤ (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
          ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c reduction) := by
      gcongr
      exact ctxPrefixBooleanReduction_random_le c adversary
    _ = ENNReal.ofReal
          (modifiedNonceAeadINDDollarAdvantage c reduction) +
        (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
      rw [add_comm]

end BeaconcryptCore.Computational.CtxNonceAeadIndDollarValidation
