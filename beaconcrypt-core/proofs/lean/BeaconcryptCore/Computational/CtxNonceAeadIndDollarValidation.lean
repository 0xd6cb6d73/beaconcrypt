import BeaconcryptCore.Computational.CtxNonceAeadIndDollar
import VCVio.CryptoFoundations.SecExp

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

/-- Total choice of a nonce outside the recorded history whenever one exists. -/
noncomputable def chooseFreshCtxNonce (used : List CtxNonce) : CtxNonce :=
  if h : ∃ nonce : CtxNonce, nonce ∉ used then Classical.choose h else default

theorem chooseFreshCtxNonce_not_mem (used : List CtxNonce)
    (hexists : ∃ nonce : CtxNonce, nonce ∉ used) :
    chooseFreshCtxNonce used ∉ used := by
  rw [chooseFreshCtxNonce, dif_pos hexists]
  exact Classical.choose_spec hexists

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
    simp only [StateT.run, hused, if_true, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    change state.usedNonces.length ≤ state.usedNonces.length + 1
    omega
  · unfold ctxDirectSampleKeyFreeSealOracle at hresult
    simp only [StateT.run, hused, if_false] at hresult
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
      · simp only [hseal, if_true] at hstepLength hrec
        have hn : 0 < n := hbound.1.resolve_left (not_not.mpr hseal)
        omega
      · simp only [hseal, if_false] at hstepLength hrec
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
  apply exists_ctxNonce_not_mem
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
    Pr[fun tag => CtxValidationTagHit tag probes | $ᵗ (FixedBytes 16)] ≤
      (qH : ℝ≥0∞) * (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
  classical
  calc
    Pr[fun tag => CtxValidationTagHit tag probes | $ᵗ (FixedBytes 16)] ≤
        ∑ i : Fin qH,
          Pr[fun tag => probes.get i = some tag | $ᵗ (FixedBytes 16)] := by
      simpa [CtxValidationTagHit] using
        (probEvent_exists_finset_le_sum
          (Finset.univ : Finset (Fin qH)) ($ᵗ (FixedBytes 16))
          (fun i tag => probes.get i = some tag))
    _ ≤ ∑ _i : Fin qH,
          (Fintype.card (FixedBytes 16) : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases hprobe : probes.get i with
      | none => simp
      | some candidate => simp
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
    Pr[= true |
      (modifiedNonceAeadINDDollarRandomSealOracle
        (ctxValidationInput nonce)).run state >>= fun result =>
          pure (ctxValidationAccept c nonce probes result.1)] ≤
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  by_cases hused : nonce ∈ state.usedNonces
  · unfold modifiedNonceAeadINDDollarRandomSealOracle
    simp [StateT.run, ctxValidationInput, hused, ctxValidationAccept]
  · unfold modifiedNonceAeadINDDollarRandomSealOracle
    simp only [StateT.run, ctxValidationInput, hused, if_false]
    simp only [bind_assoc, pure_bind]
    rw [← probEvent_eq_eq_probOutput]
    refine probEvent_bind_le_of_forall_le
      (mx := ($ᵗ (FixedBytes [].length) : ProbComp _)) ?_
    intro body _
    rw [bind_pure_comp, probEvent_map]
    calc
      probEvent ($ᵗ (FixedBytes 16))
          ((fun x => x = true) ∘ fun tag =>
            ctxValidationAccept c nonce probes
              (some ⟨body.toList, tag.toList, tag.toList_length⟩)) =
        Pr[fun tag => CtxValidationTagHit tag
            (ctxValidationTagProbeVector c nonce probes) |
          $ᵗ (FixedBytes 16)] := by
            apply OracleComp.probEvent_congr' _ rfl
            intro tag _
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
    Pr[= true |
      modifiedNonceAeadINDDollarRandomExp
        (ctxPrefixToBooleanINDDollarReduction c adversary)] ≤
      (qH : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold modifiedNonceAeadINDDollarRandomExp
    ctxPrefixToBooleanINDDollarReduction
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
  rintro ⟨⟨target, state⟩, primitiveState⟩ _
  simpa [probEvent_eq_eq_probOutput] using
    (randomValidationContinuation_le c
      (chooseFreshCtxNonce state.usedNonces)
      (ctxPrefixProbeVector qH state.publicInputs) primitiveState)

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
    Pr[= true | ctxDirectSamplePrefixProbeExpInner c key adversary] ≤
      Pr[= true | modifiedNonceAeadINDDollarRealExpInner c key
        (ctxPrefixToBooleanINDDollarReduction c adversary)] := by
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
  refine probOutput_bind_mono ?_
  intro result hresult
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
    simp [hhit, ctxValidationAccept, haccept]
  · simp [hhit]

/-- The canonical secret-prefix event is contained in real Boolean validation success. -/
theorem ctxSecretPrefixQueriedProbability_le_booleanReal
    (c : Pqxdh.Crypto) {qH qE : ℕ}
    (adversary : CtxQueryBoundedAdversary qH qE)
    (hqE : qE < 2 ^ 96) :
    ctxSecretPrefixQueriedProbability c adversary.toCtxAdversary ≤
      Pr[= true | modifiedNonceAeadINDDollarRealExp c
        (ctxPrefixToBooleanINDDollarReduction c adversary)] := by
  rw [ctxSecretPrefixQueriedProbability_eq_directSampleProbe]
  unfold ctxDirectSamplePrefixProbeExp
    modifiedNonceAeadINDDollarRealExp
  refine probOutput_bind_mono ?_
  intro key _
  change Pr[= true | ctxDirectSamplePrefixProbeExpInner c key adversary] ≤
    Pr[= true | modifiedNonceAeadINDDollarRealExpInner c key
      (ctxPrefixToBooleanINDDollarReduction c adversary)]
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
        Pr[= true | modifiedNonceAeadINDDollarRealExp c reduction] := by
      exact ctxSecretPrefixQueriedProbability_le_booleanReal
        c adversary hqE
    _ ≤ Pr[= true | modifiedNonceAeadINDDollarRandomExp reduction] +
          ENNReal.ofReal
            (modifiedNonceAeadINDDollarAdvantage c reduction) := by
      exact ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
        (modifiedNonceAeadINDDollarRealExp c reduction)
        (modifiedNonceAeadINDDollarRandomExp reduction)
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
