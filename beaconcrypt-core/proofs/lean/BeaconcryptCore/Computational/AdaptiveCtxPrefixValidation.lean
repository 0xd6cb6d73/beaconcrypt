import BeaconcryptCore.Computational.AdaptiveCtxLogSimulation
import BeaconcryptCore.Computational.VCVioForwardProbabilityTheory
import BeaconcryptCore.Computational.VCVioLegacyBridge

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open AdaptiveCtxLogSimulation AdaptiveRawNonceAead

/-- Explicit finite scan over the already constructed validation-tag candidates. -/
def validationAccept (c : Pqxdh.Crypto) (nonce : CtxNonce) {qHash : ℕ}
    (probes : CtxKeyProbes qHash) (response : Option ModifiedNonceAeadCiphertext) : Bool :=
  match response with
  | none => false
  | some ciphertext =>
    (ctxValidationTagProbeVector c nonce probes).toList.any
      (fun candidate => candidate == some (modifiedNonceAeadCiphertextTag ciphertext))

/-- The explicit scan makes exactly the same Boolean decision as the existing finite existential. -/
@[simp] theorem validationAccept_eq (c : Pqxdh.Crypto) (nonce : CtxNonce) {qHash : ℕ}
    (probes : CtxKeyProbes qHash) (response : Option ModifiedNonceAeadCiphertext) :
    validationAccept c nonce probes response = ctxValidationAccept c nonce probes response := by
  classical
  cases response with
  | none => rfl
  | some ciphertext =>
    have hits :
        (ctxValidationTagProbeVector c nonce probes).toList.any
            (fun candidate => candidate == some (modifiedNonceAeadCiphertextTag ciphertext)) = true ↔
          CtxValidationCiphertextHit c nonce probes ciphertext := by
      simp only [List.any_eq_true, beq_iff_eq, CtxValidationCiphertextHit, CtxValidationTagHit]
      constructor
      · rintro ⟨candidate, member, equal⟩
        obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
        refine ⟨⟨index.val, by simpa using index.isLt⟩, ?_⟩
        exact selected.trans equal
      · rintro ⟨index, selected⟩
        refine ⟨_, ?_, selected⟩
        exact List.get_mem _ _
    apply Bool.eq_iff_iff.mpr
    simpa only [validationAccept, ctxValidationAccept, decide_eq_true_eq] using hits

/-- The decision scans exactly the bounded candidate vector, with no search of the key universe. -/
theorem validationCandidates_length (c : Pqxdh.Crypto) (nonce : CtxNonce) {qHash : ℕ}
    (probes : CtxKeyProbes qHash) :
    (ctxValidationTagProbeVector c nonce probes).toList.length = qHash :=
  List.Vector.toList_length _

/-- The Boolean scan itself adds no primitive or uniform-oracle query; candidate-key evaluations remain local work. -/
theorem validationAccept_no_queries (c : Pqxdh.Crypto) (nonce : CtxNonce) {qHash : ℕ}
    (probes : CtxKeyProbes qHash) (response : Option ModifiedNonceAeadCiphertext) :
    (pure (validationAccept c nonce probes response) : ProbComp Bool).IsTotalQueryBound 0 := by trivial

/-- Bounded key-candidate event on the retained analysis key and complete source transcript. -/
def ProbeEvent {Result : Type} (qHash : ℕ)
    (result : CtxKey × (Result × AdaptiveCtxReceive.ReceiveState)) : Prop :=
  CtxKeyProbeHit result.1 (ctxPrefixProbeVector qHash result.2.2.ctx.publicInputs)

/-- One ordinary validation encryption after the executable adaptive log/reject client. -/
noncomputable def validationReduction {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash : ℕ) : ModifiedNonceAeadINDDollarAdversary :=
  ⟨do
    let result ← sourceClient decode adversary
    let nonce := chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))
    let probes := ctxPrefixProbeVector qHash result.1.2.ctx.publicInputs
    let response ← queryModifiedNonceAeadSeal (ctxValidationInput nonce)
    pure (validationAccept c nonce probes response)⟩

/-- The key-candidate test is an analysis event, not an oracle response. -/
noncomputable def loggedProbeExp {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash : ℕ) : ProbComp Bool := by
  classical
  exact do
    let key ← $ᵗ CtxKey
    let result ← (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (sourceClient decode adversary)).run emptyModifiedNonceAeadHandlerState
    pure (decide (ProbeEvent qHash (key, result.1.1)))

theorem loggedProbeExp_probability {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qHash : ℕ) :
    Pr{let x ← loggedProbeExp decode c adversary qHash}[x = true] =
      Pr{let x ← retainedLoggedGame decode c adversary}[ProbeEvent qHash x] := by
  classical
  unfold loggedProbeExp retainedLoggedGame
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  refine Finset.sum_congr rfl fun key _ => ?_
  congr 1
  conv_lhs => rw [bind_pure_comp _ ((simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (sourceClient decode adversary)).run emptyModifiedNonceAeadHandlerState), prEvent_map]
  conv_rhs => rw [bind_pure_comp _ ((simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (sourceClient decode adversary)).run emptyModifiedNonceAeadHandlerState), prEvent_map]
  simp only [decide_eq_true_eq]

/-- Each fixed candidate vector has at most qHash false validation matches in the random ordinary game. Adaptive raw replies and private cache state are already part of the executed client. -/
theorem validationReduction_random_le {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qHash : ℕ) :
    Pr{let x ← modifiedNonceAeadINDDollarRandomExp (validationReduction decode c adversary qHash)}[x = true] ≤
      (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  unfold modifiedNonceAeadINDDollarRandomExp
  rw [bind_pure_comp _ ((simulateQ modifiedNonceAeadINDDollarRandomImpl
    (validationReduction decode c adversary qHash).main).run emptyModifiedNonceAeadHandlerState),
    prEvent_map]
  unfold validationReduction
  simp only [simulateQ_bind, StateT.run_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun result => ?_
  rcases result with ⟨result, primitiveState⟩
  have bound := randomValidationContinuation_le c
    (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce)))
    (ctxPrefixProbeVector qHash result.1.2.ctx.publicInputs) primitiveState
  rw [bind_pure_comp _ ((modifiedNonceAeadINDDollarRandomSealOracle
    (ctxValidationInput (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))))).run
      primitiveState), prEvent_map] at bound
  simp only [simulateQ_queryModifiedNonceAeadSeal_random, simulateQ_pure, StateT.run_pure,
    validationAccept_eq]
  rw [bind_pure_comp _ ((modifiedNonceAeadINDDollarRandomSealOracle
    (ctxValidationInput (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))))).run
      primitiveState), prEvent_map]
  exact bound

/-- A real key hit always validates at the constructive unused nonce. No plaintext recovered under the hidden key is inserted into any request. -/
theorem loggedProbe_le_validationReal {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (small : qSeal < 2 ^ 96) :
    Pr{let x ← loggedProbeExp decode c adversary qHash}[x = true] ≤
      Pr{let x ← modifiedNonceAeadINDDollarRealExp c (validationReduction decode c adversary qHash)}[x = true] := by
  unfold loggedProbeExp modifiedNonceAeadINDDollarRealExp validationReduction
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun key => ?_
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  simp_rw [simulateQ_queryModifiedNonceAeadSeal, simulateQ_pure, StateT.run_pure]
  simp only [pure_bind]
  refine OracleComp.prEvent_bind_mono_of_support _ _ _ fun result supported => ?_
  by_cases hit : ProbeEvent qHash (key, result.1.1)
  · have fresh := sourceClient_validation_fresh decode c key adversary qSeal bounded small result supported
    rw [modifiedNonceAeadSealOracle_validation_run_of_fresh c key _ result.2 fresh]
    simp only [pure_bind]
    have accepts := keyProbeHit_implies_realValidationCiphertextHit c key
      (chooseFreshCtxNonce (result.1.2.map (fun entry => entry.input.nonce)))
      (ctxPrefixProbeVector qHash result.1.1.2.ctx.publicInputs) hit
    simp [hit, ctxValidationAccept, accepts, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
  · simp [hit, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]

/-- The logged source's candidate-hit event has an ordinary conventional IND$ reduction and an explicit 128-bit validation term. -/
theorem loggedProbe_le_indDollar {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (small : qSeal < 2 ^ 96) :
    Pr{let x ← retainedLoggedGame decode c adversary}[ProbeEvent qHash x] ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (validationReduction decode c adversary qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
  rw [← loggedProbeExp_probability]
  apply (loggedProbe_le_validationReal decode c adversary qHash qSeal bounded small).trans
  have comparison := VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage
    (modifiedNonceAeadINDDollarRealExp c (validationReduction decode c adversary qHash))
    (modifiedNonceAeadINDDollarRandomExp (validationReduction decode c adversary qHash))
  rw [← prEvent_eq_evalDist_singleton
      (modifiedNonceAeadINDDollarRealExp c (validationReduction decode c adversary qHash)) true,
    ← prEvent_eq_evalDist_singleton
      (modifiedNonceAeadINDDollarRandomExp (validationReduction decode c adversary qHash)) true]
    at comparison
  exact comparison.trans (by
    rw [add_comm]
    exact add_le_add le_rfl (validationReduction_random_le decode c adversary qHash))

/-- Any fixed terminal event can be transported across full-state total variation without exposing the retained state to the adversary. -/
theorem probEvent_le_add_ofReal_tvDist {Result : Type} (left right : ProbComp Result)
    (event : Result → Prop) :
    Pr{let x ← left}[event x] ≤ Pr{let x ← right}[event x] + ENNReal.ofReal (tvDist left right) := by
  classical
  let decideEvent := fun result => decide (event result)
  have comparison := VCVioForward.evalDist_apply_true_le_add_ofReal_boolDistAdvantage
    (decideEvent <$> left) (decideEvent <$> right)
  rw [← prEvent_eq_evalDist_singleton (decideEvent <$> left) true,
    ← prEvent_eq_evalDist_singleton (decideEvent <$> right) true, prEvent_map, prEvent_map] at comparison
  have variation : (decideEvent <$> left).boolDistAdvantage (decideEvent <$> right) ≤ tvDist left right := by
    rw [ProbComp.boolDistAdvantage]
    simpa only [VCVioLegacy.evalDist_singleton_eq_probOutput] using
      (abs_probOutput_toReal_sub_le_tvDist _ _).trans (tvDist_map_le decideEvent left right)
  calc
    Pr{let x ← left}[event x] ≤ Pr{let x ← right}[event x] +
        ENNReal.ofReal ((decideEvent <$> left).boolDistAdvantage (decideEvent <$> right)) := by
      simpa only [decideEvent, decide_eq_true_eq] using comparison
    _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal variation)

/-- Only the actual independent source run needs a trace-length theorem. The fixed candidate-vector event can then be transported unchanged to the logged world. -/
theorem independent_prefix_eq_probe {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash) :
    Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary}[AdaptiveCtxPrefix.RetainedPrefix x] =
      Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary}[ProbeEvent qHash x] := by
  unfold AdaptiveCtxRetainedKey.retainedIndependentGame
  rw [prEvent_bind_eq_sum_fintype, prEvent_bind_eq_sum_fintype]
  refine Finset.sum_congr rfl fun key _ => ?_
  congr 1
  rw [bind_pure_comp _ (AdaptiveCtxIndependent.independentGame decode c key adversary), prEvent_map,
    prEvent_map]
  apply prEvent_congr_of_support
  intro result supported
  exact (AdaptiveCtxPrefix.independentGame_prefix_probe_iff decode c key adversary qHash bounded result supported).symm

/-- The actual adaptive independent-public prefix probability is bounded by one concrete conventional IND$ reduction, validation false positives, and an explicit additional ordinary integrity family for the transcript transfer. -/
theorem independent_prefix_le_indDollar_add_intctxt {Result : Type}
    (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    Pr{let x ← AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary}[AdaptiveCtxPrefix.RetainedPrefix x] ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (validationReduction decode c adversary qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
          ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
            (AdaptiveRawNonceAead.indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
              (AdaptiveCtxReceive.wrapped decode adversary) index) := by
  rw [independent_prefix_eq_probe decode c adversary qHash hashBound]
  apply (probEvent_le_add_ofReal_tvDist
    (AdaptiveCtxRetainedKey.retainedIndependentGame decode c adversary)
    (retainedLoggedGame decode c adversary) (ProbeEvent qHash)).trans
  apply add_le_add
  · exact loggedProbe_le_indDollar decode c adversary qHash qSeal sealBound small
  · rw [retainedLoggedGame_eq]
    exact AdaptiveCtxRetainedKey.retainedIndependentGame_distance_le_intctxt_sum
      decode c fallback adversary qRaw rawBound

/-- Canonical routed CTX and the executable ordinary log/reject source client now share a conventional primitive bound. The factor two explicitly retains the integrity cost of both full-transcript replacement and prefix-event transfer. -/
theorem routed_distance_le_indDollar_add_two_intctxt {Result : Type}
    (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (tvDist (AdaptiveCtxPrefix.retainedRoutedGame decode c adversary)
      (retainedLoggedGame decode c adversary)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (validationReduction decode c adversary qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
          2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
            (AdaptiveRawNonceAead.indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
              (AdaptiveCtxReceive.wrapped decode adversary) index) := by
  rw [retainedLoggedGame_eq]
  apply (AdaptiveCtxPrefix.retainedRoutedGame_distance_le_prefix_add_intctxt
    decode c fallback adversary qRaw rawBound).trans
  have charged := add_le_add
    (independent_prefix_le_indDollar_add_intctxt decode c fallback adversary
      qHash qSeal qRaw hashBound sealBound rawBound small) (le_refl
        (∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
          (AdaptiveRawNonceAead.indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
            (AdaptiveCtxReceive.wrapped decode adversary) index)))
  simpa only [two_mul, add_assoc] using charged

/-- One validation seal is added to the source sealing budget. Reused-nonce source requests are still counted. -/
theorem validationReduction_seal_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal) :
    (validationReduction decode c adversary qHash).main.IsQueryBoundP IsModifiedNonceAeadSealQuery (qSeal + 1) := by
  unfold validationReduction
  refine OracleComp.isQueryBoundP_bind (n := qSeal) (m := 1)
    (sourceClient_seal_bound decode adversary qSeal bounded) ?_
  intro result _
  dsimp only
  unfold queryModifiedNonceAeadSeal
  refine OracleComp.isQueryBoundP_bind (n := 1) (m := 0) ?_ ?_
  · exact (OracleComp.isQueryBoundP_query_iff
      (spec := ModifiedNonceAeadAdversarySpec) (p := IsModifiedNonceAeadSealQuery)
      (.inr (ctxValidationInput (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))))) 1).2
      (fun _ => by omega)
  · intro response _
    exact OracleComp.isQueryBoundP_pure _ _ _

/-- Candidate-key validation is deterministic local work; its single primitive encryption introduces no source uniform-oracle query. Every adaptive cache miss remains charged. -/
theorem validationReduction_uniform_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    (validationReduction decode c adversary qHash).main.IsQueryBoundP IsPrimitiveUniformQuery
      (qCoins + 64 * (qHash + qSeal + qRaw)) := by
  unfold validationReduction
  simpa only [Nat.add_zero] using OracleComp.isQueryBoundP_bind
    (n := qCoins + 64 * (qHash + qSeal + qRaw)) (m := 0)
    (sourceClient_uniform_bound decode adversary qCoins qHash qSeal qRaw coinBound hashBound sealBound rawBound)
    (fun result _ => by
      unfold queryModifiedNonceAeadSeal
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 0) ?_ ?_
      · exact (OracleComp.isQueryBoundP_query_iff
          (spec := ModifiedNonceAeadAdversarySpec) (p := IsPrimitiveUniformQuery)
          (.inr (ctxValidationInput (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))))) 0).2
          (fun h => False.elim h)
      · intro response _
        exact OracleComp.isQueryBoundP_pure _ _ _)

/-- The complete real ordinary validation challenger pays for its sampled 32-byte key and every source/digest uniform request. Local primitive operations are counted separately by the seal/verification ledger. -/
theorem validationReal_uniform_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    (modifiedNonceAeadINDDollarRealExp c (validationReduction decode c adversary qHash)).IsTotalQueryBound
      (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  unfold modifiedNonceAeadINDDollarRealExp
  apply OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro key
  simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    CtxComputationalSecurity.modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound c key
      (validationReduction decode c adversary qHash).main _
      (validationReduction_uniform_bound decode c adversary qCoins qHash qSeal qRaw
        coinBound hashBound sealBound rawBound)

/-- The original adaptive shared-ROM source experiment retains its complete canonical cache and actual optional plaintext transcript. -/
noncomputable def retainedCanonicalGame {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × AdaptiveCtxCanonical.CanonicalState)) := do
  let key ← $ᵗ CtxKey
  let result ← AdaptiveCtxCanonical.canonicalGame decode c key adversary
  pure (key, result)

/-- Split only the cache representation while retaining the exact sampled key, source result, complete histories and every failed lookup. -/
def canonicalProjection {Result : Type}
    (result : CtxKey × (Result × AdaptiveCtxCanonical.CanonicalState)) :
    CtxKey × (Result × AdaptiveCtxReceive.ReceiveState) :=
  (result.1, Prod.map id (AdaptiveCtxCanonical.splitState result.1) result.2)

/-- The shared-ROM to routed-cache hop is exact in the same retained-key experiment. -/
theorem retainedCanonicalGame_eq_routed {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    canonicalProjection <$> retainedCanonicalGame decode c adversary =
      AdaptiveCtxPrefix.retainedRoutedGame decode c adversary := by
  simp only [retainedCanonicalGame, AdaptiveCtxPrefix.retainedRoutedGame,
    map_bind, bind_pure_comp, Functor.map_map]
  congr 1
  funext key
  simpa only [Functor.map_map, Function.comp_def, canonicalProjection] using
    congrArg (fun game => (Prod.mk key) <$> game)
      (AdaptiveCtxCanonical.canonicalGame_split decode c key adversary)

/-- Actual shared-ROM optional-plaintext receive has the same conventional bound after the exact complete-cache projection. This remains the single-key cryptographic receive interface, before ratchet selection or codec refinement. -/
theorem canonical_distance_le_indDollar_add_two_intctxt {Result : Type}
    (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (tvDist (canonicalProjection <$> retainedCanonicalGame decode c adversary)
      (retainedLoggedGame decode c adversary)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (validationReduction decode c adversary qHash)) +
        (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
          2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
            (AdaptiveRawNonceAead.indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
              (AdaptiveCtxReceive.wrapped decode adversary) index) := by
  rw [retainedCanonicalGame_eq_routed]
  exact routed_distance_le_indDollar_add_two_intctxt decode c fallback adversary
    qHash qSeal qRaw hashBound sealBound rawBound small

end BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_random_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_random_le

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.loggedProbe_le_validationReal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.loggedProbe_le_validationReal

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.independent_prefix_le_indDollar_add_intctxt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.independent_prefix_le_indDollar_add_intctxt

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.routed_distance_le_indDollar_add_two_intctxt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.routed_distance_le_indDollar_add_two_intctxt

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_seal_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReduction_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReal_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationReal_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.retainedCanonicalGame_eq_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.retainedCanonicalGame_eq_routed

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.canonical_distance_le_indDollar_add_two_intctxt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.canonical_distance_le_indDollar_add_two_intctxt

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationAccept_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrefixValidation.validationAccept_eq
