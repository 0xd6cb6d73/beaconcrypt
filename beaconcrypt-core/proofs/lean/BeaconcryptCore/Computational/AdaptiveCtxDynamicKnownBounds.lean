import BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys

/-!
The dynamic known-key compiler preserves each selected seal/raw allowance and forwards all actual known-key hashing to the selected challenger. Known keys can be generated after earlier replies; they are not sampled as an independent family. The constructed client therefore consumes the existing one-key CTX comparison with its original ordinary validation and attempt-indexed forgery reductions. This is still conditional on a source compiler supplying the selected uniform-key endpoint, decoder and freshness event.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxQueryBounds AdaptiveCtxSharedHash
open AdaptiveCtxSharedTarget AdaptiveCtxSharedReplayBounds AdaptiveCtxDynamicKnownKeys

def TargetClass (p : ReceiveSpec.Domain → Prop) : Spec.Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance (p : ReceiveSpec.Domain → Prop) [DecidablePred p] : DecidablePred (TargetClass p) :=
  fun query => by cases query <;> unfold TargetClass <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Known-key work makes no selected seal or raw call; every selected request keeps its exact category. -/
theorem target_step (c : Pqxdh.Crypto) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False) (query : Spec.Domain) (state : ReductionState) :
    ((AdaptiveCtxDynamicKnownKeys.reductionImpl c query).run state).IsQueryBoundP p
      (if TargetClass p query then 1 else 0) := by
  cases query with
  | inl selected =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, TargetClass]
    exact (isQueryBoundP_query_iff p selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, TargetClass, if_false]
    apply forward_bound
    simp only [unavailable]
    exact isQueryBoundP_false _ 0

/-- Arbitrary adaptive dynamic-key work preserves every target-only source budget. -/
theorem target_bound (c : Pqxdh.Crypto) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False) {Result : Type}
    (client : OracleComp Spec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (TargetClass p) bound) (state : ReductionState) :
    (AdaptiveCtxDynamicKnownKeys.wrapped c client state).IsQueryBoundP p bound :=
  bounded.simulateQ_run_StateT_of_step (target_step c p unavailable) state

def HashRoute : Spec.Domain → Prop
  | .inl query => SourceHash query
  | .inr known => ModeHash true known.request

instance : DecidablePred HashRoute := fun query => by
  cases query <;> unfold HashRoute <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every actual known-key verification/seal can issue its shared hash request and is counted. -/
theorem hash_step (c : Pqxdh.Crypto) (query : Spec.Domain) (state : ReductionState) :
    ((AdaptiveCtxDynamicKnownKeys.reductionImpl c query).run state).IsQueryBoundP SourceHash
      (if HashRoute query then 1 else 0) := by
  cases query with
  | inl selected =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, HashRoute]
    exact (isQueryBoundP_query_iff SourceHash selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, HashRoute]
    apply forward_bound
    simp only [forward_hash_class]
    exact mode_hash_step true known.decode c known.key known.request (state.others known.slot)

/-- The complete adaptive reduction charges selected public hashing and every forwarded known-key hash. -/
theorem hash_bound (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp Spec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP HashRoute bound) (state : ReductionState) :
    (AdaptiveCtxDynamicKnownKeys.wrapped c client state).IsQueryBoundP SourceHash bound :=
  bounded.simulateQ_run_StateT_of_step (hash_step c) state

def UniformRoute : Spec.Domain → Prop
  | .inl query => SourceUniform query
  | .inr known => SourceUniform known.request

instance : DecidablePred UniformRoute := fun query => by
  cases query <;> unfold UniformRoute <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every explicit local random request is forwarded once; real known-key work has no uncharged private random table. -/
theorem uniform_step (c : Pqxdh.Crypto) (query : Spec.Domain) (state : ReductionState) :
    ((AdaptiveCtxDynamicKnownKeys.reductionImpl c query).run state).IsQueryBoundP SourceUniform
      (if UniformRoute query then 1 else 0) := by
  cases query with
  | inl selected =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, UniformRoute]
    exact (isQueryBoundP_query_iff SourceUniform selected _).mpr (by intro hit; simp [hit])
  | inr known =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, UniformRoute]
    apply forward_bound
    simp only [forward_uniform_class]
    simpa only [ModePrivate, if_true, if_false, StateT.run] using
      mode_uniform_step true known.decode c known.key known.request (state.others known.slot)

/-- The dynamic reduction retains the complete explicit random-query allowance. -/
theorem uniform_bound (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp Spec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP UniformRoute bound) (state : ReductionState) :
    (AdaptiveCtxDynamicKnownKeys.wrapped c client state).IsQueryBoundP SourceUniform bound :=
  bounded.simulateQ_run_StateT_of_step (uniform_step c) state

/-- The exact constructed ordinary client has separate random, shared-hash, selected-seal and selected-raw ledgers. -/
theorem decision_budgets (c : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP UniformRoute qUniform)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (decisionClient c client).IsQueryBoundP SourceUniform qUniform ∧
      (decisionClient c client).IsQueryBoundP SourceHash qHash ∧
      (decisionClient c client).IsQueryBoundP SourceSeal qSeal ∧
      (decisionClient c client).IsQueryBoundP IsRawQuery qRaw := by
  simp only [decisionClient, isQueryBoundP_map_iff]
  exact ⟨uniform_bound c client qUniform uniformBound _, hash_bound c client qHash hashBound _,
    target_bound c _ forward_seal_class client qSeal sealBound _,
    target_bound c _ forward_raw_class client qRaw rawBound _⟩

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The same dynamic known-key experiment consumes the existing one-key CTX integrity comparison with actual validation and one forgery reduction for every possible raw attempt. -/
theorem selected_integrity (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp Spec Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame true decode c client).boolDistAdvantage
      (Prod.fst <$> sourceGame false decode c client)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c (decisionClient c client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
          (AdaptiveCtxReceive.wrapped decode (decisionClient c client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  rw [source_view, source_view, AdaptiveCtxSharedModes.real_view_eq, AdaptiveCtxSharedModes.replay_view_eq]
  apply AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound decode c fallback
    (decisionClient c client) qHash qSeal qRaw
  · exact (isQueryBoundP_map_iff _ _ _).mpr (hash_bound c client qHash hashBound initialReduction)
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (target_bound c _ forward_seal_class client qSeal sealBound initialReduction)
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (target_bound c _ forward_raw_class client qRaw rawBound initialReduction)
  · exact small

/-- The adjacent privacy comparison uses the same dynamic source and reduction, with the existing ordinary-random replay endpoint and both explicit IND$ reductions. -/
theorem selected_privacy (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp Spec Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame true decode c client).boolDistAdvantage
      (AdaptiveCtxPrivacyGuard.randomView decode (decisionClient c client))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c (decisionClient c client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
          (AdaptiveCtxReceive.wrapped decode (decisionClient c client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrivacyGuard.viewReduction decode (decisionClient c client))) := by
  rw [source_view, AdaptiveCtxSharedModes.real_view_eq]
  apply AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound decode c fallback
    (decisionClient c client) qHash qSeal qRaw
  · exact (isQueryBoundP_map_iff _ _ _).mpr (hash_bound c client qHash hashBound initialReduction)
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (target_bound c _ forward_seal_class client qSeal sealBound initialReduction)
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (target_bound c _ forward_raw_class client qRaw rawBound initialReduction)
  · exact small

open AdaptiveCtxPlaintextQueryBounds

def PlaintextCost : Spec.Domain → Nat
  | .inl query => SourcePlaintextCost query
  | .inr _ => 0

def PlaintextBound {Result : Type} (client : OracleComp Spec Result) (bytes : Nat) : Prop :=
  client.IsQueryBound bytes (fun query available => PlaintextCost query ≤ available)
    (fun query available => available - PlaintextCost query)

set_option backward.isDefEq.respectTransparency false in
/-- Only a selected seal passes its original plaintext to the target challenger; local known-key encryption contributes no hidden target request. -/
theorem plaintext_step (c : Pqxdh.Crypto) (query : Spec.Domain) (state : ReductionState) :
    SourcePlaintextBound ((AdaptiveCtxDynamicKnownKeys.reductionImpl c query).run state)
      (PlaintextCost query) := by
  cases query with
  | inl selected =>
    simp only [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, bind_pure_comp,
      SourcePlaintextBound, isQueryBound_map_iff, isQueryBound_query_iff, PlaintextCost]
    exact Nat.le_refl _
  | inr known =>
    apply AdaptiveCtxSharedFamilyBounds.no_target_seal_plaintext
    exact target_step c SourceSeal forward_seal_class (.inr known) state

/-- The complete adaptive wrapper preserves the weighted selected plaintext-byte budget. -/
theorem plaintext_bound (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp Spec Result) (qBytes : Nat) (bounded : PlaintextBound client qBytes)
    (state : ReductionState) :
    SourcePlaintextBound (AdaptiveCtxDynamicKnownKeys.wrapped c client state) qBytes := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => PlaintextCost query)
    (fun firstBound nextBound => AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind _ _ _ _ firstBound nextBound)
    (fun query _available state _allowed => plaintext_step c query state)
    (fun _query _available allowed => by dsimp; omega) state

/-- The concrete ordinary decision client retains the exact selected plaintext accounting used by its inherited INT/IND$ reduction resource theorems. -/
theorem decision_plaintext_bound (c : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (qBytes : Nat) (bounded : PlaintextBound client qBytes) :
    SourcePlaintextBound (decisionClient c client) qBytes := by
  simpa only [decisionClient, SourcePlaintextBound, isQueryBound_map_iff] using
    plaintext_bound c client qBytes bounded initialReduction

end BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.target_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.target_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.target_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.hash_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.hash_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.decision_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.selected_integrity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.selected_integrity

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.selected_privacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.selected_privacy

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.plaintext_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.plaintext_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.decision_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownBounds.decision_plaintext_bound
