import BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds
import BeaconcryptCore.Computational.AdaptiveRawKeyPreparation

/-!
Eighteen statements add actual probabilistic non-target preparation to the shared-cache CTX experiment. The complete evaluated generator-order law retains the entire preparation, original replies and final source state. The selected key stays in the ordinary challenger. The displayed prepared integrity/privacy reductions, their sealing caps, every uniform draw and random body/tag byte are explicitly bounded. A concrete independent preparation draws 32 bytes per other key, and the source separately draws 32 bytes for its selected key. These components do not assert source evolving-key independence, target/session selection, reveal freshness or global protocol security.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxSharedFamily
open AdaptiveCtxQueryBounds AdaptiveCtxSharedFamilyBounds

structure Prepared (Context : Type) (count : Nat) where
  context : Context
  keys : Fin count → CtxKey

noncomputable def wrapped {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result) :
    OracleComp ReceiveSpec (Prepared Context count × (Result × ReductionState count)) := do
  let prepared ← OracleComp.liftComp prepare ReceiveSpec
  let result ← AdaptiveCtxSharedFamily.wrapped decode c prepared.keys (client prepared.context) (initialReduction count)
  pure (prepared, result)

noncomputable def source {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    ProbComp (Prepared Context count × (Result × SourceState count)) := do
  let prepared ← prepare
  let result ← sourceGame selectedDecode decode c prepared.keys (client prepared.context)
  pure (prepared, result)

def reassociate {Context Result : Type} {count : Nat}
    (result : (Prepared Context count × (Result × ReductionState count)) × CanonicalState) :
    Prepared Context count × (Result × SourceState count) :=
  (result.1.1, result.1.2.1, project (result.1.2.2, result.2))

/-- Preparation randomness preserves the complete selected challenger state. -/
theorem canonical_uniform {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (work : ProbComp Result) (state : CanonicalState) :
    (simulateQ (canonicalImpl decode c key) (OracleComp.liftComp work ReceiveSpec)).run state =
      (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- Independent generation order is checked against the full retained setup and continued execution. -/
theorem prepared_interpretation {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    EvalDistEq (source prepare selectedDecode decode c client)
      (do
        let selectedKey ← $ᵗ CtxKey
        reassociate <$> canonicalGame selectedDecode c selectedKey (wrapped prepare decode c client)) := by
  simp only [source, uniform_interpretation, wrapped, canonicalGame, simulateQ_bind,
    StateT.run_bind, simulateQ_pure, StateT.run_pure, canonical_uniform, map_bind,
    bind_assoc, bind_map_left, map_pure]
  exact JointEagerTable.independent_comm_spmf prepare ($ᵗ CtxKey) _

/-- Preparation uniform draws consume no target nonuniform resource. -/
theorem lift_no_class (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work ReceiveSpec).IsQueryBoundP p 0 := by
  let : unifSpec ⊂ₒ ReceiveSpec := SubSpec.trans
    (inferInstance : unifSpec ⊂ₒ unifSpec + CtxAdversarySpec)
    (inferInstance : unifSpec + CtxAdversarySpec ⊂ₒ ReceiveSpec)
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := ReceiveSpec) (p := fun _ => False)
    (hpq := fun query => by
      change False ↔ p (.inl (.inl query))
      simp only [noUniform query])
    (OracleComp.isQueryBoundP_false work 0)

/-- Every actual preparation uniform draw is included in the reduction budget. -/
theorem lift_uniform_bound {Result : Type} (work : ProbComp Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (OracleComp.liftComp work ReceiveSpec).IsQueryBoundP SourceUniform bound := by
  let : unifSpec ⊂ₒ ReceiveSpec := SubSpec.trans
    (inferInstance : unifSpec ⊂ₒ unifSpec + CtxAdversarySpec)
    (inferInstance : unifSpec + CtxAdversarySpec ⊂ₒ ReceiveSpec)
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := ReceiveSpec) (p := fun _ => True)
    (hpq := fun _query => Iff.rfl)
  exact (OracleComp.isQueryBoundP_true_iff work bound).mpr bounded

/-- Prepared execution retains the displayed nonuniform wrapper cap. -/
theorem prepared_class_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) (bound : Nat)
    (bounded : ∀ prepared : Prepared Context count, (AdaptiveCtxSharedFamily.wrapped decode c prepared.keys
      (client prepared.context) (initialReduction count)).IsQueryBoundP p bound) :
    (wrapped prepare decode c client).IsQueryBoundP p bound := by
  unfold wrapped
  rw [← Nat.zero_add bound]
  apply isQueryBoundP_bind (n := 0) (m := bound) (lift_no_class p noUniform prepare)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using bounded prepared

/-- Preparation and caller uniform queries add in the actual reduction program. -/
theorem prepared_uniform_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (setupCount clientCount : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (bounded : ∀ context, (client context).IsQueryBoundP (RouteClass false) clientCount) :
    (wrapped prepare decode c client).IsQueryBoundP SourceUniform (setupCount + clientCount) := by
  unfold wrapped
  apply isQueryBoundP_bind (lift_uniform_bound prepare setupCount setupBound)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff, TargetResource, Bool.false_eq_true, ite_false] using
    wrapped_route_bound decode c prepared.keys false (client prepared.context) clientCount
      (bounded prepared.context) (initialReduction count)

/-- Actual preparation preserves all four routed source resource caps. -/
theorem prepared_budgets {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (wrapped prepare decode c client).IsQueryBoundP SourceUniform (setupCount + qUniform) ∧
      (wrapped prepare decode c client).IsQueryBoundP SourceHash qHash ∧
      (wrapped prepare decode c client).IsQueryBoundP SourceSeal qSeal ∧
      (wrapped prepare decode c client).IsQueryBoundP IsRawQuery qRaw := by
  refine ⟨prepared_uniform_bound prepare decode c client setupCount qUniform setupBound uniformBound, ?_, ?_, ?_⟩
  · exact prepared_class_bound prepare decode c client SourceHash (by intro coin; simp [SourceHash]) qHash
      (fun prepared => (wrapped_budgets decode c prepared.keys (client prepared.context) qUniform qHash qSeal qRaw
        (uniformBound _) (hashBound _) (sealBound _) (rawBound _) (initialReduction count)).2.1)
  · exact prepared_class_bound prepare decode c client SourceSeal (by intro coin; simp [SourceSeal]) qSeal
      (fun prepared => (wrapped_budgets decode c prepared.keys (client prepared.context) qUniform qHash qSeal qRaw
        (uniformBound _) (hashBound _) (sealBound _) (rawBound _) (initialReduction count)).2.2.1)
  · exact prepared_class_bound prepare decode c client IsRawQuery (by intro coin; simp [IsRawQuery]) qRaw
      (fun prepared => (wrapped_budgets decode c prepared.keys (client prepared.context) qUniform qHash qSeal qRaw
        (uniformBound _) (hashBound _) (sealBound _) (rawBound _) (initialReduction count)).2.2.2)

noncomputable def decisionClient {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool) : OracleComp ReceiveSpec Bool :=
  (fun result => result.2.1) <$> wrapped prepare decode c client

/-- The prepared source decision has the same evaluated distribution as its ordinary canonical wrapper. -/
theorem prepared_view_eq {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool) :
    EvalDistEq ((fun result => result.2.1) <$> source prepare selectedDecode decode c client)
      (AdaptiveCtxPrivacyGuard.canonicalView selectedDecode c (decisionClient prepare decode c client)) := by
  refine ((prepared_interpretation prepare selectedDecode decode c client).map
    (fun (result : Prepared Context count × (Bool × SourceState count)) => result.2.1)).trans ?_
  simp only [map_bind, Functor.map_map, reassociate, AdaptiveCtxPrivacyGuard.canonicalView,
    AdaptiveCtxPrefixValidation.retainedCanonicalGame, canonicalGame, decisionClient, simulateQ_map,
    StateT.run_map, bind_pure_comp]
  exact EvalDistEq.refl _

/-- The original source charges preparation, selected-key generation and all shared-cache execution. -/
theorem prepared_source_uniform {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (source prepare selectedDecode decode c client).IsTotalQueryBound
      (setupCount + (32 + (qUniform + 64 * (qHash + qSeal + qRaw)))) := by
  unfold source
  apply isTotalQueryBound_bind setupBound
  intro prepared
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    source_uniform_bound selectedDecode decode c prepared.keys (client prepared.context)
      qUniform qHash qSeal qRaw (uniformBound _) (hashBound _) (sealBound _) (rawBound _)

/-- Preparation adds no encryption plaintext while preserving all submitted selected body bytes. -/
theorem prepared_plaintext_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (qBytes : Nat) (bounded : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound (wrapped prepare decode c client) qBytes := by
  unfold wrapped
  rw [← Nat.zero_add qBytes]
  apply AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind _ _
    (firstBytes := 0) (nextBytes := qBytes)
    (no_target_seal_plaintext _ (lift_no_class SourceSeal (by intro coin; simp [SourceSeal]) prepare))
  intro prepared
  simpa only [bind_pure_comp, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound, isQueryBound_map_iff] using
    wrapped_plaintext_bound decode c prepared.keys (client prepared.context) qBytes (bounded _) (initialReduction count)

noncomputable def independentSetup {Context : Type} (count : Nat) (context : Context) :
    ProbComp (Prepared Context count) := do
  let keys ← $ᵗ (Fin count → CtxKey)
  pure ⟨context, keys⟩

/-- The concrete independent other-key sampler pays 32 byte-valued draws per key. -/
theorem independent_setup_bound {Context : Type} (count : Nat) (context : Context) :
    (independentSetup count context).IsTotalQueryBound (count * 32) := by
  simpa only [independentSetup, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    AdaptiveRawKeyPreparation.key_family_bound count

/-- The exact prepared decision client retains every source query cap. -/
theorem prepared_decision_budgets {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (decisionClient prepare decode c client).IsQueryBoundP SourceUniform (setupCount + qUniform) ∧
      (decisionClient prepare decode c client).IsQueryBoundP SourceHash qHash ∧
      (decisionClient prepare decode c client).IsQueryBoundP SourceSeal qSeal ∧
      (decisionClient prepare decode c client).IsQueryBoundP IsRawQuery qRaw := by
  simpa only [decisionClient, isQueryBoundP_map_iff] using
    prepared_budgets prepare decode c client setupCount qUniform qHash qSeal qRaw
      setupBound uniformBound hashBound sealBound rawBound

/-- The exact prepared decision client retains all submitted plaintext bytes. -/
theorem prepared_decision_plaintext {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool)
    (qBytes : Nat) (bounded : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound (decisionClient prepare decode c client) qBytes := by
  simpa only [decisionClient, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound, isQueryBound_map_iff] using
    prepared_plaintext_bound prepare decode c client qBytes bounded

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The prepared source integrity hop uses the displayed ordinary IND$ and indexed INT-CTXT reductions. -/
theorem prepared_integrity_bound {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (((fun result => result.2.1) <$> source prepare selectedDecode decode c client).boolDistance
      (AdaptiveCtxPrivacyGuard.replayView selectedDecode c (decisionClient prepare decode c client))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare decode c client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  have budgets := prepared_decision_budgets prepare decode c client setupCount qUniform qHash qSeal qRaw
    setupBound uniformBound hashBound sealBound rawBound
  have bound := AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound selectedDecode c fallback
    (decisionClient prepare decode c client) qHash qSeal qRaw budgets.2.1 budgets.2.2.1 budgets.2.2.2 small
  have equal := prepared_view_eq prepare selectedDecode decode c client
  have equal_true :
      𝒟[(fun result => result.2.1) <$> source prepare selectedDecode decode c client] {true} =
        𝒟[AdaptiveCtxPrivacyGuard.canonicalView selectedDecode c
          (decisionClient prepare decode c client)] {true} := by
    rw [EvalDistEq.evalDist_eq equal]
  simpa only [ProbComp.boolDistance, equal_true] using bound

/-- The prepared source privacy hop additionally charges the ordinary ciphertext-view reduction. -/
theorem prepared_privacy_bound {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (((fun result => result.2.1) <$> source prepare selectedDecode decode c client).boolDistance
      (AdaptiveCtxPrivacyGuard.randomView selectedDecode (decisionClient prepare decode c client))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare decode c client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare decode c client))) := by
  have budgets := prepared_decision_budgets prepare decode c client setupCount qUniform qHash qSeal qRaw
    setupBound uniformBound hashBound sealBound rawBound
  have bound := AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound selectedDecode c fallback
    (decisionClient prepare decode c client) qHash qSeal qRaw budgets.2.1 budgets.2.2.1 budgets.2.2.2 small
  have equal := prepared_view_eq prepare selectedDecode decode c client
  have equal_true :
      𝒟[(fun result => result.2.1) <$> source prepare selectedDecode decode c client] {true} =
        𝒟[AdaptiveCtxPrivacyGuard.canonicalView selectedDecode c
          (decisionClient prepare decode c client)] {true} := by
    rw [EvalDistEq.evalDist_eq equal]
  simpa only [ProbComp.boolDistance, equal_true] using bound

/-- All prepared ordinary reductions pay their setup, uniform and selected-encryption costs. -/
theorem prepared_reduction_bounds {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (fallback : ModifiedNonceAeadForgery) (index : Nat) :
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
      (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare decode c client)) index).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + qUniform + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
      (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare decode c client)) index).MakesAtMostSealQueries qSeal ∧
    (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash).main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + qUniform + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash).main.IsQueryBoundP IsModifiedNonceAeadSealQuery (qSeal + 1) ∧
    (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare decode c client)).main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + qUniform + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare decode c client)).main.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal := by
  have bounds := prepared_decision_budgets prepare decode c client setupCount qUniform qHash qSeal qRaw
    setupBound uniformBound hashBound sealBound rawBound
  have forger := AdaptiveCtxQueryBounds.indexedReduction_bounds selectedDecode fallback
    (decisionClient prepare decode c client) (setupCount + qUniform) qHash qSeal qRaw index
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  exact ⟨forger.1, forger.2,
    AdaptiveCtxPrefixValidation.validationReduction_uniform_bound selectedDecode c (decisionClient prepare decode c client)
      (setupCount + qUniform) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrefixValidation.validationReduction_seal_bound selectedDecode c (decisionClient prepare decode c client)
      qHash qSeal bounds.2.2.1,
    AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound selectedDecode (decisionClient prepare decode c client)
      (setupCount + qUniform) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound selectedDecode (decisionClient prepare decode c client)
      qSeal bounds.2.2.1⟩

/-- Every complete real or random ordinary challenger pays its key or body/tag generation costs. -/
theorem prepared_experiment_bounds {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (qBytes : Nat) (bytesBound : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash)).IsTotalQueryBound (32 + (setupCount + qUniform + 64 * (qHash + qSeal + qRaw))) ∧
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare decode c client) qHash)).IsTotalQueryBound (setupCount + qUniform + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * (qSeal + 1)) ∧
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare decode c client))).IsTotalQueryBound (32 + (setupCount + qUniform + 64 * (qHash + qSeal + qRaw))) ∧
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare decode c client))).IsTotalQueryBound (setupCount + qUniform + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) := by
  have bounds := prepared_decision_budgets prepare decode c client setupCount qUniform qHash qSeal qRaw
    setupBound uniformBound hashBound sealBound rawBound
  have bytes := prepared_decision_plaintext prepare decode c client qBytes bytesBound
  exact ⟨AdaptiveCtxPrefixValidation.validationReal_uniform_bound selectedDecode c (decisionClient prepare decode c client)
    (setupCount + qUniform) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound selectedDecode c (decisionClient prepare decode c client)
      (setupCount + qUniform) qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 bytes,
    AdaptiveCtxPrivacyQueryBounds.viewReal_uniform_bound selectedDecode c (decisionClient prepare decode c client)
      (setupCount + qUniform) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrivacyQueryBounds.viewRandom_uniform_bound selectedDecode (decisionClient prepare decode c client)
      (setupCount + qUniform) qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 bytes⟩

/-- The concrete original source charges every other key and its selected key plus all execution draws. -/
theorem independent_source_bound {Context Result : Type} (count : Nat) (context : Context)
    (selectedDecode : RawDecoder) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : ∀ context, (client context).IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : ∀ context, (client context).IsQueryBoundP (RouteClass true) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (source (independentSetup count context) selectedDecode decode c client).IsTotalQueryBound
      ((count + 1) * 32 + (qUniform + 64 * (qHash + qSeal + qRaw))) := by
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
    prepared_source_uniform (independentSetup count context) selectedDecode decode c client
      (count * 32) qUniform qHash qSeal qRaw (independent_setup_bound count context)
      uniformBound hashBound sealBound rawBound

end BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.canonical_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.canonical_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.lift_no_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.lift_no_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.lift_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.lift_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_class_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_view_eq

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_source_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.independent_setup_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.independent_setup_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_decision_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_decision_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_decision_plaintext

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_privacy_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_experiment_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.prepared_experiment_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.independent_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation.independent_source_bound
