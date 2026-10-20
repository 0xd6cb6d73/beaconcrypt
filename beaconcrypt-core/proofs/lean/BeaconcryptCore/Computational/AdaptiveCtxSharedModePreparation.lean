import BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds
import BeaconcryptCore.Computational.AdaptiveCtxSharedPreparation

/-!
Actual other-key preparation is included in the complete evaluated selected-key simulation. Independent generation order is checked through the entire retained setup and continuation. Ordinary forger, validation and view reductions pay setup, private sampling, hash work and target traffic. Real challenger keys and random body/tag bytes are counted.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation
open CtxRomAuth AdaptiveCtxQueryBounds AdaptiveCtxSharedModeFamily AdaptiveCtxSharedModeBounds AdaptiveCtxSharedModes
open AdaptiveCtxReceive hiding wrapped initialState

structure Prepared (Context : Type) (count : Nat) where
  context : Context
  keys : Fin count → CtxKey

noncomputable def wrapped {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result) :
    OracleComp ReceiveSpec (Prepared Context count × (Result × ReductionState count)) := do
  let prepared ← OracleComp.liftComp prepare ReceiveSpec
  let result ← AdaptiveCtxSharedModeFamily.wrapped real decode c prepared.keys (client prepared.context) (initialReduction count)
  pure (prepared, result)

noncomputable def source {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    ProbComp (Prepared Context count × (Result × SourceState count)) := do
  let prepared ← prepare
  let result ← sourceGame selectedReal selectedDecode real decode c prepared.keys (client prepared.context)
  pure (prepared, result)

def reassociate {Context Result : Type} {count : Nat}
    (result : (Prepared Context count × (Result × ReductionState count)) × AdaptiveCtxSharedModes.State) :
    Prepared Context count × (Result × SourceState count) :=
  (result.1.1, result.1.2.1, project (result.1.2.2, result.2))

set_option backward.isDefEq.respectTransparency false in
/-- Preparation randomness preserves the complete selected challenger state. -/
theorem mode_uniform {Result : Type} (selectedReal : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (work : ProbComp Result) (state : AdaptiveCtxSharedModes.State) :
    (simulateQ (targetImpl selectedReal decode c key) (OracleComp.liftComp work ReceiveSpec)).run state =
      (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  simp only [OracleComp.liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  change (simulateQ (targetImpl selectedReal decode c key) (ReceiveSpec.query (.inl (.inl coin)))).run before = _
  rw [simulateQ_spec_query]
  rw [target_run]
  have linked := local_forward selectedReal decode c key (.inl coin) before.1
  simp only [forwardIndex, forwardReply] at linked
  rw [linked]
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  rw [hash_uniform_step]
  simp only [Functor.map_map, afterHash]
  rfl


/-- Independent generation order is checked against the full retained setup and continued execution. -/
theorem prepared_interpretation {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    EvalDistEq (source prepare selectedReal selectedDecode real decode c client)
      (do
        let selectedKey ← $ᵗ CtxKey
        reassociate <$> (simulateQ (targetImpl selectedReal selectedDecode c selectedKey) (wrapped prepare real decode c client)).run AdaptiveCtxSharedModes.initialState) := by
  simp only [source, uniform_interpretation, targetGame, wrapped, simulateQ_bind,
    StateT.run_bind, simulateQ_pure, StateT.run_pure, mode_uniform, map_bind,
    bind_assoc, bind_map_left, map_pure]
  exact JointEagerTable.independent_comm_spmf prepare ($ᵗ CtxKey) _

open AdaptiveCtxSharedPreparation (lift_no_class lift_uniform_bound)

/-- Prepared execution retains the displayed nonuniform wrapper cap. -/
theorem prepared_class_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) (bound : Nat)
    (bounded : ∀ prepared : Prepared Context count, (AdaptiveCtxSharedModeFamily.wrapped real decode c prepared.keys
      (client prepared.context) (initialReduction count)).IsQueryBoundP p bound) :
    (wrapped prepare real decode c client).IsQueryBoundP p bound := by
  unfold wrapped
  rw [← Nat.zero_add bound]
  apply isQueryBoundP_bind (n := 0) (m := bound) (lift_no_class p noUniform prepare)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using bounded prepared

/-- Preparation and caller uniform queries add in the actual reduction program. -/
theorem prepared_uniform_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (setupCount clientCount privateCount : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (bounded : ∀ context, (client context).IsQueryBoundP UniformRoute clientCount)
    (privateBound : ∀ context, (client context).IsQueryBoundP (PrivateRoute real) privateCount) :
    (wrapped prepare real decode c client).IsQueryBoundP SourceUniform (setupCount + (clientCount + 64 * privateCount)) := by
  unfold wrapped
  apply isQueryBoundP_bind (lift_uniform_bound prepare setupCount setupBound)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    wrapped_uniform_bound real decode c prepared.keys (client prepared.context) clientCount privateCount
      (bounded prepared.context) (privateBound prepared.context) (initialReduction count)

noncomputable def decisionClient {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool) : OracleComp ReceiveSpec Bool :=
  (fun result => result.2.1) <$> wrapped prepare real decode c client

theorem prepared_view_eq {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedReal : Bool) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool) :
    EvalDistEq ((fun result => result.2.1) <$> source prepare selectedReal selectedDecode real decode c client)
      (targetView selectedReal selectedDecode c (decisionClient prepare real decode c client)) := by
  refine ((prepared_interpretation prepare selectedReal selectedDecode real decode c client).map
    (fun (result : Prepared Context count × (Bool × SourceState count)) => result.2.1)).trans ?_
  simp only [map_bind, Functor.map_map, reassociate, targetView, targetGame, decisionClient, simulateQ_map,
    StateT.run_map]
  exact EvalDistEq.refl _

theorem decision_class_bound {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool)
    (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) (bound : Nat)
    (bounded : ∀ prepared : Prepared Context count, (AdaptiveCtxSharedModeFamily.wrapped real decode c prepared.keys
      (client prepared.context) (initialReduction count)).IsQueryBoundP p bound) :
    (decisionClient prepare real decode c client).IsQueryBoundP p bound := by
  simpa only [decisionClient, isQueryBoundP_map_iff] using
    prepared_class_bound prepare real decode c client p noUniform bound bounded

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

theorem prepared_integrity_bound {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : Context → OracleComp (FamilySpec count) Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : ∀ context, (client context).IsQueryBoundP (HashRoute real) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal (((fun result => result.2.1) <$> source prepare true selectedDecode real decode c client).boolDistAdvantage
      ((fun result => result.2.1) <$> source prepare false selectedDecode real decode c client)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare real decode c client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare real decode c client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  have hashes := decision_class_bound prepare real decode c client SourceHash
    (fun _ => by simp [SourceHash]) qHash
    (fun prepared => wrapped_hash_bound real decode c prepared.keys (client prepared.context) qHash (hashBound _) _)
  have seals := decision_class_bound prepare real decode c client SourceSeal
    (fun _ => by simp [SourceSeal]) qSeal
    (fun prepared => wrapped_target_bound real decode c prepared.keys SourceSeal
      AdaptiveCtxSharedTarget.forward_seal_class (client prepared.context) qSeal (sealBound _) _)
  have raws := decision_class_bound prepare real decode c client IsRawQuery
    (fun _ => by simp [IsRawQuery]) qRaw
    (fun prepared => wrapped_target_bound real decode c prepared.keys IsRawQuery
      AdaptiveCtxSharedTarget.forward_raw_class (client prepared.context) qRaw (rawBound _) _)
  have bound := AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound selectedDecode c fallback
    (decisionClient prepare real decode c client) qHash qSeal qRaw hashes seals raws small
  have trueEq := prepared_view_eq prepare true selectedDecode real decode c client
  have falseEq := prepared_view_eq prepare false selectedDecode real decode c client
  rw [real_view_eq] at trueEq
  rw [replay_view_eq] at falseEq
  have trueMass :
      𝒟[(fun result => result.2.1) <$> source prepare true selectedDecode real decode c client] {true} =
        𝒟[AdaptiveCtxPrivacyGuard.canonicalView selectedDecode c
          (decisionClient prepare real decode c client)] {true} := by
    rw [EvalDistEq.evalDist_eq trueEq]
  have falseMass :
      𝒟[(fun result => result.2.1) <$> source prepare false selectedDecode real decode c client] {true} =
        𝒟[AdaptiveCtxPrivacyGuard.replayView selectedDecode c
          (decisionClient prepare real decode c client)] {true} := by
    rw [EvalDistEq.evalDist_eq falseEq]
  simpa only [ProbComp.boolDistAdvantage, trueMass, falseMass] using bound

noncomputable def independentSetup {Context : Type} (count : Nat) (context : Context) :
    ProbComp (Prepared Context count) := do
  let keys ← $ᵗ (Fin count → CtxKey)
  pure ⟨context, keys⟩

theorem independent_setup_bound {Context : Type} (count : Nat) (context : Context) :
    (independentSetup count context).IsTotalQueryBound (count * 32) := by
  simpa only [independentSetup, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    AdaptiveRawKeyPreparation.key_family_bound count

theorem prepared_decision_budgets {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qPrivate qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP UniformRoute qUniform)
    (privateBound : ∀ context, (client context).IsQueryBoundP (PrivateRoute real) qPrivate)
    (hashBound : ∀ context, (client context).IsQueryBoundP (HashRoute real) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (decisionClient prepare real decode c client).IsQueryBoundP SourceUniform (setupCount + (qUniform + 64 * qPrivate)) ∧
      (decisionClient prepare real decode c client).IsQueryBoundP SourceHash qHash ∧
      (decisionClient prepare real decode c client).IsQueryBoundP SourceSeal qSeal ∧
      (decisionClient prepare real decode c client).IsQueryBoundP IsRawQuery qRaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [decisionClient, isQueryBoundP_map_iff] using
      prepared_uniform_bound prepare real decode c client setupCount qUniform qPrivate setupBound uniformBound privateBound
  · exact decision_class_bound prepare real decode c client SourceHash (fun _ => by simp [SourceHash]) qHash
      (fun prepared => wrapped_hash_bound real decode c prepared.keys (client prepared.context) qHash (hashBound _) _)
  · exact decision_class_bound prepare real decode c client SourceSeal (fun _ => by simp [SourceSeal]) qSeal
      (fun prepared => wrapped_target_bound real decode c prepared.keys SourceSeal
        AdaptiveCtxSharedTarget.forward_seal_class (client prepared.context) qSeal (sealBound _) _)
  · exact decision_class_bound prepare real decode c client IsRawQuery (fun _ => by simp [IsRawQuery]) qRaw
      (fun prepared => wrapped_target_bound real decode c prepared.keys IsRawQuery
        AdaptiveCtxSharedTarget.forward_raw_class (client prepared.context) qRaw (rawBound _) _)

open AdaptiveCtxSharedFamilyBounds (SelectedPlaintextBound no_target_seal_plaintext)

theorem prepared_plaintext_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Result)
    (qBytes : Nat) (bounded : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound (wrapped prepare real decode c client) qBytes := by
  unfold wrapped
  rw [← Nat.zero_add qBytes]
  apply AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind _ _
    (firstBytes := 0) (nextBytes := qBytes)
    (no_target_seal_plaintext _ (lift_no_class SourceSeal (by intro coin; simp [SourceSeal]) prepare))
  intro prepared
  simpa only [bind_pure_comp, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound, isQueryBound_map_iff] using
    wrapped_plaintext_bound real decode c prepared.keys (client prepared.context) qBytes (bounded _) (initialReduction count)

theorem prepared_decision_plaintext {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (client : Context → OracleComp (FamilySpec count) Bool)
    (qBytes : Nat) (bounded : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound (decisionClient prepare real decode c client) qBytes := by
  simpa only [decisionClient, AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound, isQueryBound_map_iff] using
    prepared_plaintext_bound prepare real decode c client qBytes bounded

theorem prepared_reduction_bounds {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qPrivate qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP UniformRoute qUniform)
    (privateBound : ∀ context, (client context).IsQueryBoundP (PrivateRoute real) qPrivate)
    (hashBound : ∀ context, (client context).IsQueryBoundP (HashRoute real) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (fallback : ModifiedNonceAeadForgery) (index : Nat) :
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
      (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare real decode c client)) index).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
      (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient prepare real decode c client)) index).MakesAtMostSealQueries qSeal ∧
    (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare real decode c client) qHash).main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare real decode c client) qHash).main.IsQueryBoundP IsModifiedNonceAeadSealQuery (qSeal + 1) ∧
    (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare real decode c client)).main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw)) ∧
    (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare real decode c client)).main.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal := by
  have bounds := prepared_decision_budgets prepare real decode c client setupCount qUniform qPrivate qHash qSeal qRaw
    setupBound uniformBound privateBound hashBound sealBound rawBound
  have forger := AdaptiveCtxQueryBounds.indexedReduction_bounds selectedDecode fallback
    (decisionClient prepare real decode c client) (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw index
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  exact ⟨forger.1, forger.2,
    AdaptiveCtxPrefixValidation.validationReduction_uniform_bound selectedDecode c (decisionClient prepare real decode c client)
      (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrefixValidation.validationReduction_seal_bound selectedDecode c (decisionClient prepare real decode c client)
      qHash qSeal bounds.2.2.1,
    AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound selectedDecode (decisionClient prepare real decode c client)
      (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound selectedDecode (decisionClient prepare real decode c client)
      qSeal bounds.2.2.1⟩

/-- Every complete real or random ordinary challenger pays its key or body/tag generation costs. -/
theorem prepared_experiment_bounds {Context : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Bool)
    (setupCount qUniform qPrivate qHash qSeal qRaw : Nat) (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP UniformRoute qUniform)
    (privateBound : ∀ context, (client context).IsQueryBoundP (PrivateRoute real) qPrivate)
    (hashBound : ∀ context, (client context).IsQueryBoundP (HashRoute real) qHash)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (qBytes : Nat) (bytesBound : ∀ context, SelectedPlaintextBound (client context) qBytes) :
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare real decode c client) qHash)).IsTotalQueryBound (32 + (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw))) ∧
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient prepare real decode c client) qHash)).IsTotalQueryBound (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * (qSeal + 1)) ∧
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare real decode c client))).IsTotalQueryBound (32 + (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw))) ∧
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient prepare real decode c client))).IsTotalQueryBound (setupCount + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) := by
  have bounds := prepared_decision_budgets prepare real decode c client setupCount qUniform qPrivate qHash qSeal qRaw
    setupBound uniformBound privateBound hashBound sealBound rawBound
  have bytes := prepared_decision_plaintext prepare real decode c client qBytes bytesBound
  exact ⟨AdaptiveCtxPrefixValidation.validationReal_uniform_bound selectedDecode c (decisionClient prepare real decode c client)
    (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound selectedDecode c (decisionClient prepare real decode c client)
      (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 bytes,
    AdaptiveCtxPrivacyQueryBounds.viewReal_uniform_bound selectedDecode c (decisionClient prepare real decode c client)
      (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrivacyQueryBounds.viewRandom_uniform_bound selectedDecode (decisionClient prepare real decode c client)
      (setupCount + (qUniform + 64 * qPrivate)) qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 bytes⟩

end BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.mode_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.mode_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_class_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_view_eq

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.decision_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.decision_class_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.independent_setup_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.independent_setup_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_decision_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_decision_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_decision_plaintext

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_experiment_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation.prepared_experiment_bounds
