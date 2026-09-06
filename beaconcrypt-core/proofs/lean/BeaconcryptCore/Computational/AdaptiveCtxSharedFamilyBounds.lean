import BeaconcryptCore.Computational.AdaptiveCtxSharedFamily
import BeaconcryptCore.Computational.AdaptiveCtxPrefixQueryBounds
import BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds

/-!
Nineteen statements account for the complete selected shared-cache source and every constructed ordinary reduction. Original selected traffic remains separate from all forwarded other-key hash work. Submitted selected plaintext bytes and random-challenger tag bytes are counted. The exact routed hash class is all original public hashing plus other-key seals and raw attempts. Bounds quantify over all possible adaptive replies; malformed, rejected and repeated requests remain included. Local parsing, AEAD, history operations and copying remain computation rather than free ambient work.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxSharedFamily
open AdaptiveCtxQueryBounds AdaptiveCtxPrefixQueryBounds

/-- The actual fixed-key canonical program charges all caller coins and possible digest misses. -/
theorem canonical_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP SourceUniform qUniform)
    (hashBound : client.IsQueryBoundP SourceHash qHash)
    (sealBound : client.IsQueryBoundP SourceSeal qSeal)
    (rawBound : client.IsQueryBoundP IsRawQuery qRaw) :
    (canonicalGame decode c key client).IsTotalQueryBound (qUniform + 64 * (qHash + qSeal + qRaw)) := by
  have bound := run_uniform_pair_bound (AdaptiveCtxPrefix.sourceImpl true decode c key)
    (sourceImpl_uniform_step true decode c key) client qUniform (qHash + qSeal + qRaw)
    uniformBound (sourceWork_bound client qHash qSeal qRaw hashBound sealBound rawBound) initialState
  change (splitGame decode c key client).IsTotalQueryBound _ at bound
  rw [← canonicalGame_split] at bound
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using bound

/-- The complete family wrapper preserves its uniform, routed hash, selected seal and raw caps. -/
theorem wrapped_budgets {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) (state : ReductionState count) :
    (AdaptiveCtxSharedFamily.wrapped decode c keys client state).IsQueryBoundP SourceUniform qUniform ∧
      (AdaptiveCtxSharedFamily.wrapped decode c keys client state).IsQueryBoundP SourceHash qHash ∧
      (AdaptiveCtxSharedFamily.wrapped decode c keys client state).IsQueryBoundP SourceSeal qSeal ∧
      (AdaptiveCtxSharedFamily.wrapped decode c keys client state).IsQueryBoundP IsRawQuery qRaw :=
  ⟨wrapped_route_bound decode c keys false client qUniform uniformBound state,
    wrapped_route_bound decode c keys true client qHash hashBound state,
    wrapped_target_bound decode c keys _ AdaptiveCtxSharedTarget.forward_seal_class client qSeal sealBound state,
    wrapped_target_bound decode c keys _ AdaptiveCtxSharedTarget.forward_raw_class client qRaw rawBound state⟩

/-- Projecting to the original decision retains all four source-resource bounds. -/
theorem decision_budgets {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (decisionClient decode c keys client).IsQueryBoundP SourceUniform qUniform ∧
      (decisionClient decode c keys client).IsQueryBoundP SourceHash qHash ∧
      (decisionClient decode c keys client).IsQueryBoundP SourceSeal qSeal ∧
      (decisionClient decode c keys client).IsQueryBoundP IsRawQuery qRaw := by
  simpa only [decisionClient, isQueryBoundP_map_iff] using
    wrapped_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound (initialReduction count)

/-- The actual source program separately charges its 32-byte selected-key generation. -/
theorem source_uniform_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (sourceGame selectedDecode decode c keys client).IsTotalQueryBound
      (32 + (qUniform + 64 * (qHash + qSeal + qRaw))) := by
  rw [uniform_interpretation]
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro selectedKey
  have bounds := wrapped_budgets decode c keys client qUniform qHash qSeal qRaw
    uniformBound hashBound sealBound rawBound (initialReduction count)
  have canonical := canonical_uniform_bound selectedDecode c selectedKey
    (AdaptiveCtxSharedFamily.wrapped decode c keys client (initialReduction count))
      qUniform qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using canonical

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- Every stopped ordinary forger retains its exact uniform and selected-encryption caps. -/
theorem indexed_forger_bounds {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (FamilySpec count) Bool)
    (qUniform qHash qSeal qRaw index : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
      (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient decode c keys client)) index).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qUniform + 64 * (qHash + qSeal + qRaw)) ∧
      (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
        (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient decode c keys client)) index).MakesAtMostSealQueries qSeal := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact AdaptiveCtxQueryBounds.indexedReduction_bounds selectedDecode fallback (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw index bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2

/-- The validation reduction charges all uniform work and one additional empty-message seal. -/
theorem validation_bounds {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qUniform + 64 * (qHash + qSeal + qRaw)) ∧
      (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery (qSeal + 1) := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact ⟨AdaptiveCtxPrefixValidation.validationReduction_uniform_bound selectedDecode c (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrefixValidation.validationReduction_seal_bound selectedDecode c (decisionClient decode c keys client)
      qHash qSeal bounds.2.2.1⟩

/-- The ciphertext-view reduction charges all uniform work and the original encryption cap. -/
theorem privacy_bounds {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient decode c keys client)).main.IsQueryBoundP
        AdaptiveRawNonceAead.IsPrimitiveUniformQuery (qUniform + 64 * (qHash + qSeal + qRaw)) ∧
      (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient decode c keys client)).main.IsQueryBoundP
        IsModifiedNonceAeadSealQuery qSeal := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact ⟨AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound selectedDecode (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound selectedDecode (decisionClient decode c keys client) qSeal bounds.2.2.1⟩

open AdaptiveCtxPlaintextQueryBounds AdaptiveCtxPrivacyQueryBounds

def SelectedPlaintextCost {count : Nat} : (FamilySpec count).Domain → Nat
  | .inl query => SourcePlaintextCost query
  | .inr _ => 0

def SelectedPlaintextBound {count : Nat} {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bytes : Nat) : Prop :=
  client.IsQueryBound bytes (fun query available => SelectedPlaintextCost query ≤ available)
    (fun query available => available - SelectedPlaintextCost query)

/-- A computation with no selected sealing request submits no selected plaintext bytes. -/
theorem no_target_seal_plaintext {Result : Type} (client : OracleComp ReceiveSpec Result)
    (bounded : client.IsQueryBoundP SourceSeal 0) : SourcePlaintextBound client 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [SourcePlaintextBound, isQueryBound_query_bind_iff]
      have cost : SourcePlaintextCost query = 0 := by
        have excluded := bounded.1
        cases query with
        | inl request =>
            cases request with
            | inl coin => rfl
            | inr operation =>
                cases operation with
                | inl hash => rfl
                | inr input => simp [SourceSeal] at excluded
        | inr raw => rfl
      refine ⟨by simp [cost], fun answer => ?_⟩
      simpa only [cost, Nat.sub_zero, SourcePlaintextBound] using ih answer (by simpa using bounded.2 answer)

set_option backward.isDefEq.respectTransparency false in
/-- Only a selected sealing request submits its original plaintext to the target challenger. -/
theorem plaintext_step {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (query : (FamilySpec count).Domain) (state : ReductionState count) :
    SourcePlaintextBound ((reductionImpl decode c keys query).run state) (SelectedPlaintextCost query) := by
  cases query with
  | inl selected =>
      simp only [AdaptiveCtxSharedFamily.reductionImpl, StateT.run, bind_pure_comp, SourcePlaintextBound,
        isQueryBound_map_iff, isQueryBound_query_iff, SelectedPlaintextCost]
      exact Nat.le_refl _
  | inr other =>
      apply no_target_seal_plaintext
      exact target_step_bound decode c keys SourceSeal AdaptiveCtxSharedTarget.forward_seal_class (.inr other) state

/-- The full adaptive family wrapper preserves the weighted selected plaintext-byte cap. -/
theorem wrapped_plaintext_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (qBytes : Nat) (bounded : SelectedPlaintextBound client qBytes) (state : ReductionState count) :
    SourcePlaintextBound (AdaptiveCtxSharedFamily.wrapped decode c keys client state) qBytes := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => SelectedPlaintextCost query)
    (fun firstBound nextBound => sourcePlaintext_bind _ _ _ _ firstBound nextBound)
    (fun query _available state _allowed => plaintext_step decode c keys query state)
    (fun _query _available allowed => by dsimp; omega) state

/-- The Boolean decision wrapper retains the complete submitted-plaintext budget. -/
theorem decision_plaintext_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool)
    (qBytes : Nat) (bounded : SelectedPlaintextBound client qBytes) :
    SourcePlaintextBound (decisionClient decode c keys client) qBytes := by
  simpa only [decisionClient, SourcePlaintextBound, isQueryBound_map_iff] using
    wrapped_plaintext_bound decode c keys client qBytes bounded (initialReduction count)

/-- The real validation experiment additionally samples its hidden 32-byte key. -/
theorem validation_real_uniform_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash)).IsTotalQueryBound
      (32 + (qUniform + 64 * (qHash + qSeal + qRaw))) := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact AdaptiveCtxPrefixValidation.validationReal_uniform_bound selectedDecode c (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2

/-- Random validation charges submitted body bytes and 16-byte tags, including its extra seal. -/
theorem validation_random_uniform_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (qBytes : Nat) (bytesBound : SelectedPlaintextBound client qBytes) :
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash)).IsTotalQueryBound
      (qUniform + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * (qSeal + 1)) := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact validationRandom_uniform_bound selectedDecode c (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
    (decision_plaintext_bound decode c keys client qBytes bytesBound)

/-- The real ciphertext-view experiment additionally samples its hidden 32-byte key. -/
theorem privacy_real_uniform_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient decode c keys client))).IsTotalQueryBound
      (32 + (qUniform + 64 * (qHash + qSeal + qRaw))) := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact viewReal_uniform_bound selectedDecode c (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2

/-- The random ciphertext-view experiment charges every submitted body byte and 16-byte tag. -/
theorem privacy_random_uniform_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (RouteClass false) qUniform)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (qBytes : Nat) (bytesBound : SelectedPlaintextBound client qBytes) :
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient decode c keys client))).IsTotalQueryBound
      (qUniform + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) := by
  have bounds := decision_budgets decode c keys client qUniform qHash qSeal qRaw uniformBound hashBound sealBound rawBound
  exact viewRandom_uniform_bound selectedDecode (decisionClient decode c keys client)
    qUniform qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
    (decision_plaintext_bound decode c keys client qBytes bytesBound)

def AllClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (FamilySpec count).Domain → Prop
  | .inl query => p query
  | .inr other => p other.2

def OtherClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (FamilySpec count).Domain → Prop
  | .inl _ => False
  | .inr other => p other.2

instance {count : Nat} (p : ReceiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (AllClass (count := count) p) := fun query => by
  cases query <;> unfold AllClass <;> infer_instance

instance {count : Nat} (p : ReceiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (OtherClass (count := count) p) := fun query => by
  cases query <;> unfold OtherClass <;> infer_instance

/-- Independent resource caps add to a bound on their union across all adaptive replies. -/
theorem family_union_bound {count : Nat} {Result : Type} (adversary : OracleComp (FamilySpec count) Result)
    (left right : (FamilySpec count).Domain → Prop) [DecidablePred left] [DecidablePred right]
    (qLeft qRight : ℕ) (hl : adversary.IsQueryBoundP left qLeft)
    (hr : adversary.IsQueryBoundP right qRight) :
    adversary.IsQueryBoundP (fun query => left query ∨ right query) (qLeft + qRight) := by
  induction adversary using OracleComp.inductionOn generalizing qLeft qRight with
  | pure _ => trivial
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hl hr ⊢
    refine ⟨?_, ?_⟩
    · by_cases hleft : left query <;> by_cases hright : right query
      all_goals simp only [hleft, hright, not_true_eq_false, false_or, not_false_eq_true, true_or] at hl hr ⊢
      all_goals omega
    · intro answer
      refine (ih answer _ _ (hl.2 answer) (hr.2 answer)).mono ?_
      by_cases hleft : left query <;> by_cases hright : right query
      all_goals simp only [hleft, hright, not_true_eq_false, false_or, not_false_eq_true, true_or, if_true, if_false] at hl hr ⊢
      all_goals omega

/-- Caller uniform requests at every key belong to the same original global uniform class. -/
theorem uniform_route_exact (count : Nat) :
    RouteClass (count := count) false = AllClass SourceUniform := by
  funext query
  cases query <;> rfl

/-- Routed hashes are precisely all public hashes plus other-key seals and raw attempts. -/
theorem hash_route_exact (count : Nat) :
    RouteClass (count := count) true = fun query =>
      (AllClass SourceHash query ∨ OtherClass SourceSeal query) ∨ OtherClass IsRawQuery query := by
  funext query
  cases query with
  | inl selected => simp [RouteClass, TargetResource, AllClass, OtherClass]
  | inr other =>
      rcases other with ⟨index, query⟩
      cases query with
      | inl request =>
          cases request with
          | inl coin => simp [RouteClass, AdaptiveCtxSharedHash.SourceClass, SourceWork, SourceUniform,
              AllClass, OtherClass, SourceHash, SourceSeal, IsRawQuery]
          | inr operation => cases operation <;>
              simp [RouteClass, AdaptiveCtxSharedHash.SourceClass, SourceWork, SourceUniform,
                AllClass, OtherClass, SourceHash, SourceSeal, IsRawQuery]
      | inr raw => simp [RouteClass, AdaptiveCtxSharedHash.SourceClass, SourceWork, SourceUniform,
          AllClass, OtherClass, SourceHash, SourceSeal, IsRawQuery]

/-- Original public, other-key seal and other-key raw caps bound the selected public-hash traffic. -/
theorem hash_route_bound {count : Nat} {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (qPublic qOtherSeal qOtherRaw : Nat)
    (publicBound : client.IsQueryBoundP (AllClass SourceHash) qPublic)
    (sealBound : client.IsQueryBoundP (OtherClass SourceSeal) qOtherSeal)
    (rawBound : client.IsQueryBoundP (OtherClass IsRawQuery) qOtherRaw) :
    client.IsQueryBoundP (RouteClass true) (qPublic + qOtherSeal + qOtherRaw) := by
  simpa only [hash_route_exact] using family_union_bound client _ _ _ _
    (family_union_bound client _ _ _ _ publicBound sealBound) rawBound

end BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.canonical_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.canonical_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.wrapped_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.wrapped_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.decision_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.source_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.indexed_forger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.indexed_forger_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.no_target_seal_plaintext' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.no_target_seal_plaintext

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.plaintext_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.plaintext_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.wrapped_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.wrapped_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.decision_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.decision_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_real_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_real_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_random_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.validation_random_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_real_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_real_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_random_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.privacy_random_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.family_union_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.family_union_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.uniform_route_exact' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.uniform_route_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.hash_route_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.hash_route_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.hash_route_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds.hash_route_bound
