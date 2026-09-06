import BeaconcryptCore.Computational.AdaptiveCtxSharedModeFamily
import BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds
import BeaconcryptCore.Computational.AdaptiveCtxSharedFamilyBounds

/-!
The selected mixed-family integrity hop uses the completed ordinary CTX reductions. Query bounds count forwarded shared hashing, processed-key private sampling, selected raw attempts and seals, and actual selected plaintext bytes. Every adaptive reply is covered; failed requests remain charged.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds
open CtxRomAuth AdaptiveCtxQueryBounds AdaptiveCtxSharedHash
open AdaptiveCtxReceive hiding reductionImpl wrapped
open AdaptiveCtxSharedTarget AdaptiveCtxSharedModeFamily AdaptiveCtxSharedReplayBounds

def TargetClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (FamilySpec count).Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance {count : Nat} (p : ReceiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (TargetClass (count := count) p) := fun query => by
  cases query <;> unfold TargetClass <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Only original selected requests can consume a target-only resource. -/
theorem target_step_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False)
    (query : (FamilySpec count).Domain) (state : ReductionState count) :
    ((reductionImpl real decode c keys query).run state).IsQueryBoundP p
      (if TargetClass p query then 1 else 0) := by
  cases query with
  | inl selected =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass]
      exact (isQueryBoundP_query_iff p selected _).mpr (by intro hit; simp [hit])
  | inr other =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass, if_false]
      apply forward_bound
      simp only [unavailable]
      exact isQueryBoundP_false _ 0

/-- The full adaptive wrapper preserves each selected-only resource cap. -/
theorem wrapped_target_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (TargetClass p) bound) (state : ReductionState count) :
    (wrapped real decode c keys client state).IsQueryBoundP p bound :=
  bounded.simulateQ_run_StateT_of_step (target_step_bound real decode c keys p unavailable) state


def HashRoute {count : Nat} (real : Fin count → Bool) : (FamilySpec count).Domain → Prop
  | .inl query => SourceHash query
  | .inr other => ModeHash (real other.1) other.2

instance {count : Nat} (real : Fin count → Bool) : DecidablePred (HashRoute real) := fun query => by
  cases query <;> unfold HashRoute <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem hash_step_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : ReductionState count) :
    ((reductionImpl real decode c keys query).run state).IsQueryBoundP SourceHash
      (if HashRoute real query then 1 else 0) := by
  cases query with
  | inl selected =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, HashRoute]
      exact (isQueryBoundP_query_iff SourceHash selected _).mpr (by intro hit; simp [hit])
  | inr other =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, HashRoute]
      apply forward_bound
      simp only [forward_hash_class]
      exact mode_hash_step (real other.1) (decode other.1) c (keys other.1) other.2 (state.others other.1)

theorem wrapped_hash_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (HashRoute real) bound) (state : ReductionState count) :
    (wrapped real decode c keys client state).IsQueryBoundP SourceHash bound :=
  bounded.simulateQ_run_StateT_of_step (hash_step_bound real decode c keys) state

def UniformRoute {count : Nat} : (FamilySpec count).Domain → Prop
  | .inl query => SourceUniform query
  | .inr other => SourceUniform other.2

def PrivateRoute {count : Nat} (real : Fin count → Bool) : (FamilySpec count).Domain → Prop
  | .inl _ => False
  | .inr other => ModePrivate (real other.1) other.2

instance {count : Nat} : DecidablePred (UniformRoute (count := count)) := fun query => by
  cases query <;> unfold UniformRoute <;> infer_instance

instance {count : Nat} (real : Fin count → Bool) : DecidablePred (PrivateRoute real) := fun query => by
  cases query <;> unfold PrivateRoute <;> infer_instance

theorem private_not_uniform {count : Nat} (real : Fin count → Bool) (query : (FamilySpec count).Domain)
    (privateCall : PrivateRoute real query) : ¬UniformRoute query := by
  cases query with
  | inl selected => exact privateCall.elim
  | inr other => exact mode_private_not_uniform (real other.1) other.2 privateCall

set_option backward.isDefEq.respectTransparency false in
theorem uniform_step_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : ReductionState count) :
    ((reductionImpl real decode c keys query).run state).IsQueryBoundP SourceUniform
      (if UniformRoute query then 1 else if PrivateRoute real query then 64 else 0) := by
  cases query with
  | inl selected =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
        UniformRoute, PrivateRoute, if_false]
      exact (isQueryBoundP_query_iff SourceUniform selected _).mpr (by intro hit; simp [hit])
  | inr other =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, UniformRoute, PrivateRoute]
      apply forward_bound
      simp only [forward_uniform_class]
      exact mode_uniform_step (real other.1) (decode other.1) c (keys other.1) other.2 (state.others other.1)

theorem wrapped_uniform_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (qUniform qPrivate : Nat)
    (uniformBound : client.IsQueryBoundP UniformRoute qUniform)
    (privateBound : client.IsQueryBoundP (PrivateRoute real) qPrivate) (entry : ReductionState count) :
    (wrapped real decode c keys client entry).IsQueryBoundP SourceUniform
      (qUniform + 64 * qPrivate) := by
  have vector := uniformBound.and_isQueryBound_pair privateBound
  exact vector.simulateQ_run_of_step (mapBudget := fun budget : Nat × Nat => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if UniformRoute query then 1 else if PrivateRoute real query then 64 else 0)
    (combine := Nat.add)
    (fun stepBound restBound => isQueryBoundP_bind stepBound (fun result _ => restBound result))
    (fun query _ state _ => uniform_step_bound real decode c keys query state)
    (fun query budget allowed => by
      by_cases coins : UniformRoute query
      · have noPrivate : ¬PrivateRoute real query := fun hit => private_not_uniform real query hit coins
        simp only [coins, noPrivate, if_true, if_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        simp only [not_true_eq_false, false_or] at allowed
        omega
      · by_cases privateCall : PrivateRoute real query
        · simp only [coins, privateCall, if_true, if_false] at allowed ⊢
          change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
          simp only [not_true_eq_false, false_or] at allowed
          omega
        · simp only [coins, privateCall, if_false]
          change 0 + (budget.1 + 64 * budget.2) = budget.1 + 64 * budget.2
          exact Nat.zero_add _) entry

theorem decision_budgets {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool)
    (qUniform qPrivate qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP UniformRoute qUniform)
    (privateBound : client.IsQueryBoundP (PrivateRoute real) qPrivate)
    (hashBound : client.IsQueryBoundP (HashRoute real) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    (decisionClient real decode c keys client).IsQueryBoundP SourceUniform (qUniform + 64 * qPrivate) ∧
      (decisionClient real decode c keys client).IsQueryBoundP SourceHash qHash ∧
      (decisionClient real decode c keys client).IsQueryBoundP SourceSeal qSeal ∧
      (decisionClient real decode c keys client).IsQueryBoundP IsRawQuery qRaw := by
  simp only [decisionClient, isQueryBoundP_map_iff]
  exact ⟨wrapped_uniform_bound real decode c keys client qUniform qPrivate uniformBound privateBound _,
    wrapped_hash_bound real decode c keys client qHash hashBound _,
    wrapped_target_bound real decode c keys SourceSeal forward_seal_class client qSeal sealBound _,
    wrapped_target_bound real decode c keys IsRawQuery forward_raw_class client qRaw rawBound _⟩

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

theorem selected_integrity_bound {count : Nat} (selectedDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (FamilySpec count) Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (HashRoute real) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame true selectedDecode real decode c keys client).boolDistAdvantage
      (Prod.fst <$> sourceGame false selectedDecode real decode c keys client)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient real decode c keys client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient real decode c keys client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  rw [source_view_eq, source_view_eq, AdaptiveCtxSharedModes.real_view_eq, AdaptiveCtxSharedModes.replay_view_eq]
  apply AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound selectedDecode c fallback
    (decisionClient real decode c keys client) qHash qSeal qRaw
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_hash_bound real decode c keys client qHash hashBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound real decode c keys _ forward_seal_class client qSeal sealBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound real decode c keys _ forward_raw_class client qRaw rawBound (initialReduction count))
  · exact small

open AdaptiveCtxPlaintextQueryBounds
open AdaptiveCtxSharedFamilyBounds (SelectedPlaintextCost SelectedPlaintextBound no_target_seal_plaintext)

set_option backward.isDefEq.respectTransparency false in
/-- Only a selected sealing request submits its original plaintext to the target challenger. -/
theorem plaintext_step {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (query : (FamilySpec count).Domain) (state : ReductionState count) :
    SourcePlaintextBound ((reductionImpl real decode c keys query).run state) (SelectedPlaintextCost query) := by
  cases query with
  | inl selected =>
      simp only [AdaptiveCtxSharedModeFamily.reductionImpl, StateT.run, bind_pure_comp, SourcePlaintextBound,
        isQueryBound_map_iff, isQueryBound_query_iff, SelectedPlaintextCost]
      exact Nat.le_refl _
  | inr other =>
      apply no_target_seal_plaintext
      exact target_step_bound real decode c keys SourceSeal AdaptiveCtxSharedTarget.forward_seal_class (.inr other) state

/-- The full adaptive family wrapper preserves the weighted selected plaintext-byte cap. -/
theorem wrapped_plaintext_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (qBytes : Nat) (bounded : SelectedPlaintextBound client qBytes) (state : ReductionState count) :
    SourcePlaintextBound (AdaptiveCtxSharedModeFamily.wrapped real decode c keys client state) qBytes := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => SelectedPlaintextCost query)
    (fun firstBound nextBound => AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind _ _ _ _ firstBound nextBound)
    (fun query _available state _allowed => plaintext_step real decode c keys query state)
    (fun _query _available allowed => by dsimp; omega) state

/-- The Boolean decision wrapper retains the complete submitted-plaintext budget. -/
theorem decision_plaintext_bound {count : Nat} (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool)
    (qBytes : Nat) (bounded : SelectedPlaintextBound client qBytes) :
    SourcePlaintextBound (decisionClient real decode c keys client) qBytes := by
  simpa only [decisionClient, SourcePlaintextBound, isQueryBound_map_iff] using
    wrapped_plaintext_bound real decode c keys client qBytes bounded (initialReduction count)

end BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.target_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.target_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_target_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.hash_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.hash_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_hash_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.private_not_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.private_not_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.uniform_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.uniform_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.decision_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.decision_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.selected_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.selected_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.plaintext_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.plaintext_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.wrapped_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.decision_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedModeBounds.decision_plaintext_bound
