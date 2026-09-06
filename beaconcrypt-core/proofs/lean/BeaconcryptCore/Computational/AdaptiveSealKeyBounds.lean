import BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy
import BeaconcryptCore.Computational.NonceAeadRandomQueryBounds

/-!
The complete source and constructed ordinary reductions charge every generated key, explicit uniform query, other-key random ciphertext body/tag and selected sealing byte. Precise mode-aware weighted costs and conservative global caps are proved through all adaptive replies.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveSealKeyBounds
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open CtxComputationalSecurity NonceAeadRandomQueryBounds
open RawKeyPartition AdaptiveSealKeyFamily AdaptiveSealKeySelection

/-- Actual random local seals charge each submitted body byte and detached tag; real local sealing is deterministic. -/
def localUniformCost (real : Bool) : ModifiedNonceAeadAdversarySpec.Domain → Nat
  | .inl _ => 1
  | .inr input => if real then 0 else input.plaintext.length + 16

theorem local_uniform_bound (real : Bool) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ModifiedNonceAeadAdversarySpec.Domain) (state : ModifiedNonceAeadHandlerState) :
    ((localImpl real c key query).run state).IsTotalQueryBound (localUniformCost real query) := by
  cases real with
  | false => exact randomImpl_uniform_step query state
  | true =>
      cases query with
      | inl coin =>
          change ((fun answer => (answer, state)) <$> (unifSpec.query coin : ProbComp _)).IsTotalQueryBound 1
          simp only [IsTotalQueryBound, isQueryBound_map_iff, isQueryBound_query_iff]
          decide
      | inr input =>
          change ((modifiedNonceAeadSealOracle c key input).run state).IsTotalQueryBound 0
          rw [modifiedNonceAeadSealOracle_run]
          split <;> trivial

def TargetClass {count : Nat} (p : ModifiedNonceAeadAdversarySpec.Domain → Prop) : (SplitSpec count).Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance {count : Nat} (p : ModifiedNonceAeadAdversarySpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (TargetClass (count := count) p)
  | .inl query => inferInstanceAs (Decidable (p query))
  | .inr _ => isFalse id

theorem reduction_seal_step {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (query : (SplitSpec count).Domain) (state : State count) :
    ((reductionImpl real c keys query).run state).IsQueryBoundP IsModifiedNonceAeadSealQuery
      (if TargetClass IsModifiedNonceAeadSealQuery query then 1 else 0) := by
  cases query with
  | inl query =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass]
      exact (isQueryBoundP_query_iff _ query _).mpr (by intro hit; simp [hit])
  | inr other =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass, if_false] using
        liftProbComp_no_modifiedNonceAeadSealQueries
          ((localImpl (real other.1) c (keys other.1) other.2).run (state other.1))

theorem wrapped_seal_bound {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (SplitSpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (TargetClass IsModifiedNonceAeadSealQuery) bound) (state : State count) :
    (wrapped real c keys client state).IsQueryBoundP IsModifiedNonceAeadSealQuery bound :=
  bounded.simulateQ_run_StateT_of_step (reduction_seal_step real c keys) state

def SelectionClass {count : Nat} (target : Fin (count + 1))
    (p : (SplitSpec count).Domain → Prop) : (Spec (count + 1)).Domain → Prop :=
  fun query => match finSuccEquiv' target query.1 with
  | none => p (.inl query.2)
  | some other => p (.inr ⟨other, query.2⟩)

instance {count : Nat} (target : Fin (count + 1)) (p : (SplitSpec count).Domain → Prop) [DecidablePred p] :
    DecidablePred (SelectionClass target p) := fun query => by unfold SelectionClass; split <;> infer_instance

theorem selection_step_bound {count : Nat} (target : Fin (count + 1))
    (p : (SplitSpec count).Domain → Prop) [DecidablePred p] (query : (Spec (count + 1)).Domain) :
    (select target query).IsQueryBoundP p (if SelectionClass target p query then 1 else 0) := by
  cases chosen : finSuccEquiv' target query.1 with
  | none =>
      simp only [select, SelectionClass, chosen]
      exact (isQueryBoundP_query_iff p _ _).mpr (by intro hit; simp [hit])
  | some other =>
      simp only [select, SelectionClass, chosen]
      exact (isQueryBoundP_query_iff p _ _).mpr (by intro hit; simp [hit])

set_option backward.isDefEq.respectTransparency false in
theorem selection_bound {count : Nat} (target : Fin (count + 1))
    (p : (SplitSpec count).Domain → Prop) [DecidablePred p] {Result : Type}
    (client : OracleComp (Spec (count + 1)) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (SelectionClass target p) bound) :
    (simulateQ (select target) client).IsQueryBoundP p bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      cases chosen : finSuccEquiv' target query.1 <;> simp only [select, chosen, isQueryBoundP_query_bind_iff]
      all_goals refine ⟨by simpa only [SelectionClass, chosen] using bounded.1, fun answer => ?_⟩
      all_goals apply ih
      all_goals simpa only [SelectionClass, chosen] using bounded.2 _

theorem prepared_seal_bound {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp (Spec (count + 1)) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery)) bound) :
    (prepared target real c client).IsQueryBoundP IsModifiedNonceAeadSealQuery bound := by
  unfold prepared
  have complete := isQueryBoundP_bind
    (liftProbComp_no_modifiedNonceAeadSealQueries ($ᵗ (Fin count → CtxKey)))
    (fun keys _ => wrapped_seal_bound real c keys _ bound (selection_bound target _ client bound bounded) (initialState count))
  simpa only [Nat.zero_add] using complete

def WorkBound {ι Result : Type} {spec : OracleSpec ι} (cost : spec.Domain → Nat)
    (client : OracleComp spec Result) (budget : Nat) : Prop :=
  client.IsQueryBound budget (fun query available => cost query ≤ available)
    (fun query available => available - cost query)

/-- A byte-weighted source budget transfers through every complete stateful continuation. -/
theorem work_simulate {ι κ Result LocalState : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    (cost : source.Domain → Nat) (impl : QueryImpl source (StateT LocalState (OracleComp target)))
    (predicate : target.Domain → Prop) [DecidablePred predicate] (client : OracleComp source Result)
    (budget : Nat) (bounded : WorkBound cost client budget)
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (cost query)) (state : LocalState) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate budget := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => cost query)
    (fun first rest => isQueryBoundP_bind first (fun value _ => rest value))
    (fun query _ state _ => step query state)
    (fun _query _available allowed => by dsimp; omega) state

def SplitUniformCost {count : Nat} (real : Fin count → Bool) : (SplitSpec count).Domain → Nat
  | .inl (.inl _) => 1
  | .inl (.inr _) => 0
  | .inr other => localUniformCost (real other.1) other.2

theorem reduction_uniform_step {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (query : (SplitSpec count).Domain) (state : State count) :
    ((reductionImpl real c keys query).run state).IsQueryBoundP IsModifiedNonceAeadUniformQuery (SplitUniformCost real query) := by
  cases query with
  | inl query =>
      cases query <;>
        simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
          SplitUniformCost, isQueryBoundP_query_iff, IsModifiedNonceAeadUniformQuery]
      all_goals decide
  | inr other =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, SplitUniformCost] using
        liftProbComp_uniform_query_bound (local_uniform_bound (real other.1) c (keys other.1) other.2 (state other.1))

theorem wrapped_uniform_bound {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (SplitSpec count) Result)
    (budget : Nat) (bounded : WorkBound (SplitUniformCost real) client budget) (state : State count) :
    (wrapped real c keys client state).IsQueryBoundP IsModifiedNonceAeadUniformQuery budget :=
  work_simulate _ _ _ client budget bounded (reduction_uniform_step real c keys) state

def SelectedCost {count : Nat} (target : Fin (count + 1))
    (cost : (SplitSpec count).Domain → Nat) : (Spec (count + 1)).Domain → Nat :=
  fun query => match finSuccEquiv' target query.1 with
  | none => cost (.inl query.2)
  | some other => cost (.inr ⟨other, query.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem selected_work_bound {count : Nat} (target : Fin (count + 1))
    (cost : (SplitSpec count).Domain → Nat) {Result : Type} (client : OracleComp (Spec (count + 1)) Result)
    (budget : Nat) (bounded : WorkBound (SelectedCost target cost) client budget) :
    WorkBound cost (simulateQ (select target) client) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure result => trivial
  | query_bind query next ih =>
      rw [WorkBound, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      cases chosen : finSuccEquiv' target query.1 <;>
        simp only [select, chosen, WorkBound, isQueryBound_query_bind_iff]
      all_goals refine ⟨by simpa only [SelectedCost, chosen] using bounded.1, fun answer => ?_⟩
      all_goals apply ih
      all_goals simpa only [WorkBound, SelectedCost, chosen] using bounded.2 _

/-- Other-key generation and every actual local random body/tag byte remain in the reduction's uniform budget. -/
theorem prepared_uniform_bound {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp (Spec (count + 1)) Result) (budget : Nat)
    (bounded : WorkBound (SelectedCost target (SplitUniformCost real)) client budget) :
    (prepared target real c client).IsQueryBoundP IsModifiedNonceAeadUniformQuery (count * 32 + budget) := by
  unfold prepared
  apply isQueryBoundP_bind (liftProbComp_uniform_query_bound (AdaptiveRawKeyPreparation.key_family_bound count))
  intro keys _
  exact wrapped_uniform_bound real c keys _ budget (selected_work_bound target _ client budget bounded) (initialState count)

def SplitPlaintextCost {count : Nat} : (SplitSpec count).Domain → Nat
  | .inl query => plaintextCost query
  | .inr _ => 0

theorem reduction_plaintext_step {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (query : (SplitSpec count).Domain) (state : State count) :
    PlaintextBound ((reductionImpl real c keys query).run state) (SplitPlaintextCost query) := by
  cases query with
  | inl query =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, PlaintextBound, isQueryBound_map_iff,
        SplitPlaintextCost, isQueryBound_query_iff]
      exact Nat.le_refl _
  | inr other =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, PlaintextBound, isQueryBound_map_iff,
        SplitPlaintextCost] using lifted_probability_plaintext_zero
          ((localImpl (real other.1) c (keys other.1) other.2).run (state other.1))

theorem wrapped_plaintext_bound {count : Nat} (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (SplitSpec count) Result)
    (budget : Nat) (bounded : WorkBound SplitPlaintextCost client budget) (state : State count) :
    PlaintextBound (wrapped real c keys client state) budget :=
  plaintext_simulate _ _ client budget bounded (reduction_plaintext_step real c keys) state

theorem prepared_plaintext_bound {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) {Result : Type} (client : OracleComp (Spec (count + 1)) Result) (budget : Nat)
    (bounded : WorkBound (SelectedCost target SplitPlaintextCost) client budget) :
    PlaintextBound (prepared target real c client) budget := by
  unfold prepared
  have complete := plaintext_bind _ _ 0 budget (lifted_probability_plaintext_zero ($ᵗ (Fin count → CtxKey)))
    (fun keys => wrapped_plaintext_bound real c keys _ budget (selected_work_bound target _ client budget bounded) (initialState count))
  simpa only [Nat.zero_add] using complete

/-- The concrete ordinary reduction submits only target seals and bytes, while its uniform work includes all other-key generation and local randomized encryption. -/
theorem reduction_bounds {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) (qSeal qWork qBytes : Nat)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery)) qSeal)
    (workBound : WorkBound (SelectedCost target (SplitUniformCost real)) client qWork)
    (bytesBound : WorkBound (SelectedCost target SplitPlaintextCost) client qBytes) :
    (AdaptiveSealMultiKeyPrivacy.reduction target real c client).main.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal ∧
    (AdaptiveSealMultiKeyPrivacy.reduction target real c client).main.IsQueryBoundP IsModifiedNonceAeadUniformQuery (count * 32 + qWork) ∧
    PlaintextBound (AdaptiveSealMultiKeyPrivacy.reduction target real c client).main qBytes := by
  simp only [AdaptiveSealMultiKeyPrivacy.reduction, PlaintextBound, isQueryBound_map_iff, isQueryBoundP_map_iff]
  exact ⟨prepared_seal_bound target real c client qSeal sealBound,
    prepared_uniform_bound target real c client qWork workBound,
    prepared_plaintext_bound target real c client qBytes bytesBound⟩

theorem experiment_bounds {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) (qSeal qWork qBytes : Nat)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsModifiedNonceAeadSealQuery)) qSeal)
    (workBound : WorkBound (SelectedCost target (SplitUniformCost real)) client qWork)
    (bytesBound : WorkBound (SelectedCost target SplitPlaintextCost) client qBytes) :
    (modifiedNonceAeadINDDollarRealExp c (AdaptiveSealMultiKeyPrivacy.reduction target real c client)).IsTotalQueryBound
      (32 + (count * 32 + qWork)) ∧
    (modifiedNonceAeadINDDollarRandomExp (AdaptiveSealMultiKeyPrivacy.reduction target real c client)).IsTotalQueryBound
      (count * 32 + qWork + qBytes + 16 * qSeal) := by
  have bounds := reduction_bounds target real c client qSeal qWork qBytes sealBound workBound bytesBound
  constructor
  · unfold modifiedNonceAeadINDDollarRealExp
    apply isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 32)
    intro key
    simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound c key
        (AdaptiveSealMultiKeyPrivacy.reduction target real c client).main _ bounds.2.1
  · exact randomExperiment_uniform_bound _ qBytes qSeal (count * 32 + qWork) bounds.2.2 bounds.1 bounds.2.1

/-- Enlarging a weighted budget retains all possible query replies and stopping choices. -/
theorem work_mono {ι Result : Type} {spec : OracleSpec ι} (cost : spec.Domain → Nat)
    (client : OracleComp spec Result) {budget larger : Nat} (bounded : WorkBound cost client budget)
    (increase : budget ≤ larger) : WorkBound cost client larger := by
  induction client using OracleComp.inductionOn generalizing budget larger with
  | pure result => trivial
  | query_bind query next ih =>
      rw [WorkBound, isQueryBound_query_bind_iff] at bounded ⊢
      exact ⟨bounded.1.trans increase, fun answer => ih answer (bounded.2 answer) (Nat.sub_le_sub_right increase _)⟩

/-- Any per-query random-work cost below the complete random seal cost follows from global coin, plaintext and seal caps. -/
theorem work_of_global_caps {Result : Type} {K : Nat}
    (cost : (Spec K).Domain → Nat) (costBound : ∀ query, cost query ≤ localUniformCost false query.2)
    (client : OracleComp (Spec K) Result) (qUniform qBytes qSeal : Nat)
    (coinBound : client.IsQueryBoundP (fun query => IsModifiedNonceAeadUniformQuery query.2) qUniform)
    (bytesBound : WorkBound (fun query => plaintextCost query.2) client qBytes)
    (sealBound : client.IsQueryBoundP (fun query => IsModifiedNonceAeadSealQuery query.2) qSeal) :
    WorkBound cost client (qUniform + qBytes + 16 * qSeal) := by
  induction client using OracleComp.inductionOn generalizing qUniform qBytes qSeal with
  | pure result => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at coinBound sealBound
      rw [WorkBound, isQueryBound_query_bind_iff] at bytesBound ⊢
      have nextBound := fun answer => ih answer _ _ _ (coinBound.2 answer) (bytesBound.2 answer) (sealBound.2 answer)
      have charged := costBound query
      obtain ⟨index, query⟩ := query
      cases query with
      | inl coin =>
          simp only [localUniformCost] at charged
          simp only [IsModifiedNonceAeadUniformQuery, IsModifiedNonceAeadSealQuery, plaintextCost,
            if_true, if_false, Nat.sub_zero, not_true_eq_false, false_or, not_false_eq_true, true_or] at coinBound sealBound bytesBound nextBound
          refine ⟨by omega, fun answer => work_mono cost (next answer) (nextBound answer) ?_⟩
          omega
      | inr input =>
          simp only [localUniformCost, Bool.false_eq_true, if_false] at charged
          simp only [IsModifiedNonceAeadUniformQuery, IsModifiedNonceAeadSealQuery, plaintextCost,
            if_true, if_false, not_true_eq_false, false_or, not_false_eq_true, true_or] at coinBound sealBound bytesBound nextBound
          refine ⟨by omega, fun answer => work_mono cost (next answer) (nextBound answer) ?_⟩
          omega

theorem selected_uniform_cost_bound {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (query : (Spec (count + 1)).Domain) :
    SelectedCost target (SplitUniformCost real) query ≤ localUniformCost false query.2 := by
  unfold SelectedCost
  split
  · cases query.2 <;> simp [SplitUniformCost, localUniformCost]
  · cases query.2 <;> simp [SplitUniformCost, localUniformCost]
    split <;> omega

/-- Global source caps provide a conservative concrete bound; the precise mode-aware cost may be strictly smaller. -/
theorem prepared_global_uniform_bound {Result : Type} {K : Nat} (target : Fin (K + 1)) (real : Fin K → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (K + 1)) Result) (qUniform qBytes qSeal : Nat)
    (coinBound : client.IsQueryBoundP (fun query => IsModifiedNonceAeadUniformQuery query.2) qUniform)
    (bytesBound : WorkBound (fun query => plaintextCost query.2) client qBytes)
    (sealBound : client.IsQueryBoundP (fun query => IsModifiedNonceAeadSealQuery query.2) qSeal) :
    (prepared target real c client).IsQueryBoundP IsModifiedNonceAeadUniformQuery
      (K * 32 + (qUniform + qBytes + 16 * qSeal)) :=
  prepared_uniform_bound target real c client _
    (work_of_global_caps _ (selected_uniform_cost_bound target real) client qUniform qBytes qSeal coinBound bytesBound sealBound)

def FamilyCost {count : Nat} (real : Fin count → Bool) : (Spec count).Domain → Nat :=
  fun query => localUniformCost (real query.1) query.2

theorem family_uniform_step {count : Nat} (real : Fin count → Bool) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (query : (Spec count).Domain) (state : State count) :
    ((familyImpl c keys real query).run state).IsTotalQueryBound (FamilyCost real query) := by
  simpa only [familyImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, FamilyCost] using
    local_uniform_bound (real query.1) c (keys query.1) query.2 (state query.1)

theorem family_run_uniform_bound {Result : Type} {K : Nat} (real : Fin K → Bool) (c : Pqxdh.Crypto)
    (keys : Fin K → CtxKey) (client : OracleComp (Spec K) Result) (budget : Nat)
    (bounded : WorkBound (FamilyCost real) client budget) (state : State K) :
    ((simulateQ (familyImpl c keys real) client).run state).IsTotalQueryBound budget := by
  rw [← isQueryBoundP_true_iff]
  exact work_simulate _ _ (fun _ => True) client budget bounded
    (fun query state => (isQueryBoundP_true_iff _ _).mpr (family_uniform_step real c keys query state)) state

/-- The entire actual indexed source charges every generated key, even if that key's mode never uses it. -/
theorem source_uniform_bound {Result : Type} {K : Nat} (real : Fin K → Bool) (c : Pqxdh.Crypto)
    (client : OracleComp (Spec K) Result) (budget : Nat) (bounded : WorkBound (FamilyCost real) client budget) :
    (sourceGame real c client).IsTotalQueryBound (K * 32 + budget) := by
  unfold sourceGame
  apply isTotalQueryBound_bind (AdaptiveRawKeyPreparation.key_family_bound K)
  intro keys
  exact family_run_uniform_bound real c keys client budget bounded (initialState K)

end BeaconcryptCore.Computational.AdaptiveSealKeyBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.local_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.local_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_seal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_seal_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_seal_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selection_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selection_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selection_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_seal_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_simulate

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selected_work_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selected_work_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_plaintext_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_plaintext_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.wrapped_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.experiment_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.experiment_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_mono

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_of_global_caps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.work_of_global_caps

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selected_uniform_cost_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.selected_uniform_cost_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_global_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.prepared_global_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.family_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.family_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.family_run_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.family_run_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealKeyBounds.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealKeyBounds.source_uniform_bound
