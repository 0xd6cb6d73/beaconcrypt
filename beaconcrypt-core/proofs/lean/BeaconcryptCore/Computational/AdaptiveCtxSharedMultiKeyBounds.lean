import BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity

/-!
Original-interface resource classes bound every selected ordinary reduction. The global U/H/S/R caps imply the displayed conservative processed-private, routed-public, selected-seal and raw caps. Original selected plaintext-byte costs pass through setup/routing and include complete random validation bodies/tags. Local cryptography, parsing, histories and copying remain real work.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxQueryBounds CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open AdaptiveCtxSharedKeySelection AdaptiveCtxSharedModeBounds AdaptiveCtxSharedMultiKeyIntegrity
open AdaptiveRawMultiKeyIntegrity (otherReal)

theorem selected_budgets {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (qUniform qPrivate qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (SelectionClass target UniformRoute) qUniform)
    (privateBound : client.IsQueryBoundP (SelectionClass target (PrivateRoute (otherReal target))) qPrivate)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw) :
    (clientReduction target decode c client).IsQueryBoundP SourceUniform (count * 32 + (qUniform + 64 * qPrivate)) ∧
      (clientReduction target decode c client).IsQueryBoundP SourceHash qHash ∧
      (clientReduction target decode c client).IsQueryBoundP SourceSeal qSeal ∧
      (clientReduction target decode c client).IsQueryBoundP IsRawQuery qRaw := by
  apply AdaptiveCtxSharedModePreparation.prepared_decision_budgets
  · exact AdaptiveCtxSharedModePreparation.independent_setup_bound count ()
  · intro _
    exact selection_bound target UniformRoute client qUniform uniformBound
  · intro _
    exact selection_bound target (PrivateRoute (otherReal target)) client qPrivate privateBound
  · intro _
    exact selection_bound target (HashRoute (otherReal target)) client qHash hashBound
  · intro _
    exact selection_bound target (TargetClass SourceSeal) client qSeal sealBound
  · intro _
    exact selection_bound target (TargetClass IsRawQuery) client qRaw rawBound

theorem reduction_bounds {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qUniform qPrivate qHash qSeal qRaw index : Nat)
    (uniformBound : client.IsQueryBoundP (SelectionClass target UniformRoute) qUniform)
    (privateBound : client.IsQueryBoundP (SelectionClass target (PrivateRoute (otherReal target))) qPrivate)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw) :
    (forgeryReduction target decode c fallback client index).main.IsQueryBoundP
      AdaptiveRawNonceAead.IsPrimitiveUniformQuery (count * 32 + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw)) ∧
    (forgeryReduction target decode c fallback client index).MakesAtMostSealQueries qSeal ∧
    (validationReduction target decode c client qHash).main.IsQueryBoundP
      AdaptiveRawNonceAead.IsPrimitiveUniformQuery (count * 32 + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw)) ∧
    (validationReduction target decode c client qHash).main.IsQueryBoundP IsModifiedNonceAeadSealQuery (qSeal + 1) := by
  have bounds := selected_budgets target decode c client qUniform qPrivate qHash qSeal qRaw
    uniformBound privateBound hashBound sealBound rawBound
  have forger := AdaptiveCtxQueryBounds.indexedReduction_bounds (decode target) fallback
    (clientReduction target decode c client) (count * 32 + (qUniform + 64 * qPrivate)) qHash qSeal qRaw index
      bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  exact ⟨forger.1, forger.2,
    AdaptiveCtxPrefixValidation.validationReduction_uniform_bound (decode target) c (clientReduction target decode c client)
      (count * 32 + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPrefixValidation.validationReduction_seal_bound (decode target) c (clientReduction target decode c client)
      qHash qSeal bounds.2.2.1⟩

def SourceClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (SourceSpec count).Domain → Prop :=
  fun query => p query.2

instance {count : Nat} (p : ReceiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (SourceClass (count := count) p) := fun query => inferInstanceAs (Decidable (p query.2))

theorem selection_uniform_exact {count : Nat} (target : Fin (count + 1)) :
    SelectionClass target UniformRoute = SourceClass SourceUniform := by
  funext query
  unfold SelectionClass
  split <;> rfl

theorem selection_target_exact {count : Nat} (target : Fin (count + 1))
    (p : ReceiveSpec.Domain → Prop) (query : (SourceSpec count).Domain) :
    SelectionClass target (TargetClass p) query ↔ query.1 = target ∧ p query.2 := by
  cases chosen : finSuccEquiv' target query.1 with
  | none =>
      have equal := (finSuccEquiv'_eq_none.mp chosen).symm
      simp [SelectionClass, TargetClass, equal]
  | some other =>
      have different : query.1 ≠ target := by
        intro equal
        simp [equal] at chosen
      simp [SelectionClass, chosen, TargetClass, different]

theorem selected_source_bound {count : Nat} (target : Fin (count + 1))
    (p : ReceiveSpec.Domain → Prop) [DecidablePred p] {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (SourceClass p) bound) :
    client.IsQueryBoundP (SelectionClass target (TargetClass p)) bound :=
  bounded.of_imp (fun query selected => (selection_target_exact target p query).mp selected |>.2)

theorem hash_route_work {count : Nat} (target : Fin (count + 1))
    (query : (SourceSpec count).Domain)
    (hit : SelectionClass target (HashRoute (otherReal target)) query) : SourceClass SourceWork query := by
  obtain ⟨index, query⟩ := query
  unfold SelectionClass at hit
  cases chosen : finSuccEquiv' target index with
  | none =>
      simp only [chosen, HashRoute] at hit
      rcases query with (coin | hash | input) | raw <;> simp_all [SourceClass, SourceHash, SourceWork, SourceUniform]
  | some other =>
      simp only [chosen, HashRoute] at hit
      cases mode : otherReal target other <;>
        simp only [AdaptiveCtxSharedReplayBounds.ModeHash, mode, Bool.false_eq_true, ite_false, ite_true] at hit
      · rcases query with (coin | hash | input) | raw <;> simp_all [SourceClass, SourceHash, SourceWork, SourceUniform]
      · exact hit

theorem private_route_work {count : Nat} (target : Fin (count + 1))
    (query : (SourceSpec count).Domain)
    (hit : SelectionClass target (PrivateRoute (otherReal target)) query) :
    SourceClass (fun query => SourceSeal query ∨ IsRawQuery query) query := by
  obtain ⟨index, query⟩ := query
  unfold SelectionClass at hit
  cases chosen : finSuccEquiv' target index with
  | none => simp [chosen, PrivateRoute] at hit
  | some other =>
      simp only [chosen, PrivateRoute] at hit
      cases mode : otherReal target other <;>
        simp only [AdaptiveCtxSharedReplayBounds.ModePrivate, mode, Bool.false_eq_true, ite_false, ite_true] at hit
      rcases query with (coin | hash | input) | raw <;>
        simp_all [SourceClass, SourceUniform, SourceHash, SourceSeal, IsRawQuery]

theorem source_union_bound {count : Nat} {Result : Type} (adversary : OracleComp (SourceSpec count) Result)
    (left right : (SourceSpec count).Domain → Prop) [DecidablePred left] [DecidablePred right]
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
      all_goals simp only [hleft, hright, not_true_eq_false, false_or, not_false_eq_true, true_or, ite_true, ite_false] at hl hr ⊢
      all_goals omega

theorem global_work_bound {count : Nat} {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (qPublic qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qPublic)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw) :
    client.IsQueryBoundP (SourceClass SourceWork) (qPublic + (qSeal + qRaw)) := by
  have bound := source_union_bound client _ _ _ _ hashBound
    (source_union_bound client _ _ _ _ sealBound rawBound)
  apply bound.of_imp
  intro query hit
  obtain ⟨index, query⟩ := query
  rcases query with (coin | hash | input) | raw <;>
    simp_all [SourceClass, SourceWork, SourceUniform, SourceHash, SourceSeal, IsRawQuery]

theorem global_routed_budgets {count : Nat} (target : Fin (count + 1))
    (client : OracleComp (SourceSpec count) Bool) (qUniform qPublic qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (SourceClass SourceUniform) qUniform)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qPublic)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw) :
    client.IsQueryBoundP (SelectionClass target UniformRoute) qUniform ∧
      client.IsQueryBoundP (SelectionClass target (PrivateRoute (otherReal target))) (qSeal + qRaw) ∧
      client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) (qPublic + (qSeal + qRaw)) ∧
      client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal ∧
      client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw := by
  refine ⟨?_, ?_, ?_, selected_source_bound target _ client qSeal sealBound,
    selected_source_bound target _ client qRaw rawBound⟩
  · simpa only [selection_uniform_exact] using uniformBound
  · exact (source_union_bound client _ _ _ _ sealBound rawBound).of_imp (private_route_work target)
  · exact (global_work_bound client qPublic qSeal qRaw hashBound sealBound rawBound).of_imp (hash_route_work target)

theorem global_family_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qPublic qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qPublic)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    (game decode c client 0).boolDistance (game decode c client (count + 1)) ≤
      ∑ target : Fin (count + 1), (loss target decode c fallback client (qPublic + (qSeal + qRaw)) qRaw).toReal := by
  apply family_bound decode c fallback client (fun _ => qPublic + (qSeal + qRaw)) (fun _ => qSeal) (fun _ => qRaw)
  · intro target
    exact (global_work_bound client qPublic qSeal qRaw hashBound sealBound rawBound).of_imp (hash_route_work target)
  · intro target
    exact selected_source_bound target _ client qSeal sealBound
  · intro target
    exact selected_source_bound target _ client qRaw rawBound
  · exact fun _ => small

def SelectedBytesCost {count : Nat} (target : Fin (count + 1)) : (SourceSpec count).Domain → Nat :=
  fun query => match finSuccEquiv' target query.1 with
  | none => AdaptiveCtxPlaintextQueryBounds.SourcePlaintextCost query.2
  | some _ => 0

def SelectedBytesBound {count : Nat} (target : Fin (count + 1))
    (client : OracleComp (SourceSpec count) Bool) (bytes : Nat) : Prop :=
  client.IsQueryBound bytes (fun query available => SelectedBytesCost target query ≤ available)
    (fun query available => available - SelectedBytesCost target query)

set_option backward.isDefEq.respectTransparency false in
theorem selected_plaintext_bound {count : Nat} (target : Fin (count + 1))
    (client : OracleComp (SourceSpec count) Bool) (bytes : Nat) (bounded : SelectedBytesBound target client bytes) :
    AdaptiveCtxSharedFamilyBounds.SelectedPlaintextBound (simulateQ (select target) client) bytes := by
  induction client using OracleComp.inductionOn generalizing bytes with
  | pure result => trivial
  | query_bind query next ih =>
      rw [SelectedBytesBound, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      cases chosen : finSuccEquiv' target query.1 <;>
        simp only [select, chosen, AdaptiveCtxSharedFamilyBounds.SelectedPlaintextBound, isQueryBound_query_bind_iff]
      all_goals refine ⟨by simpa only [SelectedBytesCost, chosen,
        AdaptiveCtxSharedFamilyBounds.SelectedPlaintextCost] using bounded.1, fun answer => ?_⟩
      all_goals apply ih
      all_goals simpa only [SelectedBytesBound, SelectedBytesCost, chosen, AdaptiveCtxSharedFamilyBounds.SelectedPlaintextCost] using bounded.2 _

theorem selected_decision_plaintext {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (bytes : Nat) (bounded : SelectedBytesBound target client bytes) :
    AdaptiveCtxPlaintextQueryBounds.SourcePlaintextBound (clientReduction target decode c client) bytes :=
  AdaptiveCtxSharedModePreparation.prepared_decision_plaintext
    (AdaptiveCtxSharedModePreparation.independentSetup count ()) (otherReal target)
    (fun other => decode (target.succAbove other)) c (fun _ => simulateQ (select target) client) bytes
    (fun _ => selected_plaintext_bound target client bytes bounded)

theorem validation_experiment_bounds {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (qUniform qPrivate qHash qSeal qRaw qBytes : Nat)
    (uniformBound : client.IsQueryBoundP (SelectionClass target UniformRoute) qUniform)
    (privateBound : client.IsQueryBoundP (SelectionClass target (PrivateRoute (otherReal target))) qPrivate)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw)
    (bytesBound : SelectedBytesBound target client qBytes) :
    (modifiedNonceAeadINDDollarRealExp c (validationReduction target decode c client qHash)).IsTotalQueryBound
      (32 + (count * 32 + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw))) ∧
    (modifiedNonceAeadINDDollarRandomExp (validationReduction target decode c client qHash)).IsTotalQueryBound
      (count * 32 + (qUniform + 64 * qPrivate) + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * (qSeal + 1)) := by
  have bounds := selected_budgets target decode c client qUniform qPrivate qHash qSeal qRaw
    uniformBound privateBound hashBound sealBound rawBound
  exact ⟨AdaptiveCtxPrefixValidation.validationReal_uniform_bound (decode target) c (clientReduction target decode c client)
    (count * 32 + (qUniform + 64 * qPrivate)) qHash qSeal qRaw bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2,
    AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound (decode target) c (clientReduction target decode c client)
      (count * 32 + (qUniform + 64 * qPrivate)) qHash qSeal qRaw qBytes bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
      (selected_decision_plaintext target decode c client qBytes bytesBound)⟩

end BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selection_uniform_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selection_uniform_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selection_target_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selection_target_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_source_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.hash_route_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.hash_route_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.private_route_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.private_route_work

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.source_union_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.source_union_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_work_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_work_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_routed_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_routed_budgets

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.global_family_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_plaintext_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_decision_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.selected_decision_plaintext

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.validation_experiment_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds.validation_experiment_bounds
