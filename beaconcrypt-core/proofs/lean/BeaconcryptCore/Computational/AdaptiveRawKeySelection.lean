import BeaconcryptCore.Computational.RawKeyPartition
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
Ten statements route arbitrary original key indices to the selected ordinary challenger or the reduction's other-key handlers. The whole adaptive execution preserves the complete family of nonce histories, successful seals, raw-attempt counts and discrepancy flags. The actual full-key sampler agrees with the prepared selected-key experiment through the entire continuation. Query classes and resource caps follow the original indices without a random target guess.

The family contains independently sampled primitive keys, not a proved idealization of the production evolving keys. Its decoders and adversary receive no sampled secret keys. Private histories are retained for proof and are not additional observations. CTX shared-cache behavior, native parser/material selection, compromise and evolving-key correlation remain separate composition obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveRawKeySelection
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveRawKeyFamily RawKeyPartition

abbrev SourceSpec (count : Nat) := RawCtxRoleFamily.FamilySpec AdaptiveSpec (count + 1)
abbrev SourceState (count : Nat) := Fin (count + 1) → LocalState

noncomputable def sourceImpl {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey) :
    QueryImpl (SourceSpec count) (StateT (SourceState count) ProbComp) :=
  fun query state => do
    let result ← (adaptiveImpl (real query.1) (decode query.1) c (keys query.1) query.2).run (state query.1)
    pure (result.1, Function.update state query.1 result.2)

noncomputable def select {count : Nat} (target : Fin (count + 1)) :
    QueryImpl (SourceSpec count) (OracleComp (FamilySpec count)) :=
  fun query => match finSuccEquiv' target query.1 with
  | none => (FamilySpec count).query (.inl query.2)
  | some other => (FamilySpec count).query (.inr ⟨other, query.2⟩)

noncomputable def combine {count : Nat} (target : Fin (count + 1)) (state : State count) : SourceState count :=
  join target state.2 state.1

set_option backward.isDefEq.respectTransparency false in
/-- The selected-key handler retains the original reply and all complete per-key states. -/
theorem selected_step {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (SourceSpec count).Domain) (state : State count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (AdaptiveRawKeyFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
        (select target query)).run state =
      (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys) query).run (combine target state) := by
  obtain ⟨index, query⟩ := query
  obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
  cases position with
  | none =>
      simp only [finSuccEquiv'_symm_none, select, finSuccEquiv'_at,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        sourceImpl, AdaptiveRawKeyFamily.sourceImpl, StateT.run, combine,
        join_target, bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      rw [join_selected_update target state.2 result.2 state.1]
  | some other =>
      simp only [finSuccEquiv'_symm_some, select, finSuccEquiv'_succAbove,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        sourceImpl, AdaptiveRawKeyFamily.sourceImpl, StateT.run, combine,
        join_other, bind_pure_comp, Functor.map_map]
      simp only [join_other_update]

set_option backward.isDefEq.respectTransparency false in
/-- The handler equality extends to every adaptive continuation and final family state. -/
theorem selected_schedule {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (state : State count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (AdaptiveRawKeyFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
        (simulateQ (select target) client)).run state =
      (simulateQ (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys)) client).run (combine target state) := by
  simpa only [QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
    map_run_simulateQ_eq_of_query_map_eq
      ((AdaptiveRawKeyFamily.sourceImpl targetReal targetDecode real decode c targetKey keys) ∘ₛ select target)
      (sourceImpl (join target targetReal real) (join target targetDecode decode) c (join target targetKey keys))
      (combine target) (selected_step target targetReal targetDecode real decode c targetKey keys) client state

noncomputable def sourceGame {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) : ProbComp (Result × SourceState count) := do
  let keys ← $ᵗ (Fin (count + 1) → CtxKey)
  (simulateQ (sourceImpl real decode c keys) client).run (fun _ => (initialState, false))

noncomputable def erasePrepared {count : Nat} {Result : Type} (target : Fin (count + 1))
    (result : AdaptiveRawKeyPreparation.Prepared Unit count × (Result × State count)) :
    Result × SourceState count :=
  (result.2.1, combine target result.2.2)

/-- The source empty histories exactly match the split challenger and other-key histories. -/
theorem fixed_source_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) :
    (simulateQ (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys)) client).run (fun _ => (initialState, false)) =
      (fun result => (result.1, combine target result.2)) <$>
        (simulateQ (AdaptiveRawKeyFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
          (simulateQ (select target) client)).run ((fun _ => (initialState, false)), initialState, false) := by
  simpa only [combine, join_constant] using
    (selected_schedule target targetReal targetDecode real decode c targetKey keys client
      ((fun _ => (initialState, false)), initialState, false)).symm

/-- The actual full-key source distribution equals the prepared selected-key execution. -/
theorem source_prepared_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) :
    𝒟[sourceGame (join target targetReal real) (join target targetDecode decode) c client] =
      𝒟[erasePrepared target <$> AdaptiveRawKeyPreparation.source
        (AdaptiveRawKeyPreparation.independentSetup count ()) targetReal targetDecode real decode c
          (fun _ => simulateQ (select target) client)] := by
  unfold sourceGame
  rw [partition_continuation count target]
  simp only [AdaptiveRawKeyPreparation.source, AdaptiveRawKeyPreparation.independentSetup,
    uniformSource, fixed_source_selection, map_bind, bind_assoc, pure_bind, map_pure]
  simp only [erasePrepared, bind_pure_comp]
  exact JointEagerTable.independent_comm ($ᵗ CtxKey) ($ᵗ (Fin count → CtxKey)) _

def SelectionClass {count : Nat} (target : Fin (count + 1))
    (p : (FamilySpec count).Domain → Prop) : (SourceSpec count).Domain → Prop :=
  fun query => match finSuccEquiv' target query.1 with
  | none => p (.inl query.2)
  | some other => p (.inr ⟨other, query.2⟩)

instance {count : Nat} (target : Fin (count + 1))
    (p : (FamilySpec count).Domain → Prop) [DecidablePred p] : DecidablePred (SelectionClass target p) :=
  fun query => by unfold SelectionClass; split <;> infer_instance

/-- An original query maps to exactly its selected resource class. -/
theorem selection_step_bound {count : Nat} (target : Fin (count + 1))
    (p : (FamilySpec count).Domain → Prop) [DecidablePred p] (query : (SourceSpec count).Domain) :
    (select target query).IsQueryBoundP p (if SelectionClass target p query then 1 else 0) := by
  cases chosen : finSuccEquiv' target query.1 with
  | none =>
      simp only [select, SelectionClass, chosen]
      exact (isQueryBoundP_query_iff p _ _).mpr (by intro hit; simp [hit])
  | some other =>
      simp only [select, SelectionClass, chosen]
      exact (isQueryBoundP_query_iff p _ _).mpr (by intro hit; simp [hit])

set_option backward.isDefEq.respectTransparency false in
/-- Every adaptive query-class cap survives the exact index routing. -/
theorem selection_bound {count : Nat} (target : Fin (count + 1))
    (p : (FamilySpec count).Domain → Prop) [DecidablePred p] {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (bound : Nat)
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

/-- The selected source-key hop is bounded by the explicit ordinary attempt-indexed forgers. -/
theorem selected_integrity {count : Nat} (target : Fin (count + 1))
    (targetDecode : RawDecoder) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (rawCount : Nat)
    (bounded : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) rawCount) :
    ENNReal.ofReal (tvDist (sourceGame (join target true real) (join target targetDecode decode) c client)
      (sourceGame (join target false real) (join target targetDecode decode) c client)) ≤
      ∑ index ∈ Finset.range rawCount, modifiedNonceAeadINTCTXTAdvantage c
        (indexedReduction targetDecode fallback
          (AdaptiveRawKeyPreparation.wrapped (AdaptiveRawKeyPreparation.independentSetup count ())
            real decode c (fun _ => simulateQ (select target) client)) index) := by
  have integrity := AdaptiveRawKeyPreparation.prepared_integrity_bound
    (AdaptiveRawKeyPreparation.independentSetup count ()) targetDecode real decode c
      (fun _ => simulateQ (select target) client) fallback rawCount
      (fun _ => selection_bound target (TargetClass IsRawQuery) client rawCount bounded)
  have mapped := (ENNReal.ofReal_le_ofReal (tvDist_map_le (erasePrepared target)
    (AdaptiveRawKeyPreparation.source (AdaptiveRawKeyPreparation.independentSetup count ()) true targetDecode real decode c
      (fun _ => simulateQ (select target) client))
    (AdaptiveRawKeyPreparation.source (AdaptiveRawKeyPreparation.independentSetup count ()) false targetDecode real decode c
      (fun _ => simulateQ (select target) client)))).trans integrity
  simpa only [tvDist, ← source_prepared_selection] using mapped

/-- Selected resource membership is exactly original-index equality and the local predicate. -/
theorem selection_target_class {count : Nat} (target : Fin (count + 1))
    (p : AdaptiveSpec.Domain → Prop) (query : (SourceSpec count).Domain) :
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

def SourceUniform {count : Nat} : (SourceSpec count).Domain → Prop :=
  fun query => IsUniform query.2

instance {count : Nat} : DecidablePred (SourceUniform (count := count)) :=
  fun query => inferInstanceAs (Decidable (IsUniform query.2))

/-- Uniform work at every original key is charged to the same caller budget. -/
theorem selection_uniform_class {count : Nat} (target : Fin (count + 1)) :
    SelectionClass target UniformClass = SourceUniform := by
  funext query
  unfold SelectionClass
  split <;> rfl

/-- The constructed forgers charge every other sampled key and inherit target seal bounds. -/
theorem selected_reduction_bounds {count : Nat} (target : Fin (count + 1))
    (targetDecode : RawDecoder) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (uniformCount sealCount index : Nat)
    (uniformBound : client.IsQueryBoundP SourceUniform uniformCount)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass (primitiveClass IsModifiedNonceAeadSealQuery))) sealCount) :
    (indexedReduction targetDecode fallback
      (AdaptiveRawKeyPreparation.wrapped (AdaptiveRawKeyPreparation.independentSetup count ())
        real decode c (fun _ => simulateQ (select target) client)) index).main.IsQueryBoundP
      IsPrimitiveUniformQuery (count * 32 + uniformCount) ∧
      (indexedReduction targetDecode fallback
        (AdaptiveRawKeyPreparation.wrapped (AdaptiveRawKeyPreparation.independentSetup count ())
          real decode c (fun _ => simulateQ (select target) client)) index).MakesAtMostSealQueries sealCount := by
  apply AdaptiveRawKeyPreparation.prepared_reduction_bounds
  · exact AdaptiveRawKeyPreparation.independent_setup_bound count ()
  · intro context
    apply selection_bound
    simpa only [selection_uniform_class] using uniformBound
  · intro context
    exact selection_bound target _ client sealCount sealBound

end BeaconcryptCore.Computational.AdaptiveRawKeySelection

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.fixed_source_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.fixed_source_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.source_prepared_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.source_prepared_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_integrity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_integrity

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_target_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_target_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_uniform_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selection_uniform_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeySelection.selected_reduction_bounds
