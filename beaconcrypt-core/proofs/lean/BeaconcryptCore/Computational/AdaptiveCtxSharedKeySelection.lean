import BeaconcryptCore.Computational.AdaptiveCtxSharedModePreparation
import BeaconcryptCore.Computational.RawKeyPartition

/-!
The actual original-index finite key sampler and adaptive shared-cache source are factored at any selected index. The full continuation and every per-index local state survive the sampling partition and exact routing. The selected adjacent integrity bound uses the constructed ordinary validation and attempt-indexed forgers.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection
open CtxRomAuth AdaptiveCtxSharedModes RawKeyPartition
open AdaptiveCtxReceive hiding initialState

abbrev SourceSpec (count : Nat) := RawCtxRoleFamily.FamilySpec ReceiveSpec (count + 1)
abbrev SourceState (count : Nat) := (Fin (count + 1) → Entry) × CtxRO.QueryCache

noncomputable def sourceImpl {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey) :
    QueryImpl (SourceSpec count) (StateT (SourceState count) ProbComp) :=
  fun query state => do
    let result ← (targetImpl (real query.1) (decode query.1) c (keys query.1) query.2).run (state.1 query.1, state.2)
    pure (result.1, Function.update state.1 query.1 result.2.1, result.2.2)

noncomputable def select {count : Nat} (target : Fin (count + 1)) :
    QueryImpl (SourceSpec count) (OracleComp (AdaptiveCtxSharedModeFamily.FamilySpec count)) :=
  fun query => match finSuccEquiv' target query.1 with
  | none => (AdaptiveCtxSharedModeFamily.FamilySpec count).query (.inl query.2)
  | some other => (AdaptiveCtxSharedModeFamily.FamilySpec count).query (.inr ⟨other, query.2⟩)

noncomputable def combine {count : Nat} (target : Fin (count + 1))
    (state : AdaptiveCtxSharedModeFamily.SourceState count) : SourceState count :=
  (join target state.selected state.others, state.cache)

set_option backward.isDefEq.respectTransparency false in
theorem selected_step {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (SourceSpec count).Domain) (state : AdaptiveCtxSharedModeFamily.SourceState count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (AdaptiveCtxSharedModeFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
        (select target query)).run state =
      (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys) query).run (combine target state) := by
  obtain ⟨index, query⟩ := query
  obtain ⟨position, rfl⟩ := (finSuccEquiv' target).symm.surjective index
  cases position with
  | none =>
      simp only [finSuccEquiv'_symm_none, select, finSuccEquiv'_at,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        sourceImpl, AdaptiveCtxSharedModeFamily.sourceImpl, StateT.run, combine,
        join_target, bind_pure_comp, Functor.map_map]
      rw [show targetImpl targetReal targetDecode c targetKey query (state.selected, state.cache) =
        (targetImpl targetReal targetDecode c targetKey query).run (state.selected, state.cache) from rfl, target_run]
      simp only [Functor.map_map]
      congr 1
      funext result
      rw [join_selected_update target state.selected result.1.2 state.others]
  | some other =>
      simp only [finSuccEquiv'_symm_some, select, finSuccEquiv'_succAbove,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        sourceImpl, AdaptiveCtxSharedModeFamily.sourceImpl, StateT.run, combine,
        join_other, bind_pure_comp, Functor.map_map]
      rw [show targetImpl (real other) (decode other) c (keys other) query (state.others other, state.cache) =
        (targetImpl (real other) (decode other) c (keys other) query).run (state.others other, state.cache) from rfl, target_run]
      simp only [Functor.map_map, join_other_update]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- The handler equality extends to every adaptive continuation and final family state. -/
theorem selected_schedule {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (state : AdaptiveCtxSharedModeFamily.SourceState count) :
    (fun result => (result.1, combine target result.2)) <$>
      (simulateQ (AdaptiveCtxSharedModeFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
        (simulateQ (select target) client)).run state =
      (simulateQ (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys)) client).run (combine target state) := by
  simpa only [QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
    map_run_simulateQ_eq_of_query_map_eq
      ((AdaptiveCtxSharedModeFamily.sourceImpl targetReal targetDecode real decode c targetKey keys) ∘ₛ select target)
      (sourceImpl (join target targetReal real) (join target targetDecode decode) c (join target targetKey keys))
      (combine target) (selected_step target targetReal targetDecode real decode c targetKey keys) client state

noncomputable def sourceGame {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) : ProbComp (Result × SourceState count) := do
  let keys ← $ᵗ (Fin (count + 1) → CtxKey)
  (simulateQ (sourceImpl real decode c keys) client).run ((fun _ => initialEntry), ∅)

noncomputable def erasePrepared {count : Nat} {Result : Type} (target : Fin (count + 1))
    (result : AdaptiveCtxSharedModePreparation.Prepared Unit count × (Result × AdaptiveCtxSharedModeFamily.SourceState count)) :
    Result × SourceState count :=
  (result.2.1, combine target result.2.2)

/-- The source empty histories exactly match the split challenger and other-key histories. -/
theorem fixed_source_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (targetKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) :
    (simulateQ (sourceImpl (join target targetReal real) (join target targetDecode decode) c
        (join target targetKey keys)) client).run ((fun _ => initialEntry), ∅) =
      (fun result => (result.1, combine target result.2)) <$>
        (simulateQ (AdaptiveCtxSharedModeFamily.sourceImpl targetReal targetDecode real decode c targetKey keys)
          (simulateQ (select target) client)).run (AdaptiveCtxSharedModeFamily.initialSource count) := by
  simpa only [combine, AdaptiveCtxSharedModeFamily.initialSource, join_constant] using
    (selected_schedule target targetReal targetDecode real decode c targetKey keys client
      (AdaptiveCtxSharedModeFamily.initialSource count)).symm

/-- The actual full-key source distribution equals the prepared selected-key execution. -/
theorem source_prepared_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) :
    EvalDistEq (sourceGame (join target targetReal real) (join target targetDecode decode) c client)
      (erasePrepared target <$> AdaptiveCtxSharedModePreparation.source
        (AdaptiveCtxSharedModePreparation.independentSetup count ()) targetReal targetDecode real decode c
          (fun _ => simulateQ (select target) client)) := by
  unfold sourceGame
  refine (partition_continuation count target _).trans ?_
  simp only [AdaptiveCtxSharedModePreparation.source, AdaptiveCtxSharedModePreparation.independentSetup,
    AdaptiveCtxSharedModeFamily.sourceGame, fixed_source_selection, map_bind, bind_assoc, pure_bind, map_pure]
  simp only [erasePrepared, bind_pure_comp]
  exact JointEagerTable.independent_comm_spmf ($ᵗ CtxKey) ($ᵗ (Fin count → CtxKey)) _


def SelectionClass {count : Nat} (target : Fin (count + 1))
    (p : (AdaptiveCtxSharedModeFamily.FamilySpec count).Domain → Prop) : (SourceSpec count).Domain → Prop :=
  fun query => match finSuccEquiv' target query.1 with
  | none => p (.inl query.2)
  | some other => p (.inr ⟨other, query.2⟩)

instance {count : Nat} (target : Fin (count + 1))
    (p : (AdaptiveCtxSharedModeFamily.FamilySpec count).Domain → Prop) [DecidablePred p] : DecidablePred (SelectionClass target p) :=
  fun query => by unfold SelectionClass; split <;> infer_instance

/-- An original query maps to exactly its selected resource class. -/
theorem selection_step_bound {count : Nat} (target : Fin (count + 1))
    (p : (AdaptiveCtxSharedModeFamily.FamilySpec count).Domain → Prop) [DecidablePred p] (query : (SourceSpec count).Domain) :
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
    (p : (AdaptiveCtxSharedModeFamily.FamilySpec count).Domain → Prop) [DecidablePred p] {Result : Type}
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

theorem source_view_selection {count : Nat} (target : Fin (count + 1))
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) :
    EvalDistEq (Prod.fst <$> sourceGame (join target targetReal real) (join target targetDecode decode) c client)
      ((fun result => result.2.1) <$> AdaptiveCtxSharedModePreparation.source
        (AdaptiveCtxSharedModePreparation.independentSetup count ()) targetReal targetDecode real decode c
          (fun _ => simulateQ (select target) client)) := by
  refine ((source_prepared_selection target targetReal targetDecode real decode c client).map Prod.fst).trans ?_
  simp only [Functor.map_map, erasePrepared]
  exact EvalDistEq.refl _

open AdaptiveCtxSharedModeBounds CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open AdaptiveCtxQueryBounds

theorem selected_integrity {count : Nat} (target : Fin (count + 1))
    (targetDecode : RawDecoder) (real : Fin count → Bool) (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (client : OracleComp (SourceSpec count) Bool) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute real)) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame (join target true real) (join target targetDecode decode) c client).boolDistance
      (Prod.fst <$> sourceGame (join target false real) (join target targetDecode decode) c client)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction targetDecode c
          (AdaptiveCtxSharedModePreparation.decisionClient (AdaptiveCtxSharedModePreparation.independentSetup count ())
            real decode c (fun _ => simulateQ (select target) client)) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder targetDecode) fallback
          (AdaptiveCtxReceive.wrapped targetDecode
            (AdaptiveCtxSharedModePreparation.decisionClient (AdaptiveCtxSharedModePreparation.independentSetup count ())
              real decode c (fun _ => simulateQ (select target) client))) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  have bound := AdaptiveCtxSharedModePreparation.prepared_integrity_bound
    (AdaptiveCtxSharedModePreparation.independentSetup count ()) targetDecode real decode c fallback
    (fun _ => simulateQ (select target) client) qHash qSeal qRaw
    (fun _ => selection_bound target (HashRoute real) client qHash hashBound)
    (fun _ => selection_bound target (TargetClass SourceSeal) client qSeal sealBound)
    (fun _ => selection_bound target (TargetClass IsRawQuery) client qRaw rawBound) small
  have trueEq := source_view_selection target true targetDecode real decode c client
  have falseEq := source_view_selection target false targetDecode real decode c client
  have trueMass :
      𝒟[Prod.fst <$> sourceGame (join target true real) (join target targetDecode decode) c client] {true} =
        𝒟[(fun result => result.2.1) <$> AdaptiveCtxSharedModePreparation.source
          (AdaptiveCtxSharedModePreparation.independentSetup count ()) true targetDecode real decode c
            (fun _ => simulateQ (select target) client)] {true} := by
    rw [EvalDistEq.evalDist_eq trueEq]
  have falseMass :
      𝒟[Prod.fst <$> sourceGame (join target false real) (join target targetDecode decode) c client] {true} =
        𝒟[(fun result => result.2.1) <$> AdaptiveCtxSharedModePreparation.source
          (AdaptiveCtxSharedModePreparation.independentSetup count ()) false targetDecode real decode c
            (fun _ => simulateQ (select target) client)] {true} := by
    rw [EvalDistEq.evalDist_eq falseEq]
  simpa only [ProbComp.boolDistance, trueMass, falseMass] using bound

end BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.fixed_source_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.fixed_source_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.source_prepared_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.source_prepared_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selection_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selection_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selection_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selection_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.source_view_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.source_view_selection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_integrity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection.selected_integrity
