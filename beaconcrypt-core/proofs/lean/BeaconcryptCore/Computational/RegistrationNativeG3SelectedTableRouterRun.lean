-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter

/-! The actual selected-only router preserves whole adaptive byte-table executions and their original value-query allowance. The native lazy table therefore splits into uniform selected first-touch material/seed tables beside the literal nonselected cache. The allocator records selected inputs only, matching the selective hidden service's chronology. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun
open RegistrationNativeG3SelectedTableRouter (Cache keep partition known handler source)
open RegistrationNativeG3FirstTouchBound (IsValue)
open RegistrationNativeKeyCompiler (KeySpec coins)
variable {Value : Type}
attribute [local irreducible] uniformSample

/-- The exact two cache views persist through the complete adaptive native key-table program. -/
theorem program_source (selected : Pqxdh.Bytes → Bool) (work : OracleComp KeySpec Value) (before : Cache) :
    Prod.map id (partition selected) <$> (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run before =
      (simulateQ (source selected) work).run (partition selected before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (partition selected)
    (RegistrationNativeG3SelectedTableRouter.query_source selected) work before

private theorem empty_partition (selected : Pqxdh.Bytes → Bool) : partition selected ∅ = (∅, ∅) := by
  apply Prod.ext
  all_goals apply QueryCache.ext
  all_goals intro bytes
  all_goals simp only [partition, RegistrationNativeG3SelectedTableRouter.keep_get,
    QueryCache.empty_apply, ite_self]

/-- The literal nested selected/nonselected cache interpretation is the same original lazy byte-table execution, retaining both final private cache coordinates. -/
theorem nested_source (selected : Pqxdh.Bytes → Bool) (work : OracleComp KeySpec Value) (before : Cache) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
      ((simulateQ (handler selected) work).run (partition selected before).1)).run (partition selected before).2 =
      (fun result => ((result.1, (partition selected result.2).1), (partition selected result.2).2)) <$>
        (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run before := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result => ((result.1, result.2.1), result.2.2)) <$>
    (simulateQ (source selected) work).run (partition selected before) = _
  rw [← program_source]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Starting with the actual empty byte cache, closing the independent nonselected cache before the selected table preserves every original client observation. -/
theorem values_source (selected : Pqxdh.Bytes → Bool) (work : OracleComp KeySpec Value) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅ =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (handler selected) work).run' ∅)).run' ∅ := by
  have actual := nested_source selected work ∅
  rw [empty_partition] at actual
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

private theorem coins_free (work : ProbComp Value) : (simulateQ coins work).IsQueryBoundP IsValue 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
  intro query
  simp [coins, IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]

private theorem known_free (bytes : Pqxdh.Bytes) (before : Cache) :
    ((known bytes).run before).IsQueryBoundP IsValue 0 := by
  simp only [known, StateT.run]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact coins_free _

private theorem query_bound (selected : Pqxdh.Bytes → Bool) (query : KeySpec.Domain) (before : Cache) :
    ((handler selected query).run before).IsQueryBoundP IsValue (if IsValue query then 1 else 0) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]
  | inr bytes =>
      simp only [IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, ite_true, handler]
      split
      · simp [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
          PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]
      · exact (known_free bytes before).mono (by omega)

/-- The selected-only external table inherits the original complete material allowance; nonselected cache draws add only actual uniform coin queries. -/
theorem program_bound (selected : Pqxdh.Bytes → Bool) (work : OracleComp KeySpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsValue count) (before : Cache) :
    ((simulateQ (handler selected) work).run before).IsQueryBoundP IsValue count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using query_bound selected query current
  · intro query free current
    simpa only [ite_eq_right free] using query_bound selected query current

/-- The same original capped native byte-table program is the selected-only first-touch material44/seed64 source, beside its actual nonselected protected108 cache. -/
theorem lazy_split {n : Nat} (selected : Pqxdh.Bytes → Bool) (work : OracleComp KeySpec Value)
    (bounded : work.IsQueryBoundP IsValue n) :
    LazyOracleDiscard.LawEq ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅)
      (do
        let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
        Prod.fst <$> RegistrationNativeG3FirstTouchEager.fixedRun (RegistrationNativeG3Tables.join materials seeds)
          ((simulateQ (handler selected) work).run' ∅) PqxdhRegistrationJointKemSecondEntry.emptyAlloc) := by
  rw [values_source]
  exact RegistrationNativeG3FirstTouchGame.lazy_split _ (by
    simpa only [StateT.run'_eq, isQueryBoundP_map_iff] using program_bound selected work n bounded ∅)

end BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.nested_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.values_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.values_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.lazy_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun.lazy_split
