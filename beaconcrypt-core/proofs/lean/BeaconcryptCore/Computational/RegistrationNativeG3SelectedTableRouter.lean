-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchGame
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService

/-! A deterministic selected-input partition moves only nonselected protected108-byte answers into their actual independent known cache. Selected requests remain the original external byte table. The two caches are literal disjoint views of the original lazy table, so adaptive routing preserves the complete result and both reached caches without an alias or independence premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter
open PqxdhServerAuthKeySchedule (Output)
open RegistrationNativeKeyCompiler (KeySpec coins)
abbrev Cache := (Pqxdh.Bytes →ₒ Output).QueryCache
variable {Value : Type}
attribute [local irreducible] uniformSample

def keep (selected : Pqxdh.Bytes → Bool) (cache : Cache) : Cache :=
  QueryCache.ofFn fun bytes => if selected bytes then cache bytes else none

def partition (selected : Pqxdh.Bytes → Bool) (cache : Cache) : Cache × Cache :=
  (keep (fun bytes => !selected bytes) cache, keep selected cache)

noncomputable def known (bytes : Pqxdh.Bytes) : StateT Cache (OracleComp KeySpec) Output := fun before =>
  match before bytes with
  | some output => pure (output, before)
  | none => (fun output => (output, before.cacheQuery bytes output)) <$> simulateQ coins ($ᵗ Output)

noncomputable def handler (selected : Pqxdh.Bytes → Bool) : QueryImpl KeySpec (StateT Cache (OracleComp KeySpec))
  | .inl coin => StateT.lift (KeySpec.query (.inl coin))
  | .inr bytes => if selected bytes then StateT.lift (KeySpec.query (.inr bytes)) else known bytes

noncomputable def source (selected : Pqxdh.Bytes → Bool) :=
  (PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase (handler selected)).flattenStateT

/-- A filtered cache retains its exact selected-byte answer and contains no entry in the complementary domain. -/
theorem keep_get (selected : Pqxdh.Bytes → Bool) (cache : Cache) (bytes : Pqxdh.Bytes) :
    keep selected cache bytes = if selected bytes then cache bytes else none := rfl

/-- Updating one actual byte cell changes only the corresponding partition coordinate. -/
theorem partition_update (selected : Pqxdh.Bytes → Bool) (cache : Cache) (bytes : Pqxdh.Bytes) (output : Output) :
    partition selected (cache.cacheQuery bytes output) =
      if selected bytes then ((partition selected cache).1, (partition selected cache).2.cacheQuery bytes output)
      else ((partition selected cache).1.cacheQuery bytes output, (partition selected cache).2) := by
  cases active : selected bytes <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals apply Prod.ext
  all_goals apply QueryCache.ext
  all_goals intro point
  all_goals by_cases same : point = bytes
  all_goals first
    | subst point
      simp only [partition, keep_get, active, Bool.not_false, Bool.not_true,
        QueryCache.cacheQuery_self, ite_false, ite_true, Bool.false_eq_true]
    | simp only [partition, keep_get, QueryCache.cacheQuery_of_ne _ _ same]

private theorem coins_source (work : ProbComp Value) (before : Cache) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl (simulateQ coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : PqxdhRegistrationJointKemSecondEntry.lazyImpl ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Cache ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem known_source (bytes : Pqxdh.Bytes) (before outside : Cache) :
    (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl ((known bytes).run before)).run outside =
      (fun result => (result, outside)) <$> ((Pqxdh.Bytes →ₒ Output).randomOracle bytes).run before := by
  cases found : before bytes with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ found]
      simp only [known, StateT.run, found, simulateQ_pure, map_pure]
      rfl
  | none =>
      rw [QueryImpl.withCaching_run_none _ found]
      have expanded : (known bytes).run before =
          (fun output : Output => (output, before.cacheQuery bytes output)) <$> simulateQ coins ($ᵗ Output) := by
        simp only [known, StateT.run, found]
      rw [expanded, simulateQ_map, StateT.run_map, coins_source]
      simp only [Functor.map_map]
      rfl

/-- Every actual selected or nonselected lazy table callback has the same reply and exact partitioned reached cache. -/
theorem query_source (selected : Pqxdh.Bytes → Bool) (query : KeySpec.Domain) (before : Cache) :
    Prod.map id (partition selected) <$> (PqxdhRegistrationJointKemSecondEntry.lazyImpl query).run before =
      (source selected query).run (partition selected before) := by
  cases query with
  | inl coin =>
      simp only [source, partition, QueryImpl.flattenStateT_mapStateTBase_apply_run, handler,
        StateT.run_lift, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        PqxdhRegistrationJointKemSecondEntry.lazyImpl, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, Functor.map_map, bind_pure_comp]
      rfl
  | inr bytes =>
      cases active : selected bytes
      all_goals simp only [source, partition, QueryImpl.flattenStateT_mapStateTBase_apply_run,
        handler, active, Bool.false_eq_true, ite_false, ite_true, StateT.run_lift,
        bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map]
      case false =>
        rw [known_source]
        simp only [PqxdhRegistrationJointKemSecondEntry.lazyImpl, QueryImpl.add_apply_inr]
        cases found : before bytes with
        | some output =>
            have kept : keep (fun bytes => !selected bytes) before bytes = some output := by
              simp only [keep_get, active, Bool.not_false, ite_true, found]
            rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ kept]
            simp only [map_pure]
            rfl
        | none =>
            have kept : keep (fun bytes => !selected bytes) before bytes = none := by
              simp only [keep_get, active, Bool.not_false, ite_true, found]
            rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ kept]
            simp only [Functor.map_map]
            congr 1
            funext output
            have updated := partition_update selected before bytes output
            simp only [active, Bool.false_eq_true, ite_false] at updated
            exact Prod.ext rfl updated
      case true =>
        simp only [PqxdhRegistrationJointKemSecondEntry.lazyImpl, QueryImpl.add_apply_inr]
        cases found : before bytes with
        | some output =>
            have kept : keep selected before bytes = some output := by simp only [keep_get, active, ite_true, found]
            rw [QueryImpl.withCaching_run_some _ found, QueryImpl.withCaching_run_some _ kept]
            simp only [map_pure]
            rfl
        | none =>
            have kept : keep selected before bytes = none := by simp only [keep_get, active, ite_true, found]
            rw [QueryImpl.withCaching_run_none _ found, QueryImpl.withCaching_run_none _ kept]
            simp only [Functor.map_map]
            congr 1
            funext output
            have updated := partition_update selected before bytes output
            simp only [active, ite_true] at updated
            exact Prod.ext rfl updated

end BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.keep_get' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.keep_get
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.partition_update' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.partition_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouter.query_source
