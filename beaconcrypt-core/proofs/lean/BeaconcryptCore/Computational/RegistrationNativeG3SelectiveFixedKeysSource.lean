-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedCallbacks

/-! The actual selective fixed108-byte service is the selected-only first-touch table router. Its slot map and cursor are the original reserve fields, and its nonselected answers retain the literal existing byte cache. Preparation flags, material cache and demand counters are untouched by this key-oracle callback and are deliberately outside this projection. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource
open PqxdhServerAuthKeySchedule (Output)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3SelectedTableRouter (Cache handler)
open RegistrationNativeG3FirstTouch (Alloc Table)
open RegistrationNativeKeyCompiler (KeySpec coins)
variable {n : Nat} {Value : Type}
attribute [local irreducible] uniformSample

def project (before : RegistrationNativeSelectiveHiddenService.State n) : Cache × Alloc n :=
  (before.2, (before.1.slots, before.1.next))

noncomputable def target (outputs : Table n) (selected : Pqxdh.Bytes → Bool) :=
  ((RegistrationNativeG3SelectedZeroTable.zero outputs).mapStateTBase (handler selected)).flattenStateT

private theorem old_coins (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3MetricCoins.localCoins (n := n))
      (simulateQ RegistrationNativeHiddenService.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3MetricCoins.localCoins (n := n) ∘ₛ RegistrationNativeHiddenService.coins =
      QueryImpl.ofLift unifSpec ProbComp := by
    funext query
    rfl
  rw [same, simulateQ_ofLift_eq_self]

private theorem table_coins (outputs : Table n) (work : ProbComp Value) (before : Alloc n) :
    (simulateQ (RegistrationNativeG3SelectedZeroTable.zero outputs) (simulateQ coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3SelectedZeroTable.zero outputs ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Alloc n) ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem table_known (outputs : Table n) (bytes : Pqxdh.Bytes) (before : Cache) (alloc : Alloc n) :
    (simulateQ (RegistrationNativeG3SelectedZeroTable.zero outputs)
      ((RegistrationNativeG3SelectedTableRouter.known bytes).run before)).run alloc =
      (fun result => (result, alloc)) <$> ((Pqxdh.Bytes →ₒ Output).randomOracle bytes).run before := by
  cases found : before bytes with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ found]
      simp only [RegistrationNativeG3SelectedTableRouter.known, StateT.run, found, simulateQ_pure, map_pure]
      rfl
  | none =>
      rw [QueryImpl.withCaching_run_none _ found]
      have expanded : (RegistrationNativeG3SelectedTableRouter.known bytes).run before =
          (fun output : Output => (output, before.cacheQuery bytes output)) <$> simulateQ coins ($ᵗ Output) := by
        simp only [RegistrationNativeG3SelectedTableRouter.known, StateT.run, found]
      rw [expanded, simulateQ_map, StateT.run_map, table_coins]
      simp only [Functor.map_map]
      rfl

/-- The original selective fixed-key callback preserves exactly its nonselected byte cache and selected input-to-slot assignment under the concrete router state map. -/
theorem query_source (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : KeySpec.Domain) (before : RegistrationNativeSelectiveHiddenService.State n) :
    Prod.map id project <$> simulateQ RegistrationNativeG3MetricCoins.localCoins
      ((RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate query).run before) =
      (target (RegistrationNativeG3Tables.join materials seeds) (RegistrationNativeSelectiveHiddenService.selected inside candidate) query).run (project before) := by
  cases query with
  | inl coin =>
      simp only [target, project, QueryImpl.flattenStateT_mapStateTBase_apply_run,
        RegistrationNativeG3SelectiveService.fixedKeys, handler, StateT.run_lift,
        simulateQ_map, StateT.run_map, simulateQ_spec_query, bind_pure_comp,
        RegistrationNativeHiddenService.coins, RegistrationNativeG3MetricCoins.localCoins,
        RegistrationNativeG3SelectedZeroTable.zero, Functor.map_map]
      rfl
  | inr bytes =>
      cases chosen : RegistrationNativeSelectiveHiddenService.selected inside candidate bytes
      all_goals change (Prod.map id project <$> simulateQ RegistrationNativeG3MetricCoins.localCoins
        ((RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate (.inr bytes)) before) =
        (fun result => (result.1.1, (result.1.2, result.2))) <$>
          (simulateQ (RegistrationNativeG3SelectedZeroTable.zero (RegistrationNativeG3Tables.join materials seeds))
            ((handler (RegistrationNativeSelectiveHiddenService.selected inside candidate) (.inr bytes)).run before.2)).run (before.1.slots, before.1.next))
      all_goals simp only [RegistrationNativeG3SelectiveService.fixedKeys, handler, chosen,
        Bool.false_eq_true, ite_false, ite_true, StateT.run_lift, bind_pure_comp,
        simulateQ_map, StateT.run_map, simulateQ_spec_query]
      case false =>
        rw [table_known]
        cases found : before.2 bytes with
        | some output =>
            rw [QueryImpl.withCaching_run_some _ found]
            simp only [RegistrationNativeSelectiveHiddenService.known, StateT.run, found,
              simulateQ_pure, map_pure]
            rfl
        | none =>
            rw [QueryImpl.withCaching_run_none _ found]
            simp only [RegistrationNativeSelectiveHiddenService.known, StateT.run, found,
              simulateQ_map, old_coins, Functor.map_map]
            rfl
      case true =>
        cases found : before.1.slots bytes with
        | some slot =>
            simp only [RegistrationNativeHiddenService.reserve, RegistrationNativeG3SelectedZeroTable.zero,
              RegistrationNativeG3FirstTouch.take, StateT.run, found, simulateQ_pure, map_pure,
              RegistrationNativeG3Tables.join]
            rfl
        | none =>
            by_cases room : before.1.next < n
            all_goals simp only [RegistrationNativeHiddenService.reserve, RegistrationNativeG3SelectedZeroTable.zero,
              RegistrationNativeG3FirstTouch.take, StateT.run, found, room, dite_true, dite_false,
              simulateQ_pure, map_pure, RegistrationNativeG3Tables.join,
              RegistrationNativeG3SelectedZeroTable.fallback]
            all_goals rfl

/-- The entire adaptive original fixed-key service retains its exact replies, selected slot dictionary and nonselected cache under the selected-only first-touch router. -/
theorem program_source (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (inside : Pqxdh.Bytes → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp KeySpec Value) (before : RegistrationNativeSelectiveHiddenService.State n) :
    Prod.map id project <$> simulateQ RegistrationNativeG3MetricCoins.localCoins
      ((simulateQ (RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate) work).run before) =
      (simulateQ (target (RegistrationNativeG3Tables.join materials seeds)
        (RegistrationNativeSelectiveHiddenService.selected inside candidate)) work).run (project before) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source materials seeds inside candidate) work before

end BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource.program_source
