-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSource
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBound
/-! Closing the private indexed service over uniform coins leaves the same explicit physical CTX client. This statistical compiler may hold the private service table; it is not an executable selected-identity forgery reduction. -/
open OracleComp OracleSpec CoreModels ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open PqxdhDynamicIdentityPool (SourceState)
variable {A : Type}

noncomputable def free (joint : PqxdhJointIdentity.Primitives) :
    QueryImpl Spec (StateT SourceState (OracleComp RegistrationNativePlatformCtxBackend.Spec))
  | .inl query => fun before => simulateQ RegistrationNativePlatformCtxBackend.coin
      ((RegistrationNativeIdentityMainSource.implementation joint query).run before)
  | .inr bytes => fun before => (fun reply => (reply, before)) <$>
      RegistrationNativePlatformCtxBackend.Spec.query (.inl bytes)

/-- Reassociate both genuine private interpreter coordinates without dropping service or cache state. -/
def flatten (result : (A × SourceState) × RegistrationNativePlatformCtxBackend.State) :
    A × RegistrationNativePlatformIdentityCtxSource.State := (result.1.1, (result.1.2, result.2))

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

/-- Every actual service/hash query has the same complete source result after closing the physical backend. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (query : Spec.Domain)
    (before : RegistrationNativePlatformIdentityCtxSource.State) :
    flatten <$> (simulateQ RegistrationNativePlatformCtxBackend.implementation ((free joint query).run before.1)).run before.2 =
      (RegistrationNativePlatformIdentityCtxSource.implementation joint query).run before := by
  cases query with
  | inl query =>
    simp only [free, StateT.run]
    rw [RegistrationNativePlatformCtxBackend.coins]
    simp only [state_lift_apply, Functor.map_map, flatten,
      RegistrationNativePlatformIdentityCtxSource.implementation, StateT.run]
    rfl
  | inr bytes =>
    simp only [free, StateT.run, simulateQ_map, simulateQ_spec_query,
      RegistrationNativePlatformCtxBackend.implementation,
      RegistrationNativePlatformIdentityCtxSource.implementation, state_map_apply, Functor.map_map, flatten, Prod.map_def, id_eq]
    rfl

private theorem interpreter (joint : PqxdhJointIdentity.Primitives) :
    (RegistrationNativePlatformCtxBackend.implementation.mapStateTBase (free joint)).flattenStateT =
      RegistrationNativePlatformIdentityCtxSource.implementation joint := by
  ext current before
  exact query joint current before

/-- Arbitrary adaptive indexed work retains every service row, raw counter reply and physical cache coordinate. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A)
    (before : RegistrationNativePlatformIdentityCtxSource.State) :
    flatten <$> (simulateQ RegistrationNativePlatformCtxBackend.implementation ((simulateQ (free joint) work).run before.1)).run before.2 =
      (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run before := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, interpreter]
  simp only [Functor.map_map, flatten, Prod.eta]
  exact id_map _

def IsHash : Spec.Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred IsHash := fun query => by cases query <;> simp only [IsHash] <;> infer_instance

private theorem coins_zero {X : Type} (work : ProbComp X) :
    (simulateQ RegistrationNativePlatformCtxBackend.coin work).IsQueryBoundP RegistrationNativePlatformCtxBirthdayBudget.IsHash 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformCtxBackend.coin,
      isQueryBoundP_query_bind_iff, RegistrationNativePlatformCtxBirthdayBudget.IsHash,
      not_false_eq_true, true_or, ite_false]
    exact ⟨trivial, ih⟩

/-- Closing the genuine indexed service cannot add a shared hash query; its sampler coins remain separately counted. -/
theorem hash_bound (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A) (future : Nat)
    (bounded : work.IsQueryBoundP IsHash future) (before : SourceState) :
    ((simulateQ (free joint) work).run before).IsQueryBoundP RegistrationNativePlatformCtxBirthdayBudget.IsHash future := by
  apply bounded.simulateQ_run_of_step
  · intro current actual previous
    cases current with
    | inl query => exact False.elim actual
    | inr bytes =>
      simp only [free, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        RegistrationNativePlatformCtxBirthdayBudget.IsHash]
      decide
  · intro current inactive previous
    cases current with
    | inl query => exact coins_zero _
    | inr bytes => exact False.elim (inactive trivial)

/-- The actual shared-cache collision mass for one complete indexed run pays one warm-cache birthday term, with no owner union. -/
theorem collision_bound (joint : PqxdhJointIdentity.Primitives) (work : OracleComp Spec A) (future : Nat)
    (bounded : work.IsQueryBoundP IsHash future) (before : RegistrationNativePlatformIdentityCtxSource.State)
    (warm : RegistrationNativePlatformCtxBirthdayCache.Warm before.2.1) :
    𝒟[(fun result : A × RegistrationNativePlatformIdentityCtxSource.State =>
      @decide (PqxdhRecordFactsCollisionCache.Collision (fun _ => true) result.2.2.1) (Classical.propDecidable _)) <$>
        (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint) work).run before] {true} ≤
      ((future + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  have tight := RegistrationNativePlatformCtxBirthdayBound.physical_bound ((simulateQ (free joint) work).run before.1)
    future (hash_bound joint work future bounded before.1) before.2 warm
  rw [← program joint work before, Functor.map_map]
  exact tight
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.hash_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend.collision_bound
