-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore
/-! Structural attached Ed signing bills retain all opaque-owner, environment and external platform state. Hashes, KEM operations and independent sampling contribute zero; only the exact indexed signing query is counted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds
open RegistrationNativeIdentityFrontend (M Trusted)
variable {n : Nat} {KemSK Auxiliary A B : Type} {source : RegistrationNativeMldsa.Source}

def IsSign : (Trusted n KemSK).Domain → Prop
  | .inr (.service _ (.sign _)) => True
  | _ => False
instance : DecidablePred (IsSign (n := n) (KemSK := KemSK)) := fun query => by
  unfold IsSign
  split <;> infer_instance

def Bounded (work : M n KemSK Auxiliary source A) (cap : Nat) : Prop :=
  ∀ owners env, ((work.run owners).run env).IsQueryBoundP (IsSign (KemSK := KemSK)) cap

theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M n KemSK Auxiliary source A) cap :=
  fun _ _ => isQueryBoundP_pure _ _ _

theorem bind_bound (work : M n KemSK Auxiliary source A) (next : A → M n KemSK Auxiliary source B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded owners env) (fun result _ => rest result.1.1 result.1.2 result.2)

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

theorem effect_bound (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Bounded (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query)
      (if IsSign (KemSK := KemSK) (.inl (.inl query)) then 1 else 0) := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.effect, StateT.run, state_lift_apply, state_map_apply,
    Functor.map_map, isQueryBoundP_map_iff]
  by_cases active : IsSign (KemSK := KemSK) (.inl (.inl query)) <;>
    simp only [isQueryBoundP_query_iff, active, ite_true, ite_false] <;> simp

theorem kem_bound (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Bounded (RegistrationNativeIdentityFrontend.kem (n := n) (Auxiliary := Auxiliary) (source := source) query) 0 := by
  intro owners env
  simp [RegistrationNativeIdentityFrontend.kem, StateT.run, state_lift_apply, state_map_apply,
    Functor.map_map, isQueryBoundP_map_iff, IsSign]

theorem sample_bound (work : ProbComp A) :
    Bounded (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [RegistrationNativeIdentityFrontend.sample, simulateQ_pure] using pure_bound (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) value 0
  | query_bind query next ih =>
    simp only [RegistrationNativeIdentityFrontend.sample, simulateQ_bind, simulateQ_spec_query]
    exact bind_bound _ _ 0 0 (effect_bound (.inl query)) ih

theorem lift_free_bound (work : OracleComp (Trusted n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (IsSign (KemSK := KemSK)) cap) :
    Bounded (StateT.lift (StateT.lift work) : M n KemSK Auxiliary source A) cap := by
  intro owners env
  simpa only [StateT.run, state_lift_apply, state_map_apply, Functor.map_map, isQueryBoundP_map_iff] using bounded

theorem get_bound : Bounded (get : M n KemSK Auxiliary source (RegistrationNativeIdentityFrontend.State source)) 0 :=
  fun _ _ => isQueryBoundP_pure _ _ _

theorem modify_bound (update : RegistrationNativeIdentityFrontend.State source → RegistrationNativeIdentityFrontend.State source) :
    Bounded (modify update : M n KemSK Auxiliary source Unit) 0 :=
  fun _ _ => isQueryBoundP_pure _ _ _

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

theorem update_env_bound (update : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Bounded (RegistrationNativeIdentityFrontend.updateEnv (n := n) (KemSK := KemSK) (source := source) update) 0 := by
  intro owners env
  simp only [RegistrationNativeIdentityFrontend.updateEnv, StateT.run, state_lift_apply, state_map_apply,
    state_modify_apply, map_pure, isQueryBoundP_pure]

theorem hash_bound (request : registration.HashRequest) :
    Bounded (RegistrationNativeIdentityFrontend.hash (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) request) 0 :=
  effect_bound _
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.effect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.kem_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.sample_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.lift_free_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.lift_free_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.get_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.get_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.modify_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.modify_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.update_env_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.update_env_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFrontendEdBounds.hash_bound
