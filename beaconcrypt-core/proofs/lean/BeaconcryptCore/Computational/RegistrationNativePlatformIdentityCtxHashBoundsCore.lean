-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds
/-! Resource accounting retains physical shared hashes separately from native and public sampler coins. The Main/Context lenses and adaptive sequencing preserve actual all-reply hash caps. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore
open RegistrationNativePlatformIdentityCtxMain (M)
open RegistrationNativePlatformIdentityCtxBackend (IsHash)
variable {n : Nat} {KemSK Platform A B : Type} {source : RegistrationNativeMldsa.Source}

def Bounded (work : M n KemSK Platform source A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP IsHash cap

def ContextBounded (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A) (cap : Nat) : Prop :=
  ∀ before, (work.run before).IsQueryBoundP RegistrationNativePlatformCtxBirthdayBudget.IsHash cap

/-- The explicit backend embedding forwards each hash once and forwards coins into the separate protocol branch. -/
theorem backend_bound (work : OracleComp RegistrationNativePlatformCtxBackend.Spec A) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformCtxBirthdayBudget.IsHash cap) :
    (simulateQ RegistrationNativePlatformIdentityCtxCompiler.backend work).IsQueryBoundP IsHash cap := by
  apply bounded.simulateQ_of_step
  · intro query active
    cases query with
    | inl bytes => simp [RegistrationNativePlatformIdentityCtxCompiler.backend, IsHash]
    | inr coin => exact False.elim active
  · intro query inactive
    cases query with
    | inl bytes => exact False.elim (inactive trivial)
    | inr coin => simp [RegistrationNativePlatformIdentityCtxCompiler.backend, IsHash]

/-- Pure source outcomes issue no additional shared hash. -/
theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M n KemSK Platform source A) cap :=
  fun _ => isQueryBoundP_pure _ _ _

/-- Every adaptive continuation receives the reached state and retains the sum of its literal source hash allowances. -/
theorem bind_bound (work : M n KemSK Platform source A) (next : A → M n KemSK Platform source B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro before
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before) (fun result _ => rest result.1 result.2)

/-- Lifting the actual ordinary Context program cannot add a hash query or charge public coins as hashes. -/
theorem ordinary_bound (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A) (cap : Nat)
    (bounded : ContextBounded work cap) :
    Bounded (RegistrationNativePlatformIdentityCtxOrdinary.ordinary (source := source) work) cap := by
  intro before
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.ordinary, RegistrationNativePlatformIdentityCtxCompiler.ordinary,
    StateT.run, isQueryBoundP_map_iff]
  exact backend_bound _ cap (bounded (before.1.context, before.2))

/-- Mapping public results leaves the actual Context hash bill unchanged. -/
theorem context_map_bound (work : RegistrationNativePlatformCtxContext.M n KemSK Platform A) (observe : A → B)
    (cap : Nat) (bounded : ContextBounded work cap) : ContextBounded (observe <$> work) cap := by
  intro before
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact bounded before

/-- The complete ordinary World lens keeps the actual leaf bill and external sampler tree. -/
theorem world_bound (work : RegistrationNativePlatformCtxRunner.M (PqxdhRecordLiftWorld.State n) Platform A)
    (cap : Nat) (bounded : RegistrationNativePlatformCtxLeafHashBounds.Bounded work cap) :
    ContextBounded (RegistrationNativePlatformCtxContext.world (KemSK := KemSK) work) cap := by
  rintro ⟨before, previous⟩
  simpa only [RegistrationNativePlatformCtxContext.world, StateT.run, isQueryBoundP_map_iff] using
    bounded before.server.world.world.1 previous

/-- The full SDK-to-Context lens cannot add shared hash calls. -/
theorem server_bound (work : RegistrationNativePlatformCtxRunner.M (RegistrationServerFrontendCompiler.State n) Platform A)
    (cap : Nat) (bounded : RegistrationNativePlatformCtxLeafHashBounds.Bounded work cap) :
    ContextBounded (RegistrationNativePlatformCtxBuild.server (KemSK := KemSK) work) cap := by
  rintro ⟨before, previous⟩
  simpa only [RegistrationNativePlatformCtxBuild.server, StateT.run, isQueryBoundP_map_iff] using
    bounded before.server previous
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.backend_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.pure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.ordinary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.ordinary_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.context_map_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.context_map_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.world_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.world_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHashBoundsCore.server_bound
