-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhIdentityCollisionReduction

/-! The actual on-demand generated-identity source has the original zero-query collision loss. Reserving a bounded future seed family preserves the whole execution, and every reached eager source table is its literal prefix. Service calls, reveals, adaptive failure and unused future identities remain unrestricted. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound
open PqxdhJointIdentity
open PqxdhDynamicIdentityPool
open PqxdhDeploymentServerAuthInjective (Collision collider collision_bound)

/-- An eager creation can append only the next seed of the same reserved pool. -/
theorem eager_step_prefix (joint : Primitives) (pool : List IdentitySeed)
    (query : DynamicSpec.Domain) (before : SourceState)
    (prior : before.seeds <+: pool) (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((eagerImpl joint pool query).run before)) :
    result.2.seeds <+: pool := by
  obtain ⟨future, rfl⟩ := prior
  cases query with
  | inl coin =>
      simp only [eagerImpl, poolImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _drawn, returned⟩ := supported
      simp only [mem_support_pure_iff] at returned
      cases returned
      exact List.prefix_append before.seeds future
  | inr query => cases query with
    | create =>
        have lookup : (before.seeds ++ future)[before.seeds.length]? = future[0]? := by
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        simp only [eagerImpl, poolImpl, StateT.run, pure_bind, lookup] at supported
        cases future with
        | nil =>
            simp only [List.getElem?_nil, mem_support_pure_iff] at supported
            cases supported
            simpa only [record, List.append_nil] using List.prefix_refl before.seeds
        | cons seed rest =>
            simp only [List.getElem?_cons_zero, mem_support_pure_iff] at supported
            cases supported
            exact ⟨rest, by simp [record, List.append_assoc]⟩
    | service identity request =>
        simp only [eagerImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        exact List.prefix_append before.seeds future
    | reveal identity =>
        simp only [eagerImpl, poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        exact List.prefix_append before.seeds future

/-- Every continued eager execution retains its complete source table as a prefix of the same reserved pool. -/
theorem eager_run_prefix {Value : Type} (joint : Primitives) (pool : List IdentitySeed)
    (work : OracleComp DynamicSpec Value) (before : SourceState) (prior : before.seeds <+: pool)
    (result : Value × SourceState)
    (supported : result ∈ support ((simulateQ (eagerImpl joint pool) work).run before)) :
    result.2.seeds <+: pool :=
  simulateQ_run_preservesInv (eagerImpl joint pool) (fun current => current.seeds <+: pool)
    (fun query current earlier later reached => eager_step_prefix joint pool query current earlier later reached)
    work before prior result supported

/-- A collision in a reached source prefix is a collision in that exact reserved pool. -/
theorem prefix_collision (joint : Primitives) (prefixSeeds pool : List IdentitySeed)
    (prior : prefixSeeds <+: pool) (collision : Collision joint prefixSeeds) : Collision joint pool := by
  rw [List.prefix_iff_eq_take.mp prior] at collision
  exact PqxdhDeploymentServerAuthInjective.collision_take joint pool prefixSeeds.length collision

/-- On-demand generation pays exactly the existing sum of zero-query weak-EUF collision advantages; all continued source behavior remains unrestricted. -/
theorem lazy_collision_bound {ι KemSK Value : Type} {base : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (work : OracleComp DynamicSpec Value)
    (count : Nat) (bounded : work.IsQueryBoundP IsCreate (count + 1)) :
    Pr{let result ← (simulateQ (lazyImpl setup.joint) work).run initialState}[Collision setup.joint result.2.seeds] ≤
      ∑ target : Fin (count + 1), advantage setup.joint (collider setup.joint count target) := by
  have reserved := lazy_eager_complete setup.joint work (count + 1) bounded initialState
  have included :
      Pr{let result ← (sampleSeeds (count + 1) >>= fun pool =>
        (simulateQ (eagerImpl setup.joint pool) work).run initialState)}[Collision setup.joint result.2.seeds] ≤
      Pr{let pool ← sampleSeeds (count + 1)}[Collision setup.joint pool] := by
    apply prEvent_bind_le_prEvent_of_support _ _ _ _
    intro pool _sampled free
    rw [OracleComp.prEvent_eq_zero_iff]
    intro result reached collision
    exact free (prefix_collision setup.joint result.2.seeds pool
      (eager_run_prefix setup.joint pool work initialState List.nil_prefix result reached) collision)
  exact (reserved.prEvent_eq (fun result => Collision setup.joint result.2.seeds)).trans_le
    (included.trans (collision_bound setup count))

end BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.eager_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.eager_step_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.eager_run_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.eager_run_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.prefix_collision' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.prefix_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.lazy_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCollisionBound.lazy_collision_bound
