-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhIdentityCollisionReduction
import BeaconcryptCore.Computational.RegistrationNativeIdentityCallbacks
import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting
/-! Actual generated-handle receipts transport equal owner keys to a collision in the same private source seed table. The table is the reached prefix of one reserved family, which retains the existing zero-query weak-EUF collision loss and bills. The internal ownership/distinctness receipts must be derived by the actual initialized-source invariant; they are not new public endpoint assumptions. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision
open PqxdhJointIdentity
open PqxdhDeploymentServerAuthInjective
open RegistrationNativeIdentityInterface (Credential)

/-- Distinct source handles, their actual private seed-table receipts and equal generated public keys give an ordinary collision in that same seed table. -/
theorem credential_collision (joint : Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (credentials : List Credential)
    (owned : ∀ credential ∈ credentials, ∃ seed, RegistrationNativeIdentityCallbacks.Owns joint pool credential seed)
    (distinct : (credentials.map Credential.handle).Nodup)
    (first second : Nat) (different : first ≠ second) (left right : Credential)
    (leftAt : credentials[first]? = some left) (rightAt : credentials[second]? = some right)
    (same : left.publicIdentity.ed25519 = right.publicIdentity.ed25519) : Collision joint pool.seeds := by
  obtain ⟨leftSeed, leftOwned⟩ := owned left (List.mem_of_getElem? leftAt)
  obtain ⟨rightSeed, rightOwned⟩ := owned right (List.mem_of_getElem? rightAt)
  have leftHandle : (credentials.map Credential.handle)[first]? = some left.handle := by
    simp only [List.getElem?_map, leftAt, Option.map_some]
  have rightHandle : (credentials.map Credential.handle)[second]? = some right.handle := by
    simp only [List.getElem?_map, rightAt, Option.map_some]
  have handles : left.handle ≠ right.handle := by
    intro equal
    have sameAt := leftHandle.trans ((congrArg some equal).trans rightHandle.symm)
    exact different (distinct.eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp leftHandle).1 sameAt)
  refine ⟨left.handle, right.handle, handles, leftSeed, rightSeed, leftOwned.1, rightOwned.1, ?_⟩
  rw [← leftOwned.2, ← rightOwned.2]
  exact same

/-- The private source seed table is the reached prefix of its one reserved family, so any source-table collision is already a collision of that same family. -/
theorem source_state_collision (joint : Primitives) {count : Nat}
    (seeds : Fin count → IdentitySeed) (state : PqxdhDynamicIdentityRouting.PublicState)
    (collision : Collision joint (PqxdhDynamicIdentityRouting.sourceState seeds state).seeds) :
    Collision joint (List.ofFn seeds) :=
  collision_take joint (List.ofFn seeds) state.created collision

/-- Every complete continuation of one reserved generated family has the original zero-query collision bound for its actual source seed prefix. The continuation and its full result are unrestricted. -/
theorem family_prefix_bound {ι A : Type} {base : OracleSpec ι} {KemSK : Type}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (count : Nat)
    (next : (Fin (count + 1) → IdentitySeed) → ProbComp A)
    (state : A → PqxdhDynamicIdentityRouting.PublicState) :
    Pr{let result ← (do
       let seeds ← PqxdhJointIdentityFamily.sampleFamily (count + 1)
       let value ← next seeds
       pure (seeds, value))}[Collision setup.joint (PqxdhDynamicIdentityRouting.sourceState result.1 (state result.2)).seeds] ≤
      ∑ target : Fin (count + 1), advantage setup.joint (collider setup.joint count target) := by
  have included :
      Pr{let result ← (do
         let seeds ← PqxdhJointIdentityFamily.sampleFamily (count + 1)
         let value ← next seeds
         pure (seeds, value))}[Collision setup.joint (PqxdhDynamicIdentityRouting.sourceState result.1 (state result.2)).seeds] ≤
      Pr{let seeds ← PqxdhJointIdentityFamily.sampleFamily (count + 1)}[Collision setup.joint (List.ofFn seeds)] := by
    apply prEvent_bind_le_prEvent_of_support _ _ _ _
    intro seeds _sampled free
    rw [bind_pure_comp, prEvent_map, OracleComp.prEvent_eq_zero_iff]
    intro value _supported collision
    exact free (source_state_collision setup.joint seeds (state value) collision)
  exact included.trans (by simpa only [PqxdhDynamicIdentityPool.sampleSeeds, prEvent_map] using collision_bound setup count)

end BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.credential_collision' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.credential_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.source_state_collision' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.source_state_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.family_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedIdentityCollision.family_prefix_bound
