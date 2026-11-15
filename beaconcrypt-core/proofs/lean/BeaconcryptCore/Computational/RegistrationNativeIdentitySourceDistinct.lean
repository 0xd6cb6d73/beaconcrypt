-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned

/-! Actual native construction gives each public credential its fresh generated pool index. Distinct handles are derived from the existing source ownership invariant, without assuming public-key injectivity or changing alias reporting. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityRealization (Owned)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- An actually owned public credential refers to a genuine earlier private identity index. -/
theorem owned_handle_lt (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhDynamicIdentityPool.SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source) (owned : Owned joint pool owners)
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ owners) :
    owner.identity.handle < pool.seeds.length := by
  obtain ⟨value, stored⟩ := owned owner member
  exact (List.getElem?_eq_some_iff.mp stored.1).1

private theorem append_distinct (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeIdentityFrontend.Prepared source) (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (distinct : (current.map fun owner => owner.identity.handle).Nodup)
    (fresh : ∀ owner ∈ current, owner.identity.handle ≠ prepared.identity.handle)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentitySourceCreate.append setup source edPin keyId prepared).run current).run env)).run before)) :
    (result.1.1.2.map fun owner => owner.identity.handle).Nodup := by
  rw [RegistrationNativeIdentitySourceCreate.append_program,
    RegistrationNativeIdentitySourceFrame.ambient_program, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨born, _generated, allocated, _allocated, returned⟩ := reached
  cases returned
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil, List.nodup_append]
  refine ⟨distinct, by simp, ?_⟩
  intro handle member next same
  simp only [List.mem_singleton] at same
  subst next
  obtain ⟨owner, old, rfl⟩ := List.mem_map.mp member
  exact fresh owner old

/-- Actual complete native creation preserves distinct generated identity handles on every failure and successful append; public-key aliases remain unrestricted. -/
theorem create_distinct (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (owned : Owned setup.joint before.identities current)
    (distinct : (current.map fun owner => owner.identity.handle).Nodup)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before)) :
    (result.1.1.2.map fun owner => owner.identity.handle).Nodup := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have same := RegistrationNativeIdentitySourcePrepareOwned.prepare_roster setup checks representation created edPin mlPin keyId current env before middle reached
  rcases middle with ⟨⟨⟨reply, nextOwners⟩, nextEnv⟩, nextPrivate⟩
  change nextOwners = current at same
  have prior : (nextOwners.map fun owner => owner.identity.handle).Nodup := by
    rw [same]
    exact distinct
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact prior
  | ok reply => cases reply with
    | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact prior
    | some prepared =>
        obtain ⟨value, handleEq, _publicEq, _poolEq⟩ := RegistrationNativeIdentitySourceFresh.prepare_fresh
          setup checks representation created edPin mlPin keyId current nextOwners env nextEnv before nextPrivate prepared reached
        apply append_distinct setup checks representation created edPin keyId prepared nextOwners nextEnv nextPrivate result prior _ continued
        intro owner member
        have old : owner ∈ current := same ▸ member
        rw [handleEq]
        exact Nat.ne_of_lt (owned_handle_lt setup.joint before.identities current owned owner old)

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct.owned_handle_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct.owned_handle_lt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct.create_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct.create_distinct
