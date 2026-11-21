-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreate
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned

/-! Actual complete native identity construction preserves source ownership of all earlier credentials and derives ownership for its newly appended owner. The invariant begins at the generated empty public roster, without key injectivity or public-event restrictions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityRealization (Owned)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual preparation outcome preserves source ownership of its unchanged prior roster. -/
theorem prepare_old_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (owned : Owned setup.joint before.identities current)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    Owned setup.joint result.2.identities result.1.1.2 := by
  have same := RegistrationNativeIdentitySourcePrepareOwned.prepare_roster setup checks representation created edPin mlPin keyId current env before result supported
  have preserved := RegistrationNativeIdentitySourceSeedPrefix.program_prefix setup checks representation created _ before result supported
  rw [same]
  intro selected member
  obtain ⟨value, found⟩ := owned selected member
  exact ⟨value, RegistrationNativeIdentitySourceRealizePrefix.owns setup.joint before.identities result.2.identities preserved selected.identity value found⟩

/-- Literal KEM/owner allocation appends only its already source-owned credential and preserves every existing owner. -/
theorem append_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeIdentityFrontend.Prepared source) (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (owned : Owned setup.joint before.identities current)
    (fresh : ∃ value, RegistrationNativeIdentityCallbacks.Owns setup.joint before.identities prepared.identity value)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentitySourceCreate.append setup source edPin keyId prepared).run current).run env)).run before)) :
    Owned setup.joint result.2.identities result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program,
    RegistrationNativeIdentitySourceFrame.ambient_program, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨born, _generated, allocated, _allocated, returned⟩ := reached
  cases returned
  intro selected member
  rw [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact owned selected member
  · exact fresh

/-- The actual complete public constructor preserves credential ownership on every failure and derives the new owner's ownership on success. -/
theorem create_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (owned : Owned setup.joint before.identities current)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before)) :
    Owned setup.joint result.2.identities result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have prior := prepare_old_owned setup checks representation created edPin mlPin keyId current env before middle owned reached
  rcases middle with ⟨⟨⟨reply, nextOwners⟩, nextEnv⟩, nextPrivate⟩
  cases reply with
  | fail error =>
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact prior
  | div =>
      simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact prior
  | ok reply => cases reply with
    | none =>
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact prior
    | some prepared =>
        have fresh := RegistrationNativeIdentitySourcePrepareOwned.prepare_owned setup checks representation created edPin mlPin keyId
          current nextOwners env nextEnv before nextPrivate prepared reached
        exact append_owned setup checks representation created edPin keyId prepared nextOwners nextEnv nextPrivate result prior fresh continued

/-- The actual empty generated public roster establishes credential ownership without a supplied source invariant. -/
theorem empty_owned (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhDynamicIdentityPool.SourceState) :
    Owned joint pool ([] : RegistrationNativeIdentityFrontend.State source) := by
  intro selected member
  cases member

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.prepare_old_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.prepare_old_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.append_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.append_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.create_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.create_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.empty_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCreateOwned.empty_owned
