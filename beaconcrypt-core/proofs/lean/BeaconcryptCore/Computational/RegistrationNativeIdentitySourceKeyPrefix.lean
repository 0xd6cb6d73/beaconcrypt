-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct
import BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata

/-! Actual construction preserves the entire old immutable key roster as an ordered prefix. Preparation may fail after private source effects; the public append occurs only on the literal successful suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceKeyPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityMetadata (keys)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem append_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeIdentityFrontend.Prepared source) (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentitySourceCreate.append setup source edPin keyId prepared).run current).run env)).run before)) :
    keys current <+: keys result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program,
    RegistrationNativeIdentitySourceFrame.ambient_program, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
  obtain ⟨born, _generated, allocated, _allocated, returned⟩ := reached
  cases returned
  simp only [keys, List.map_append]
  exact List.prefix_append _ _

/-- Every actual constructor outcome keeps all previous immutable owner keys at their original indices. -/
theorem create_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before)) :
    keys current <+: keys result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have same := RegistrationNativeIdentitySourcePrepareOwned.prepare_roster setup checks representation created edPin mlPin keyId current env before middle reached
  rcases middle with ⟨⟨⟨reply, nextOwners⟩, nextEnv⟩, nextPrivate⟩
  change nextOwners = current at same
  subst nextOwners
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at continued
      cases continued
      exact List.prefix_rfl
  | ok reply => cases reply with
    | none =>
        simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at continued
        cases continued
        exact List.prefix_rfl
    | some prepared => exact append_prefix setup checks representation created edPin keyId prepared current nextEnv nextPrivate result continued

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceKeyPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceKeyPrefix.create_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceKeyPrefix.create_prefix
