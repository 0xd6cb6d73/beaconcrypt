-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth

/-! The complete actual indexed identity service only appends private seeds. Ordinary callbacks, services and reveals preserve all existing handles. This source invariant applies to arbitrary adaptive programs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityFrontend (Trusted)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual indexed source callback preserves all earlier seed indices, including failed services and all ordinary World effects. -/
theorem query_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : (Trusted n KemSK).Domain)
    (before : State n KemSK) (result : (Trusted n KemSK).Range query × State n KemSK)
    (supported : result ∈ support ((implementation (mlSource := source) setup checks representation created query).run before)) :
    before.identities.seeds.IsPrefix result.2.identities.seeds := by
  cases query with
  | inl ordinary =>
      simp only [implementation, StateT.run, support_map] at supported
      obtain ⟨inner, _possible, equal⟩ := supported
      cases equal
      exact ⟨[], List.append_nil _⟩
  | inr query => cases query with
    | create =>
        rw [RegistrationNativeIdentitySourceBirth.query_source, support_map] at supported
        obtain ⟨seed, _possible, equal⟩ := supported
        cases equal
        exact ⟨[seed], rfl⟩
    | service handle request =>
        rw [RegistrationNativeIdentityWorld.service_source, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact ⟨[], List.append_nil _⟩
    | reveal handle =>
        simp only [implementation, PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
          StateT.run, simulateQ_pure, StateT.monad_pure_def, StateT.pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact ⟨[], List.append_nil _⟩

/-- Every complete adaptive identity-frontend source program retains the original private seed roster as a prefix. -/
theorem program_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : OracleComp (Trusted n KemSK) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created) work).run before)) :
    before.identities.seeds.IsPrefix result.2.identities.seeds := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query _
    (fun current => before.identities.seeds.IsPrefix current.identities.seeds)
    (fun query current prior next reached => prior.trans
      (query_prefix setup checks representation created query current next reached))
    work before ⟨[], List.append_nil _⟩ result supported

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix.query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix.query_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceSeedPrefix.program_prefix
