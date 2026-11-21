-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceOwnership
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceCommon

/-! Every actual successful public constructor preparation derives ownership of its generated indexed credential. Preparation itself leaves the entire public roster unchanged; future source invariants can therefore retain prior owners while adding the genuine new identity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual shared-prefix preparation program returns only source-generated owned credentials on success. -/
theorem program_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (.ok (some prepared), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourcePrepare.program source edPin mlPin keyId)).run before)) :
    ∃ value, RegistrationNativeIdentityCallbacks.Owns setup.joint after.identities prepared.identity value := by
  rw [RegistrationNativeIdentitySourceCommon.exposed_factor] at supported
  simp only [RegistrationNativeIdentitySourceCommon.exposedProgram, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativeIdentitySourceFrame.ambient_program, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨⟨earlier, current⟩, _prefix, continued⟩ := supported
  cases earlier with
  | fail error => simp [RegistrationNativeIdentitySourceCommon.afterExposed, simulateQ_pure, StateT.run_pure] at continued
  | div => simp [RegistrationNativeIdentitySourceCommon.afterExposed, simulateQ_pure, StateT.run_pure] at continued
  | ok reply => cases reply with
    | none => simp [RegistrationNativeIdentitySourceCommon.afterExposed, simulateQ_pure, StateT.run_pure] at continued
    | some base =>
        exact RegistrationNativeIdentitySourceOwnership.suffix_owned setup checks representation created base
          ⟨current, before.identities⟩ after prepared continued

/-- Actual source preparation, including its full nested local state, derives the returned credential's source ownership. -/
theorem prepare_owned (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current afterOwners : RegistrationNativeIdentityFrontend.State source)
    (env afterEnv : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (((.ok (some prepared), afterOwners), afterEnv), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    ∃ value, RegistrationNativeIdentityCallbacks.Owns setup.joint after.identities prepared.identity value := by
  rw [RegistrationNativeIdentitySourcePrepare.prepare_run, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have projected := congrArg (fun output => (output.1.1.1, output.2)) equal
  apply program_owned setup checks representation created edPin mlPin keyId before after prepared
  rw [← projected]
  exact reached

/-- Preparation keeps the entire existing public owner roster on every actual source outcome. -/
theorem prepare_roster (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : State n KemSK)
    (result : ((RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    result.1.1.2 = current := by
  rw [RegistrationNativeIdentitySourcePrepare.prepare_run, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, _reached, equal⟩ := supported
  exact (congrArg (fun output => output.1.1.2) equal).symm

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.program_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.program_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.prepare_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.prepare_owned
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.prepare_roster' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned.prepare_roster
