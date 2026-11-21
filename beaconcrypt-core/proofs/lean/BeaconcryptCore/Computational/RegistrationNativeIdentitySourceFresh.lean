-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourcePrepareOwned

/-! Successful native identity preparation returns the next genuine private identity handle and exactly one private source creation observation. Earlier identities and their source transcript prefix remain literal; public-key equality is never used as identity ownership. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentitySourceBirth (born credential)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- A successful actual identity/prekey suffix returns exactly the pre-birth pool length and preserves the complete original transcript before its one creation observation. -/
theorem suffix_fresh (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pin : session.ServerAuthenticationPin)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (.ok (some prepared), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourceSuffix.exposed (source := source) pin)).run before)) :
    ∃ value, prepared.identity = credential setup.joint before value ∧
      after.identities = (PqxdhDynamicIdentityPool.createdReply setup.joint before.identities value).2 := by
  simp only [RegistrationNativeIdentitySourceSuffix.exposed, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativeIdentitySourceBirth.create_source, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨value, _drawn, continued⟩ := supported
  simp only [RegistrationNativeIdentitySourceSuffix.newSample, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure] at continued
  rw [RegistrationNativeIdentitySourceFrame.ambient_program, bind_map_left, mem_support_bind_iff] at continued
  obtain ⟨scalar, _sampled, returned⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at returned
  obtain ⟨preparedEq, afterEq⟩ := returned
  subst prepared
  subst after
  exact ⟨value, rfl, rfl⟩

/-- Every successful complete preparation program has one fresh handle and its exact generated private source append. -/
theorem program_fresh (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (.ok (some prepared), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (RegistrationNativeIdentitySourcePrepare.program source edPin mlPin keyId)).run before)) :
    ∃ value, prepared.identity.handle = before.identities.seeds.length ∧
      prepared.identity.publicIdentity = setup.joint.publicKeys value ∧
      after.identities = (PqxdhDynamicIdentityPool.createdReply setup.joint before.identities value).2 := by
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
        obtain ⟨value, identityEq, poolEq⟩ := suffix_fresh setup checks representation created base
          ⟨current, before.identities⟩ after prepared continued
        exact ⟨value, congrArg (fun selected => selected.handle) identityEq,
          congrArg (fun selected => selected.publicIdentity) identityEq, poolEq⟩

/-- The full nested source preparation exposes the same fresh-handle and literal private append receipt, with no supplied success or ownership premise. -/
theorem prepare_fresh (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current afterOwners : RegistrationNativeIdentityFrontend.State source)
    (env afterEnv : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before after : State n KemSK) (prepared : RegistrationNativeIdentityFrontend.Prepared source)
    (supported : (((.ok (some prepared), afterOwners), afterEnv), after) ∈ support
      ((simulateQ (implementation (mlSource := source) setup checks representation created)
        (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    ∃ value, prepared.identity.handle = before.identities.seeds.length ∧
      prepared.identity.publicIdentity = setup.joint.publicKeys value ∧
      after.identities = (PqxdhDynamicIdentityPool.createdReply setup.joint before.identities value).2 := by
  rw [RegistrationNativeIdentitySourcePrepare.prepare_run, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have projected := congrArg (fun output => (output.1.1.1, output.2)) equal
  apply program_fresh setup checks representation created edPin mlPin keyId before after prepared
  rw [← projected]
  exact reached

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.suffix_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.suffix_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.program_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.program_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.prepare_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh.prepare_fresh
