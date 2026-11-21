-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReserved
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceFresh

/-! Actual native preparation performs pure full-pin selection, one indexed identity birth and ordinary prekey sampling. It issues no signing or static-DH service, so every earlier generated-handle history stays exact on success and failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityHistory (history)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem suffix_history (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (pin : session.ServerAuthenticationPin)
    (before : State n KemSK)
    (result : RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (RegistrationNativeIdentitySourceSuffix.exposed (source := source) pin)).run before)) :
    ∀ identity, history identity result.2.identities.transcript = history identity before.identities.transcript := by
  simp only [RegistrationNativeIdentitySourceSuffix.exposed, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativeIdentitySourceBirth.create_source, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨value, _drawn, continued⟩ := supported
  simp only [RegistrationNativeIdentitySourceSuffix.newSample, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure] at continued
  rw [RegistrationNativeIdentitySourceFrame.ambient_program, bind_map_left, mem_support_bind_iff] at continued
  obtain ⟨scalar, _sampled, returned⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases returned
  intro identity
  simp [RegistrationNativeIdentitySourceBirth.born, PqxdhDynamicIdentityPool.createdReply,
    PqxdhDynamicIdentityPool.record, history, RegistrationNativeIdentityHistory.entry, List.filterMap_append]

theorem program_history (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State n KemSK)
    (result : RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (RegistrationNativeIdentitySourcePrepare.program source edPin mlPin keyId)).run before)) :
    ∀ identity, history identity result.2.identities.transcript = history identity before.identities.transcript := by
  rw [RegistrationNativeIdentitySourceCommon.exposed_factor] at supported
  simp only [RegistrationNativeIdentitySourceCommon.exposedProgram, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativeIdentitySourceFrame.ambient_program, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨⟨earlier, current⟩, _prefix, continued⟩ := supported
  cases earlier with
  | fail error | div =>
      simp only [RegistrationNativeIdentitySourceCommon.afterExposed, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at continued
      cases continued
      intro identity
      rfl
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeIdentitySourceCommon.afterExposed, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at continued
        cases continued
        intro identity
        rfl
    | some selected =>
        exact suffix_history setup checks representation created selected
          ⟨current, before.identities⟩ result continued

/-- The complete nested actual preparation retains every prior source history without assuming source success. -/
theorem prepare_history (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    ∀ identity, history identity result.2.identities.transcript = history identity before.identities.transcript := by
  rw [RegistrationNativeIdentitySourcePrepare.prepare_run, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact program_history setup checks representation created edPin mlPin keyId before inner reached

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.suffix_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.suffix_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.program_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.prepare_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation.prepare_history
