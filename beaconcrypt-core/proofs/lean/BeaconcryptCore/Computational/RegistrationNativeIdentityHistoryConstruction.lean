-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryPreparation
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryInvariant
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceDistinct

/-! Genuine indexed birth starts a new owner's chronological signing history empty. Earlier rejected future-handle calls cannot supply a signature receipt. Actual native construction retains synchronization for every earlier owner and derives it for the new owner, without public-key injectivity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityHistorySync (Synced Distinct)
open RegistrationNativeIdentityHistoryReserved (ReservedEmpty)
open RegistrationNativeIdentityHistoryInvariant (Holds)
open RegistrationNativeIdentityHistory (history)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem prepare_synced (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option (RegistrationNativeIdentityFrontend.Prepared source)) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (prior : Synced before.identities current)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.prepare source edPin mlPin keyId).run current).run env)).run before)) :
    Synced result.2.identities result.1.1.2 := by
  have same := RegistrationNativeIdentitySourcePrepareOwned.prepare_roster setup checks representation created edPin mlPin keyId current env before result supported
  have histories := RegistrationNativeIdentityHistoryPreparation.prepare_history setup checks representation created edPin mlPin keyId current env before result supported
  rw [same]
  intro owner member
  rw [histories]
  exact prior owner member

theorem append_synced (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeIdentityFrontend.Prepared source) (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (prior : Synced before.identities current)
    (fresh : history prepared.identity.handle before.identities.transcript = [])
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentitySourceCreate.append setup source edPin keyId prepared).run current).run env)).run before)) :
    Synced result.2.identities result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.append_program,
    RegistrationNativeIdentitySourceFrame.ambient_program, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query,
    mem_support_bind_iff, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
  obtain ⟨born, _, allocated, _, finished⟩ := reached
  cases finished
  intro owner member
  rw [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact prior owner member
  · change PqxdhJointIdentity.signedMessages (history prepared.identity.handle before.identities.transcript) = []
    rw [fresh]
    rfl

/-- Every complete source construction result has exactly the native chronological signing history at each generated handle. -/
theorem create_synced (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (prior : Synced before.identities current) (reserved : ReservedEmpty before.identities)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before)) :
    Synced result.2.identities result.1.1.2 := by
  rw [RegistrationNativeIdentitySourceCreate.create_factor] at supported
  simp only [StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  have synchronized := prepare_synced setup checks representation created edPin mlPin keyId current env before middle prior reached
  rcases middle with ⟨⟨⟨reply, nextOwners⟩, nextEnv⟩, nextPrivate⟩
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at continued
      cases continued
      exact synchronized
  | ok reply => cases reply with
    | none =>
        simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at continued
        cases continued
        exact synchronized
    | some prepared =>
        obtain ⟨value, handleEq, _publicEq, poolEq⟩ := RegistrationNativeIdentitySourceFresh.prepare_fresh
          setup checks representation created edPin mlPin keyId current nextOwners env nextEnv before nextPrivate prepared reached
        apply append_synced setup checks representation created edPin keyId prepared nextOwners nextEnv nextPrivate result synchronized _ continued
        rw [poolEq, handleEq]
        simpa [PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, history,
          RegistrationNativeIdentityHistory.entry, List.filterMap_append] using reserved before.identities.seeds.length (Nat.le_refl _)

/-- Ownership, handle distinctness and synchronized monitor histories all follow from the actual native constructor, including its failure paths. -/
theorem create_holds (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (current : RegistrationNativeIdentityFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : State n KemSK)
    (result : ((RustM (Option Nat) × RegistrationNativeIdentityFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × State n KemSK)
    (prior : Holds setup.joint before.identities current) (reserved : ReservedEmpty before.identities)
    (supported : result ∈ support ((simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.create setup source edPin mlPin keyId).run current).run env)).run before)) :
    Holds setup.joint result.2.identities result.1.1.2 :=
  ⟨RegistrationNativeIdentitySourceCreateOwned.create_owned setup checks representation created edPin mlPin keyId current env before result prior.1 supported,
    RegistrationNativeIdentitySourceDistinct.create_distinct setup checks representation created edPin mlPin keyId current env before result prior.1 prior.2.1 supported,
    create_synced setup checks representation created edPin mlPin keyId current env before result prior.2.2 reserved supported⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.prepare_synced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.prepare_synced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.append_synced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.append_synced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.create_synced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.create_synced

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.create_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryConstruction.create_holds
