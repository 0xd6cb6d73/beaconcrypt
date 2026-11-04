-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
import BeaconcryptCore.Computational.RegistrationNativeExperiment
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def Safe : (Trusted n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr (.hash _)) => True
  | .inr _ => True
  | _ => False

theorem sampled_owners (work : ProbComp A) (before : PqxdhRecordLiftWorld.State n)
    (result : A × PqxdhRecordLiftWorld.State n)
    (reached : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    result.2.owners = before.owners := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨inner, _called, same⟩ := reached
  cases same
  rfl

theorem coin_owners (query : unifSpec.Domain) (before : PqxdhRecordLiftWorld.State n)
    (result : unifSpec.Range query × PqxdhRecordLiftWorld.State n)
    (reached : result ∈ support ((PqxdhRecordLiftWorld.effects (.inl query)).run before)) :
    result.2.owners = before.owners :=
  sampled_owners _ (PqxdhRecordLiftWorld.chargeEffect (.inl query) before) result reached

theorem hash_owners (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n)
    (result : CtxRomAuth.CtxDigest × PqxdhRecordLiftWorld.State n)
    (reached : result ∈ support ((PqxdhRecordLiftWorld.effects (.inr (.hash bytes))).run before)) :
    result.2.owners = before.owners := by
  simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.capability, StateT.run,
    mem_support_bind_iff] at reached
  obtain ⟨inner, called, returned⟩ := reached
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases returned
  exact sampled_owners _ (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash bytes)) before) inner called

theorem trusted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (Trusted n KemSK).Domain) (safe : Safe query) (before : Native)
    (result : (Trusted n KemSK).Range query × Native)
    (reached : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners := by
  cases query with
  | inl query =>
      change result ∈ support ((RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.effects query)).run before) at reached
      simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
        Functor.map_map, support_map] at reached
      obtain ⟨inner, called, same⟩ := reached
      cases same
      cases query with
      | inl coin => exact coin_owners coin _ inner called
      | inr capability => cases capability with
        | hash bytes => exact hash_owners bytes _ inner called
        | _ => exact False.elim safe
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, mem_support_bind_iff] at reached
      obtain ⟨inner, called, returned⟩ := reached
      simp only [support_pure, Set.mem_singleton_iff] at returned
      cases returned
      exact sampled_owners _ _ inner called

theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp (Trusted n KemSK) A)
    (allowed : AllQueriesSatisfy work (Safe (n := n) (KemSK := KemSK))) (before : Native) (result : A × Native)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      cases reached
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨inner, called, continued⟩ := reached
      exact (ih inner.1 (allowed.2 inner.1) inner.2 result continued).trans
        (trusted setup checks representation created query allowed.1 before inner called)
end BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.sampled_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.sampled_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.coin_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.coin_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.hash_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.hash_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.trusted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame.program
