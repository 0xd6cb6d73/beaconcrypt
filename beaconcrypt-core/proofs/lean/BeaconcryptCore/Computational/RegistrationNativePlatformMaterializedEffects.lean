-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedPublicationFree
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonServer
/-! Fixed private seeds materialize only hidden installation references in the actual new effect language. Source allocation, hash, signature, writer and all external coins stay in their original free order. Actual publication is structurally installation-free, so its complete source tree is unchanged by this materialization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePlatformEffectCompiler (Spec)
open RegistrationNativePlatformPairedPublicationFree (Allowed Quiet)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {A S Encoded : Type}

noncomputable def realize (seeds : Seeds n) : QueryImpl (Spec n) (OracleComp (Spec n))
  | .inl (.inr (.installServer keyId binding (.hidden slot))) => (Spec n).query
      (.inl (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot))))))
  | .inl (.inr (.installBeacon owner shell (.hidden slot))) => (Spec n).query
      (.inl (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot))))))
  | query => (Spec n).query query

def effect : QueryImpl (EnvEffects n) (OracleComp (Spec n)) := fun query => (Spec n).query (.inl query)

private theorem query_free (seeds : Seeds n) (query : (Spec n).Domain) (allowed : Allowed query) :
    realize seeds query = (Spec n).query query := by
  cases query with
  | inr coin => rfl
  | inl query => cases query with
    | inl coin => rfl
    | inr capability => cases capability with
      | installServer keyId binding tag => exact (allowed .server rfl).elim
      | installBeacon owner shell tag => exact (allowed .beacon rfl).elim
      | _ => rfl

/-- Every literal installation-free free program, including actual publication and all randomized platform failures, is unchanged by fixed private seed materialization. -/
theorem program_free (seeds : Seeds n) (work : OracleComp (Spec n) A)
    (allowed : work.AllQueriesSatisfy Allowed) : simulateQ (realize seeds) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, query_free seeds query allowed.1]
    congr 1
    funext reply
    exact ih reply (allowed.2 reply)

/-- A stateful actual source publication retains its complete returned state under materialization, with no condition on the private seed/cache or prior use of a role. -/
theorem state_free (seeds : Seeds n) (work : StateT S (OracleComp (Spec n)) A)
    (quiet : Quiet work) (before : S) : simulateQ (realize seeds) (work.run before) = work.run before :=
  program_free seeds _ (quiet before)

private theorem install (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded) (seeds : Seeds n)
    (canonical : published.kernel = PqxdhRecordLiftWorld.kernel .server (seeds slot)) :
    simulateQ effect (RegistrationNativePairedServerService.knownInstall control published) =
      simulateQ (realize seeds) (simulateQ effect (RegistrationHiddenInstall.install control slot published)) := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationNativePairedServerService.knownInstall, RegistrationHiddenInstall.install, prepared]
      rfl
  | Ok pending =>
      rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared,
        RegistrationHiddenInstall.install_native control slot published pending prepared, retained.2.2.2.1, canonical]
      rfl

/-- Actual known-kernel insertion is the same reached source continuation as hidden-reference insertion under the fixed seed table, including every failed publication and failed install. -/
theorem after_replaced (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (seeds : Seeds n) (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    simulateQ effect (RegistrationNativePairedServerService.knownAfter control
      (RegistrationPublicationKernelErasure.result (PqxdhRecordLiftWorld.kernel .server (seeds slot)) published)) =
      simulateQ (realize seeds) (simulateQ effect (RegistrationHiddenInstall.after control slot published)) := by
  cases published with
  | fail error | div => rfl
  | ok value => cases value with
    | Err previous => rfl
    | Ok completed =>
      have same := install control slot
        (RegistrationPublicationKernelErasure.published (PqxdhRecordLiftWorld.kernel .server (seeds slot)) completed) seeds rfl
      rw [RegistrationHiddenInstall.install_map] at same
      exact same
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.program_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.state_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.state_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.after_replaced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedEffects.after_replaced
