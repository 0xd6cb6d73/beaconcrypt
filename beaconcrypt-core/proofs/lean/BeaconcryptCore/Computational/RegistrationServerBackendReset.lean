-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
import BeaconcryptCore.Computational.RegistrationServerRoleBackend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! A genuine Fresh Server entry first generates and overwrites the sole ephemeral role field. Its complete result and query/reply trace are therefore independent of a prior Server ephemeral, including rejected later replies. No empty-auxiliary admission premise is needed. -/
namespace BeaconcryptCore.Computational.RegistrationServerBackendReset
open RegistrationAgreementExecutor RegistrationAgreementQueryTrace
variable {ι KemSK Value : Type} {base : OracleSpec ι}

theorem generate (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (identity : PqxdhJointIdentity.IdentitySeed)
    (before : RegistrationServerRoleBackend.State) :
    (RegistrationAgreementShared.auxiliary setup.source (RegistrationServerRoleBackend.native setup checks representation identity)
      (.generate .ServerEphemeral)).run before =
    (RegistrationAgreementShared.auxiliary setup.source (RegistrationServerRoleBackend.native setup checks representation identity)
      (.generate .ServerEphemeral)).run RegistrationServerRoleBackend.empty := by
  cases before
  rfl

theorem query_start (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (identity : PqxdhJointIdentity.IdentitySeed)
    (next : Spec.Range (.generate .ServerEphemeral) → OracleComp Spec Value)
    (before : RegistrationServerRoleBackend.State) :
    (simulateQ (RegistrationAgreementShared.auxiliary setup.source
      (RegistrationServerRoleBackend.native setup checks representation identity))
      (Spec.query (.generate .ServerEphemeral) >>= next)).run before =
    (simulateQ (RegistrationAgreementShared.auxiliary setup.source
      (RegistrationServerRoleBackend.native setup checks representation identity))
      (Spec.query (.generate .ServerEphemeral) >>= next)).run RegistrationServerRoleBackend.empty := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [generate setup checks representation identity before]

theorem server_trace (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (identity : PqxdhJointIdentity.IdentitySeed)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (journal : Trace)
    (before : RegistrationServerRoleBackend.State) :
    (simulateQ (RegistrationAgreementShared.auxiliary setup.source
      (RegistrationServerRoleBackend.native setup checks representation identity))
      (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal)).run before =
    (simulateQ (RegistrationAgreementShared.auxiliary setup.source
      (RegistrationServerRoleBackend.native setup checks representation identity))
      (trace (RegistrationAgreementExecutor.server control .Fresh authenticated) journal)).run RegistrationServerRoleBackend.empty := by
  obtain ⟨phase, started⟩ : ∃ phase, agreement.begin_server_agreement control .Fresh authenticated = .ok (.GenerateEphemeral phase) := by
    rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2]
    simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok]
    exact ⟨_, rfl⟩
  unfold RegistrationAgreementExecutor.server
  rw [started]
  simp only [continueWith]
  rw [drive]
  simp only [step, agreement.EphemeralPending.role, continueWith, bind_assoc, pure_bind, trace_query_bind]
  exact query_start setup checks representation identity _ before
end BeaconcryptCore.Computational.RegistrationServerBackendReset

/-- info: 'BeaconcryptCore.Computational.RegistrationServerBackendReset.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerBackendReset.generate

/-- info: 'BeaconcryptCore.Computational.RegistrationServerBackendReset.query_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerBackendReset.query_start

/-- info: 'BeaconcryptCore.Computational.RegistrationServerBackendReset.server_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerBackendReset.server_trace
