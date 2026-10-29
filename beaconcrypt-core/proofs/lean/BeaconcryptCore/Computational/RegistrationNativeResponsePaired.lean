-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCipherBound
import BeaconcryptCore.Computational.RegistrationNativeResponseBound
import BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-! Native paired publication retains the admitted ciphertext and Server identity through either actual known-kernel or hidden-slot installation. The receipts hold over the original free callback program, so arbitrary interpreted primitive replies preserve them. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponsePaired
variable {n : Nat} {Encoded Index Target Value : Type}
variable {source : OracleSpec Index} {target : OracleSpec Target}

theorem simulation_support (implementation : QueryImpl source (OracleComp target))
    (work : OracleComp source Value) (value : Value)
    (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure result => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _reached, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ _, ih reply continued⟩

/-- Successful concrete-kernel insertion returns the same encoded publication. -/
theorem known_encoded (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) (peer : peer.PublishedPeer Encoded)
    (supported : .ok (.Ok peer) ∈ support
      (RegistrationNativePairedServerService.knownInstall (n := n) control published)) :
    peer.encoded = published.encoded := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationNativePairedServerService.knownInstall, prepared] at supported
      cases supported
  | Ok pending =>
      rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared] at supported
      simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨inserted, _reached, returned⟩ := supported
      cases inserted <;> simp [BeaconcryptCore.Refinement.PeerOwnership.publication_finish] at returned
      exact (congrArg (fun value : beaconcrypt_core.peer.PublishedPeer Encoded => value.encoded) returned).trans
        retained.2.2.2.2.1

/-- Successful hidden-slot insertion returns the same encoded publication. -/
theorem hidden_encoded (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded) (peer : peer.PublishedPeer Encoded)
    (supported : .ok (.Ok peer) ∈ support (RegistrationHiddenInstall.install control slot published)) :
    peer.encoded = published.encoded := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationHiddenInstall.install, prepared] at supported
      cases supported
  | Ok pending =>
      rw [RegistrationHiddenInstall.install_native control slot published pending prepared] at supported
      simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨inserted, _reached, returned⟩ := supported
      cases inserted <;> simp [BeaconcryptCore.Refinement.PeerOwnership.publication_finish] at returned
      exact (congrArg (fun value : beaconcrypt_core.peer.PublishedPeer Encoded => value.encoded) returned).trans
        retained.2.2.2.2.1

def EncodedFrom (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (bytes : Encoded) : Prop :=
  RegistrationNativeResponseCiphertext.EncodedFrom encode initial.candidate.kem_ciphertext bytes ∧
    RegistrationNativeResponseIdentity.EncodedFrom encode initial.candidate.server_identity_public_key bytes

/-- The ordinary 108-byte branch retains both public fields through its actual native insertion. -/
theorem known (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (peer : peer.PublishedPeer Encoded)
    (supported : .ok (.Ok peer) ∈ support
      (RegistrationNativePairedServerService.knownStage (n := n) encode control initial output)) :
    EncodedFrom encode initial peer.encoded := by
  simp only [RegistrationNativePairedServerService.knownStage, mem_support_bind_iff] at supported
  obtain ⟨published, reached, continued⟩ := supported
  have after := simulation_support RegistrationHiddenInstall.effectLift _ _ continued
  cases published with
  | fail error | div => cases after
  | ok result => cases result with
    | Err previous => cases after
    | Ok published =>
        have same := known_encoded control published peer after
        have original := simulation_support RegistrationHiddenInstall.publicationLift _ _ reached
        rw [same]
        exact ⟨RegistrationNativeResponseCipherBound.program_ciphertext encode initial output published original,
          RegistrationNativeResponseBound.program_identity encode initial output published original⟩

/-- The public material44 branch retains both public fields through its actual hidden installation. -/
theorem hidden (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) (peer : peer.PublishedPeer Encoded)
    (supported : .ok (.Ok peer) ∈ support
      (RegistrationNativePairedServerService.hiddenStage encode control initial reference)) :
    EncodedFrom encode initial peer.encoded := by
  simp only [RegistrationNativePairedServerService.hiddenStage, mem_support_bind_iff] at supported
  obtain ⟨published, reached, continued⟩ := supported
  have after := simulation_support RegistrationHiddenInstall.effectLift _ _ continued
  cases published with
  | fail error | div => cases after
  | ok result => cases result with
    | Err previous => cases after
    | Ok published =>
        have same := hidden_encoded control reference.slot published peer after
        have original := simulation_support RegistrationHiddenInstall.publicationLift _ _ reached
        rw [same]
        exact ⟨RegistrationNativeResponseCipherBound.thin_ciphertext encode initial reference.material published original,
          RegistrationNativeResponseBound.thin_identity encode initial reference.material published original⟩

/-- Arbitrary actual paired choices preserve the same admitted public response fields. -/
theorem branch (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) (peer : peer.PublishedPeer Encoded)
    (supported : .ok (.Ok peer) ∈ support
      (RegistrationNativePairedServerService.publicBranch encode control initial choice)) :
    EncodedFrom encode initial peer.encoded := by
  cases choice with
  | known output => exact known encode control initial output peer supported
  | hidden reference => exact hidden encode control initial reference peer supported

end BeaconcryptCore.Computational.RegistrationNativeResponsePaired

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.simulation_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.simulation_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.known_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.known_encoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.hidden_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.hidden_encoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponsePaired.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponsePaired.branch
