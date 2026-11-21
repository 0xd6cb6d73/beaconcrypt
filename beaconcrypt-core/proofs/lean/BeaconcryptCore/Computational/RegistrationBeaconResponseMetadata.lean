-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! Actual response acceptance retains the original control, configured pin and Init digest while completing its binding with the second owned hash reply. The completed binding carries the assembled AD used by the subsequent agreement phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata
open BeaconcryptCore.Refinement.RegistrationResponse

/-- Acceptance keeps the pending public source fields and completes their binding using an actual AD-hash continuation reply. -/
def Retained (pending : registration.BeaconPending) (accepted : registration.AuthenticatedResponse) : Prop :=
  accepted.control = pending.control ∧
  accepted.binding.server_pin = pending.binding.server_pin ∧
  accepted.binding.init_hash = pending.binding.init_hash ∧
  ∃ digest, pending.binding.complete digest = .ok accepted.binding ∧
    accepted.binding.session_transcript_hash = digest ∧
    BeaconcryptCore.Refinement.SessionBinding.registrationConsistent accepted.binding

private theorem completed (stage : registration.BeaconAdHash) (digest : Std.Array U8 64#usize)
    (accepted : registration.AuthenticatedResponse)
    (resumed : stage.resume (.Some digest) = .ok (.Ok accepted)) :
    stage.pending.binding.complete digest = .ok accepted.binding := by
  obtain ⟨binding, ran, _⟩ := BeaconcryptCore.Refinement.SessionBinding.complete_refines stage.pending.binding digest
  simp only [registration.BeaconAdHash.resume, ran, bind_tc_ok, RustM.ok.injEq,
    core.result.Result.Ok.injEq] at resumed
  cases resumed
  exact ran

/-- Both real hash positions and the mandatory Server signature gate preserve the original metadata until the final completed binding is accepted. -/
theorem accepted_metadata (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) (accepted : registration.AuthenticatedResponse)
    (supported : .ok (.Ok accepted) ∈ support (RegistrationResponseExecutor.begin pending packet)) :
    Retained pending accepted := by
  cases packet with
  | none =>
      rw [RegistrationResponseExecutor.begin_malformed] at supported
      simp only [mem_support_pure_iff] at supported
      cases supported
  | some packet =>
      obtain ⟨hashed, started, pendingSame, _packetSame, parts, request, _bytes⟩ := begin_response_some_exact pending packet
      simp only [RegistrationResponseExecutor.begin, started, RegistrationResponseExecutor.continueResult,
        request, RegistrationAuthenticationExecutor.continueWith, mem_support_bind_iff] at supported
      obtain ⟨digest, _queried, supported⟩ := supported
      cases digest with
      | none =>
          rw [(malformed_and_hash_failure_exact pending hashed).2] at supported
          simp only [mem_support_pure_iff] at supported
          cases supported
      | some digest =>
          obtain ⟨verified, resumed, retained, _packetSame, request, requested, _properties⟩ := response_hash_some_exact hashed digest
          simp only [resumed, requested, mem_support_bind_iff] at supported
          obtain ⟨reply, _queried, supported⟩ := supported
          obtain ⟨adState, gate, adPending, _packet, _input⟩ := response_mldsa_gate_exact verified reply
          rw [gate] at supported
          cases reply with
          | false =>
              simp only [Bool.false_eq_true, ite_false, mem_support_pure_iff] at supported
              cases supported
          | true =>
              obtain ⟨adRequest, adRequested, _bytes⟩ := response_ad_hash_request_exact adState
              simp only [ite_true, adRequested, mem_support_bind_iff] at supported
              obtain ⟨adDigest, _adQueried, supported⟩ := supported
              cases adDigest with
              | none =>
                  rw [response_ad_hash_none_exact] at supported
                  simp only [mem_support_pure_iff] at supported
                  cases supported
              | some adDigest =>
                  obtain ⟨acceptedResult, acceptedRun, control, _packet, pin, initHash, hash, consistent⟩ :=
                    response_ad_hash_some_exact adState adDigest
                  simp only [acceptedRun, mem_support_pure_iff, RustM.ok.injEq,
                    core.result.Result.Ok.injEq] at supported
                  subst accepted
                  have same : adState.pending = pending := adPending.trans (retained.trans pendingSame)
                  refine ⟨control.trans (congrArg registration.BeaconPending.control same),
                    pin.trans (congrArg (fun value => value.binding.server_pin) same),
                    initHash.trans (congrArg (fun value => value.binding.init_hash) same), adDigest, ?_, hash, consistent⟩
                  rw [← same]
                  exact completed adState adDigest acceptedResult acceptedRun

/-- Any concrete stateful interpretation retains the same control/pin/Init metadata and exact successful binding completion after both hash callbacks. -/
theorem simulated_metadata {State : Type}
    (implementation : QueryImpl RegistrationAuthenticationExecutor.Spec (StateT State ProbComp))
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (accepted : registration.AuthenticatedResponse) (before after : State)
    (supported : (.ok (.Ok accepted), after) ∈ support
      ((simulateQ implementation (RegistrationResponseExecutor.begin pending packet)).run before)) :
    Retained pending accepted := by
  apply accepted_metadata pending packet accepted
  apply OracleComp.support_simulateQ_run'_subset implementation (RegistrationResponseExecutor.begin pending packet) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.accepted_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.accepted_metadata
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.simulated_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.simulated_metadata
