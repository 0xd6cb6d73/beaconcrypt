-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! A response accepted by the actual extracted controller retains exactly the pending capability supplied before decoding. This transports its source-derived control/pin coherence to the subsequent agreement phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata
open BeaconcryptCore.Refinement.RegistrationResponse

/-- No hash or verification callback can replace the accepted response's original pending binding. -/
theorem accepted_pending (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) (accepted : registration.AuthenticatedResponse)
    (supported : .ok (.Ok accepted) ∈ support (RegistrationResponseExecutor.begin pending packet)) :
    accepted.pending = pending := by
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
          simp only [resumed, requested,
            mem_support_bind_iff] at supported
          obtain ⟨reply, _queried, supported⟩ := supported
          rw [response_mldsa_gate_exact] at supported
          cases reply with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, mem_support_pure_iff] at supported
              cases supported
          | true =>
              simp only [↓reduceIte, mem_support_pure_iff] at supported
              cases supported
              exact retained.trans pendingSame

/-- The same pending capability is retained after any concrete stateful interpretation, including all reached callback effects. -/
theorem simulated_pending {State : Type}
    (implementation : QueryImpl RegistrationAuthenticationExecutor.Spec (StateT State ProbComp))
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (accepted : registration.AuthenticatedResponse) (before after : State)
    (supported : (.ok (.Ok accepted), after) ∈ support
      ((simulateQ implementation (RegistrationResponseExecutor.begin pending packet)).run before)) :
    accepted.pending = pending := by
  apply accepted_pending pending packet accepted
  apply OracleComp.support_simulateQ_run'_subset implementation (RegistrationResponseExecutor.begin pending packet) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.accepted_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.accepted_pending
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.simulated_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata.simulated_pending
