-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor
/-! The actual response-authentication free tree always returns a normal Rust result. Every rejected packet, missing hash and failed verification yields the exact pending abort control; every accepted result retains the original pending owner and supplied packet. These are derived source-shape facts for every reply, not authentication or success assumptions. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationResponseNormal
open RegistrationResponseExecutor
open BeaconcryptCore.Refinement.RegistrationResponse

def Shape (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (outcome : RustM ResponseResult) : Prop :=
  outcome = .ok (.Err (abortedState pending)) ∨
    ∃ supplied, packet = .Some supplied ∧ outcome = .ok (.Ok ⟨pending, supplied⟩)

theorem aborted_exact (pending : registration.BeaconPending) : pending.aborted_state = .ok (abortedState pending) := rfl

theorem begin_shape (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (outcome : RustM ResponseResult) (supported : outcome ∈ support (begin pending packet)) : Shape pending packet outcome := by
  cases packet with
  | none =>
      rw [begin_malformed] at supported
      exact .inl (by simpa only [support_pure, Set.mem_singleton_iff] using supported)
  | some packet =>
      obtain ⟨hashState, started, samePending, samePacket, parts, requested, _bytes⟩ := begin_response_some_exact pending packet
      simp only [begin, started, continueResult, RegistrationAuthenticationExecutor.continueWith, requested, mem_support_bind_iff] at supported
      obtain ⟨digest, _, continued⟩ := supported
      cases digest with
      | none =>
          rw [(malformed_and_hash_failure_exact pending hashState).2] at continued
          simp only [support_pure, Set.mem_singleton_iff, samePending] at continued
          exact .inl continued
      | some digest =>
          obtain ⟨verificationState, resumed, pendingSame, packetSame, request, requestRun, _key, _signature, _context, _contextBytes, _inputBytes⟩ := response_hash_some_exact hashState digest
          simp only [resumed, requestRun, mem_support_bind_iff] at continued
          obtain ⟨verified, _, returned⟩ := continued
          rw [response_mldsa_gate_exact] at returned
          cases verified with
          | false =>
              simp only [Bool.false_eq_true, ite_false, support_pure, Set.mem_singleton_iff, pendingSame, samePending] at returned
              exact .inl returned
          | true =>
              simp only [ite_true, support_pure, Set.mem_singleton_iff, pendingSame, packetSame, samePending, samePacket] at returned
              exact .inr ⟨packet, rfl, returned⟩

theorem normal (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (outcome : RustM ResponseResult) (supported : outcome ∈ support (begin pending packet)) : ∃ result, outcome = .ok result := by
  rcases begin_shape pending packet outcome supported with rejected | ⟨supplied, _, accepted⟩
  · exact ⟨_, rejected⟩
  · exact ⟨_, accepted⟩

end BeaconcryptCore.Computational.RegistrationResponseNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseNormal.aborted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseNormal.aborted_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseNormal.begin_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseNormal.begin_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationResponseNormal.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationResponseNormal.normal
