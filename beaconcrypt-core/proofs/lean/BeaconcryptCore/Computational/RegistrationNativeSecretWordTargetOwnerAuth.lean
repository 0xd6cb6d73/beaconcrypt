-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor
import BeaconcryptCore.Computational.RegistrationBeaconResponseMetadata

/-! Successful mandatory response authentication retains the caller's packet and control and completes the binding with its actual second hash reply. This receipt introduces no signature-security or cache premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth
open BeaconcryptCore.Refinement.RegistrationResponse
open RegistrationResponseExecutor (begin continueResult)

private theorem packet_field (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse)
    (supported : .ok (.Ok authenticated) ∈ support (begin pending (.Some packet))) :
    authenticated.packet = packet := by
  obtain ⟨hashState, started, _samePending, samePacket, _parts, requested, _bytes⟩ :=
    begin_response_some_exact pending packet
  simp only [begin, started, continueResult, RegistrationAuthenticationExecutor.continueWith,
    requested, mem_support_bind_iff] at supported
  obtain ⟨digest, _queried, supported⟩ := supported
  cases digest with
  | none =>
      simp only [(malformed_and_hash_failure_exact pending hashState).2, mem_support_pure_iff] at supported
      cases supported
  | some digest =>
      obtain ⟨verificationState, resumed, _pendingSame, packetSame, _request, requestRun,
        _properties⟩ := response_hash_some_exact hashState digest
      simp only [resumed, requestRun, mem_support_bind_iff] at supported
      obtain ⟨verified, _verified, supported⟩ := supported
      obtain ⟨adState, gate, _pending, adPacket, _input⟩ := response_mldsa_gate_exact verificationState verified
      rw [gate] at supported
      cases verified with
      | false =>
          simp only [Bool.false_eq_true, ite_false, mem_support_pure_iff] at supported
          cases supported
      | true =>
          obtain ⟨_adRequest, adRequested, _bytes⟩ := response_ad_hash_request_exact adState
          simp only [ite_true, adRequested, mem_support_bind_iff] at supported
          obtain ⟨adDigest, _adQueried, supported⟩ := supported
          cases adDigest with
          | none =>
              rw [response_ad_hash_none_exact] at supported
              simp only [mem_support_pure_iff] at supported
              cases supported
          | some adDigest =>
              obtain ⟨acceptedResult, acceptedRun, _control, acceptedPacket, _properties⟩ :=
                response_ad_hash_some_exact adState adDigest
              simp only [acceptedRun, mem_support_pure_iff, RustM.ok.injEq,
                core.result.Result.Ok.injEq] at supported
              subst authenticated
              exact acceptedPacket.trans (adPacket.trans (packetSame.trans samePacket))

/-- The successful actual controller returns its exact packet/control and a binding completed by a reached AD-hash reply. -/
theorem packet (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse)
    (supported : .ok (.Ok authenticated) ∈ support (begin pending (.Some packet))) :
    ∃ (digest : Std.Array Std.U8 64#usize) (completed : session.CompletedRegistrationBinding),
      pending.binding.complete digest = .ok completed ∧
      authenticated = ⟨pending.control, completed, packet⟩ := by
  have contents := packet_field pending packet authenticated supported
  have retained := RegistrationBeaconResponseMetadata.accepted_metadata pending (.Some packet) authenticated supported
  obtain ⟨control, _pin, _init, digest, completed, _hash, _consistent⟩ := retained
  refine ⟨digest, authenticated.binding, completed, ?_⟩
  cases authenticated with
  | mk actualControl actualBinding actualPacket =>
      change actualControl = pending.control at control
      change actualPacket = packet at contents
      cases control
      cases contents
      rfl
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth.packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth.packet
