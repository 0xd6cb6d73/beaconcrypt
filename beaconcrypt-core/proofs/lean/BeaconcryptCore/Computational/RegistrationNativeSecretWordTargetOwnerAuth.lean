-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! A successful original mandatory response-authentication controller returns precisely its supplied pending owner and packet, for every possible hash and verification reply. This receipt introduces no signature-security assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth
open BeaconcryptCore.Refinement.RegistrationResponse
open RegistrationResponseExecutor (begin continueResult)

/-- The actual original response controller preserves the exact caller packet on successful mandatory authentication. -/
theorem packet (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse)
    (supported : .ok (.Ok authenticated) ∈ support (begin pending (.Some packet))) :
    authenticated = ⟨pending, packet⟩ := by
  obtain ⟨hashState, started, samePending, samePacket, parts, requested, _bytes⟩ :=
    begin_response_some_exact pending packet
  simp only [begin, started, continueResult, RegistrationAuthenticationExecutor.continueWith,
    requested, mem_support_bind_iff] at supported
  obtain ⟨digest, _queried, supported⟩ := supported
  cases digest with
  | none =>
      simp only [(malformed_and_hash_failure_exact pending hashState).2, mem_support_pure_iff] at supported
      cases supported
  | some digest =>
      obtain ⟨verificationState, resumed, pendingSame, packetSame, request, requestRun,
        _key, _signature, _context, _contextBytes, _inputBytes⟩ := response_hash_some_exact hashState digest
      simp only [resumed, requestRun, mem_support_bind_iff] at supported
      obtain ⟨verified, _verified, supported⟩ := supported
      rw [response_mldsa_gate_exact] at supported
      cases verified with
      | false => simp only [Bool.false_eq_true, ite_false, mem_support_pure_iff] at supported; cases supported
      | true =>
          simp only [ite_true, mem_support_pure_iff, RustM.ok.injEq, core.result.Result.Ok.injEq] at supported
          simpa only [pendingSame, packetSame, samePending, samePacket] using supported
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth.packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth.packet
