-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterResponseAuthentication
import BeaconcryptCore.PanicFreedom.RegistrationResponse

/-! Direct execution safety of the production response driver. Primitive refusal and false verification are ordinary replies; the contracts exclude only represented failure and divergence of the two hash calls and one verification call. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication

variable [operations : beaconcrypt.auth.Operations]

structure Contracts : Prop where
  hash : ∀ request, ∃ result, operations.hash request = ok result
  verify : ∀ request, ∃ result, operations.verify request = ok result

theorem authenticate_response_total (contracts : Contracts)
    (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) :
    ∃ result, beaconcrypt.auth.authenticate_response pending packet = ok result := by
  obtain ⟨admission, admitted⟩ := RegistrationResponse.begin_response_authentication_total pending packet
  cases admission with
  | Err aborted =>
    exact ⟨_, Refinement.AdapterResponseAuthentication.admission_rejected pending packet aborted admitted⟩
  | Ok stage =>
    obtain ⟨parts, requested, _⟩ := Refinement.RegistrationResponse.response_hash_request_exact stage
    let request : registration.HashRequest := .Triple parts
    obtain ⟨digest, hashed⟩ := contracts.hash request
    simp only [request] at hashed
    obtain ⟨resumed, resumedHash⟩ := RegistrationResponse.ResponseHash_resume_total stage digest
    cases resumed with
    | Err aborted =>
      refine ⟨.Err aborted, ?_⟩
      simp only [beaconcrypt.auth.authenticate_response, admitted,
        core.result.Result.Insts.CoreOpsTry_traitTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
        requested, beaconcrypt.auth.execute_hash, hashed, resumedHash,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from, bind_tc_ok]
    | Ok verification =>
      obtain ⟨verificationRequest, requestedVerification⟩ :
          ∃ result, verification.request = ok result := ⟨_, rfl⟩
      obtain ⟨verified, checked⟩ := contracts.verify verificationRequest
      obtain ⟨adStage, resumedVerification, _, _, _⟩ :=
        Refinement.RegistrationResponse.response_mldsa_gate_exact verification verified
      cases verified with
      | false =>
        exact ⟨_, Refinement.AdapterResponseAuthentication.verification_result_exact pending packet
          stage request digest verification verificationRequest admitted requested hashed resumedHash
          requestedVerification checked⟩
      | true =>
        obtain ⟨adRequest, requestedAd, _⟩ :=
          Refinement.RegistrationResponse.response_ad_hash_request_exact adStage
        obtain ⟨adDigest, hashedAd⟩ := contracts.hash adRequest
        obtain ⟨result, returned⟩ : ∃ result, adStage.resume adDigest = ok result := by
          cases adDigest with
          | none => exact ⟨_, Refinement.RegistrationResponse.response_ad_hash_none_exact adStage⟩
          | some value =>
            obtain ⟨result, returned, _⟩ :=
              Refinement.RegistrationResponse.response_ad_hash_some_exact adStage value
            exact ⟨_, returned⟩
        exact ⟨result, (Refinement.AdapterResponseAuthentication.replies_forwarded pending packet
          stage request digest verification verificationRequest true adStage adRequest adDigest
          admitted requested hashed resumedHash requestedVerification checked resumedVerification
          requestedAd hashedAd).trans returned⟩

end BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication
