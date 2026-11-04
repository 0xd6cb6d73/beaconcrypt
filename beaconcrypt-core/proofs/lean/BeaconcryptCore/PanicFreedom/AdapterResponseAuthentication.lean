-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterResponseAuthentication
import BeaconcryptCore.PanicFreedom.RegistrationResponse
import BeaconcryptCore.PanicFreedom.RegistrationTrivial

/-! Direct execution safety of the production response driver. Primitive refusal and false verification are ordinary replies; the contracts exclude only represented failure and divergence of the two external calls. -/

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
    exact (RegistrationTrivial.ResponseHash_request_total stage).elim fun request requested =>
      (contracts.hash request).elim fun digest hashed =>
      (RegistrationResponse.ResponseHash_resume_total stage digest).elim fun resumed resumedHash => by
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
          exact (RegistrationTrivial.ResponseMldsaVerification_request_total verification).elim
            fun verificationRequest requestedVerification =>
            (contracts.verify verificationRequest).elim fun verified checked =>
            (RegistrationTrivial.ResponseMldsaVerification_resume_total verification verified).elim
              fun result returned =>
              ⟨result, (Refinement.AdapterResponseAuthentication.replies_forwarded pending packet
                stage request digest verification verificationRequest verified admitted requested
                hashed resumedHash requestedVerification checked).trans returned⟩

end BeaconcryptCore.PanicFreedom.AdapterResponseAuthentication
