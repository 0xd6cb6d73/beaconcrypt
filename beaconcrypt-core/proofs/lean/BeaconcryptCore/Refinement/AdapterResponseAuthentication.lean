-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterAuthenticationExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationResponse

/-!
The selected production Rust response-authentication driver is translated by Charon and Aeneas. These deterministic statements quantify over its explicit primitive implementations and connect the generated function to the maintained core continuations. They do not establish native primitive conformance, mutable oracle histories, or a probabilistic deployment simulation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterResponseAuthentication

variable [operations : beaconcrypt.auth.Operations]

/-- Every reached core request receives its actual primitive reply, and the generated driver returns the exact verification continuation. -/
theorem replies_forwarded
    (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (hashStage : registration.ResponseHash)
    (hashRequest : registration.HashRequest)
    (digest : core.option.Option (Array Std.U8 64#usize))
    (verificationStage : registration.ResponseMldsaVerification)
    (verificationRequest : registration.MldsaVerificationRequest)
    (verified : Bool)
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok hashStage))
    (requestedHash : registration.ResponseHash.request hashStage = ok hashRequest)
    (hashed : operations.hash hashRequest = ok digest)
    (resumedHash : registration.ResponseHash.resume hashStage digest = ok (.Ok verificationStage))
    (requestedVerification : registration.ResponseMldsaVerification.request verificationStage =
      ok verificationRequest)
    (checked : operations.verify verificationRequest = ok verified) :
    beaconcrypt.auth.authenticate_response pending packet =
      registration.ResponseMldsaVerification.resume verificationStage verified := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requestedHash, beaconcrypt.auth.execute_hash, hashed, resumedHash,
    requestedVerification, beaconcrypt.auth.verify_requested, checked, bind_tc_ok]

/-- Rejected admission returns the exact abort value independently of either primitive implementation. -/
theorem admission_rejected
    (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (aborted : pqxdh.BeaconAborted)
    (admitted : registration.begin_response_authentication pending packet = ok (.Err aborted)) :
    beaconcrypt.auth.authenticate_response pending packet = ok (.Err aborted) := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from, bind_tc_ok]

/-- Missing decoded response data returns the original pending state's precise terminal abort identifier. -/
theorem missing_packet_rejected (pending : registration.BeaconPending) :
    beaconcrypt.auth.authenticate_response pending .None =
      ok (.Err { server_key_id := pending.control.expected_server_binding.identity_key_id }) := by
  exact admission_rejected pending .None _ rfl

/-- A failed hash result returns the reached pending state's exact abort identifier before verification. -/
theorem hash_rejected
    (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (stage : registration.ResponseHash)
    (request : registration.HashRequest)
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok stage))
    (requested : registration.ResponseHash.request stage = ok request)
    (hashed : operations.hash request = ok .None) :
    beaconcrypt.auth.authenticate_response pending packet =
      ok (.Err (BeaconcryptCore.Refinement.RegistrationResponse.abortedState stage.pending)) := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requested, beaconcrypt.auth.execute_hash, hashed,
    (BeaconcryptCore.Refinement.RegistrationResponse.malformed_and_hash_failure_exact pending stage).2,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from, bind_tc_ok]

/-- The actual verification reply determines the exact returned authenticated fields or abort identifier. -/
theorem verification_result_exact
    (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (hashStage : registration.ResponseHash)
    (hashRequest : registration.HashRequest)
    (digest : core.option.Option (Array Std.U8 64#usize))
    (verificationStage : registration.ResponseMldsaVerification)
    (verificationRequest : registration.MldsaVerificationRequest)
    (verified : Bool)
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok hashStage))
    (requestedHash : registration.ResponseHash.request hashStage = ok hashRequest)
    (hashed : operations.hash hashRequest = ok digest)
    (resumedHash : registration.ResponseHash.resume hashStage digest = ok (.Ok verificationStage))
    (requestedVerification : registration.ResponseMldsaVerification.request verificationStage =
      ok verificationRequest)
    (checked : operations.verify verificationRequest = ok verified) :
    beaconcrypt.auth.authenticate_response pending packet =
      if verified then ok (.Ok { pending := verificationStage.pending, packet := verificationStage.packet })
      else ok (.Err (BeaconcryptCore.Refinement.RegistrationResponse.abortedState verificationStage.pending)) := by
  simpa only [BeaconcryptCore.Refinement.RegistrationResponse.response_mldsa_gate_exact] using
    replies_forwarded pending packet hashStage hashRequest digest verificationStage verificationRequest
      verified admitted requestedHash hashed resumedHash requestedVerification checked

/-- Every successful generated-driver result retains the original pending state and decoded packet, for arbitrary primitive implementations. -/
theorem successful_response_retains_pending_packet
    (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse)
    (success : beaconcrypt.auth.authenticate_response pending (.Some packet) =
      ok (.Ok authenticated)) :
    authenticated.pending = pending ∧ authenticated.packet = packet := by
  obtain ⟨stage, admitted, stagePending, stagePacket, parts, requestedHash, _⟩ :=
    BeaconcryptCore.Refinement.RegistrationResponse.begin_response_some_exact pending packet
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requestedHash, beaconcrypt.auth.execute_hash, bind_tc_ok] at success
  cases hashed : operations.hash (.Triple parts) <;>
    simp only [hashed, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
  case ok digest =>
    cases digest with
    | some digest =>
      obtain ⟨verificationStage, resumedHash, verificationPending, verificationPacket,
        request, requestedVerification, _⟩ :=
        BeaconcryptCore.Refinement.RegistrationResponse.response_hash_some_exact stage digest
      simp only [resumedHash, requestedVerification, beaconcrypt.auth.verify_requested,
        bind_tc_ok] at success
      cases checked : operations.verify request <;>
        simp only [checked, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
      case ok verified =>
        cases verified <;>
          simp [BeaconcryptCore.Refinement.RegistrationResponse.response_mldsa_gate_exact] at success
        simpa only [← success] using
          And.intro (verificationPending.trans stagePending) (verificationPacket.trans stagePacket)
    | none =>
      simp only [(BeaconcryptCore.Refinement.RegistrationResponse.malformed_and_hash_failure_exact
        pending stage).2,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from, bind_tc_ok] at success
      cases success


/-- Success has actual hash and true-verification replies on the pinned key, supplied signature, exact context and role-separated transcript digest. -/
theorem successful_response_was_verified
    (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse)
    (success : beaconcrypt.auth.authenticate_response pending (.Some packet) =
      ok (.Ok authenticated)) :
    ∃ (hashRequest : registration.HashRequest) (digest : Array Std.U8 64#usize)
      (request : registration.MldsaVerificationRequest),
      operations.hash hashRequest = ok (.Some digest) ∧
      operations.verify request = ok true ∧
      request.public_key = pending.binding.server_pin.public_key ∧
      request.signature = packet.signature ∧
      request.context = authentication.SIGNING_CONTEXT ∧
      PqxdhRefinement.absBytes request.input =
        Pqxdh.TranscriptAuth.signatureInput .server (PqxdhRefinement.absBytes digest) ∧
      RegistrationInputs.hashBytes hashRequest =
        Pqxdh.TranscriptAuth.responseTranscript (PqxdhRefinement.absBytes pending.binding.init_hash)
          (TranscriptAuthRefinement.absResponse (RegistrationResponse.responseFields packet)) := by
  obtain ⟨stage, admitted, stagePending, stagePacket, parts, requestedHash, hashBytes⟩ :=
    RegistrationResponse.begin_response_some_exact pending packet
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requestedHash, beaconcrypt.auth.execute_hash, bind_tc_ok] at success
  cases hashed : operations.hash (.Triple parts) <;>
    simp only [hashed, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
  case ok digest =>
    cases digest with
    | some digest =>
      obtain ⟨verificationStage, resumedHash, _, _, request, requestedVerification, requestFields⟩ :=
        RegistrationResponse.response_hash_some_exact stage digest
      simp only [resumedHash, requestedVerification, beaconcrypt.auth.verify_requested,
        bind_tc_ok] at success
      cases checked : operations.verify request <;>
        simp only [checked, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
      case ok verified =>
        cases verified <;>
          simp [RegistrationResponse.response_mldsa_gate_exact] at success
        refine ⟨.Triple parts, digest, request, hashed, checked, ?_, ?_,
          requestFields.2.2.1, requestFields.2.2.2.2, hashBytes⟩
        · simpa only [stagePending] using requestFields.1
        · simpa only [stagePacket] using requestFields.2.1
    | none =>
      simp only [(RegistrationResponse.malformed_and_hash_failure_exact pending stage).2,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from, bind_tc_ok] at success
      cases success

end BeaconcryptCore.Refinement.AdapterResponseAuthentication

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.replies_forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.replies_forwarded

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.admission_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.admission_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.missing_packet_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.missing_packet_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.hash_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.hash_rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.verification_result_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.verification_result_exact

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_retains_pending_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_retains_pending_packet

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_was_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_was_verified
