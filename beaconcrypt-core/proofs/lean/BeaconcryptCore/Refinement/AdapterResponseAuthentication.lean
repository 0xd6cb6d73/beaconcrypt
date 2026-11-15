-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterAuthenticationExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationResponse

/-! Direct deterministic execution of the generated response driver, including the second transcript-AD hash after pinned Server verification. External operations may fail or diverge; successful execution retains their actual replies. Native conformance and cryptographic security remain separate. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterResponseAuthentication
open RegistrationResponse
variable [operations : beaconcrypt.auth.Operations]

/-- The final driver tail issues the exact core-selected AD request. -/
def completeAd (stage : registration.BeaconAdHash) := do
  let request ← stage.request
  let digest ← beaconcrypt.auth.execute_hash request
  stage.resume digest

/-- All actual replies are forwarded to their matching continuation, in source order. -/
theorem replies_forwarded (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (hashStage : registration.ResponseHash) (hashRequest : registration.HashRequest)
    (digest : core.option.Option (Array Std.U8 64#usize))
    (verificationStage : registration.ResponseMldsaVerification)
    (verificationRequest : registration.MldsaVerificationRequest) (verified : Bool)
    (adStage : registration.BeaconAdHash) (adRequest : registration.HashRequest)
    (adDigest : core.option.Option (Array Std.U8 64#usize))
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok hashStage))
    (requestedHash : hashStage.request = ok hashRequest)
    (hashed : operations.hash hashRequest = ok digest)
    (resumedHash : hashStage.resume digest = ok (.Ok verificationStage))
    (requestedVerification : verificationStage.request = ok verificationRequest)
    (checked : operations.verify verificationRequest = ok verified)
    (resumedVerification : verificationStage.resume verified = ok (.Ok adStage))
    (requestedAd : adStage.request = ok adRequest)
    (hashedAd : operations.hash adRequest = ok adDigest) :
    beaconcrypt.auth.authenticate_response pending packet = adStage.resume adDigest := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requestedHash, beaconcrypt.auth.execute_hash, hashed, resumedHash,
    requestedVerification, beaconcrypt.auth.verify_requested, checked,
    resumedVerification, requestedAd, hashedAd, bind_tc_ok]

/-- Admission rejection does not call either primitive. -/
theorem admission_rejected (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) (aborted : pqxdh.BeaconAborted)
    (admitted : registration.begin_response_authentication pending packet = ok (.Err aborted)) :
    beaconcrypt.auth.authenticate_response pending packet = ok (.Err aborted) := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from, bind_tc_ok]

theorem missing_packet_rejected (pending : registration.BeaconPending) :
    beaconcrypt.auth.authenticate_response pending .None = ok (.Err (abortedState pending)) :=
  admission_rejected pending .None _ rfl

/-- First-hash refusal aborts before verification or the AD hash. -/
theorem hash_rejected (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (stage : registration.ResponseHash) (request : registration.HashRequest)
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok stage))
    (requested : stage.request = ok request) (hashed : operations.hash request = ok .None) :
    beaconcrypt.auth.authenticate_response pending packet = ok (.Err (abortedState stage.pending)) := by
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requested, beaconcrypt.auth.execute_hash, hashed,
    (malformed_and_hash_failure_exact pending stage).2,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from, bind_tc_ok]

/-- False verification aborts before the final hash. -/
theorem verification_result_exact (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket)
    (hashStage : registration.ResponseHash) (hashRequest : registration.HashRequest)
    (digest : core.option.Option (Array Std.U8 64#usize))
    (stage : registration.ResponseMldsaVerification) (request : registration.MldsaVerificationRequest)
    (admitted : registration.begin_response_authentication pending packet = ok (.Ok hashStage))
    (requestedHash : hashStage.request = ok hashRequest) (hashed : operations.hash hashRequest = ok digest)
    (resumedHash : hashStage.resume digest = ok (.Ok stage))
    (requestedVerification : stage.request = ok request) (checked : operations.verify request = ok false) :
    beaconcrypt.auth.authenticate_response pending packet = ok (.Err (abortedState stage.pending)) := by
  simp [beaconcrypt.auth.authenticate_response, admitted, requestedHash,
    beaconcrypt.auth.execute_hash, hashed, resumedHash, requestedVerification,
    beaconcrypt.auth.verify_requested, checked, registration.ResponseMldsaVerification.resume,
    registration.BeaconPending.abort, pqxdh.beacon_abort_init, abortedState,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from]

/-- A successful final tail contains an actual Some digest and the completed binding's exact provenance. -/
theorem completeAd_success (stage : registration.BeaconAdHash)
    (accepted : registration.AuthenticatedResponse)
    (success : completeAd stage = ok (.Ok accepted)) :
    accepted.control = stage.pending.control ∧ accepted.packet = stage.packet ∧
      accepted.binding.server_pin = stage.pending.binding.server_pin ∧
      accepted.binding.init_hash = stage.pending.binding.init_hash ∧
      ∃ (request : registration.HashRequest) (digest : Array Std.U8 64#usize),
        stage.request = ok request ∧ operations.hash request = ok (.Some digest) ∧
        RegistrationInputs.hashBytes request = PqxdhRefinement.absBytes stage.input ∧
        accepted.binding.session_transcript_hash = digest ∧
        SessionBinding.registrationConsistent accepted.binding := by
  obtain ⟨request, requested, input⟩ := response_ad_hash_request_exact stage
  simp only [completeAd, requested, beaconcrypt.auth.execute_hash, bind_tc_ok] at success
  cases hashed : operations.hash request <;>
    simp only [hashed, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
  case ok digest =>
    cases digest with
    | none => simp [response_ad_hash_none_exact] at success
    | some digest =>
      obtain ⟨result, ran, control, packet, pin, initHash, retained, consistent⟩ :=
        response_ad_hash_some_exact stage digest
      rw [ran] at success
      cases success
      exact ⟨control, packet, pin, initHash, request, digest, requested, hashed,
        input, retained, consistent⟩

/-- Success exposes the actual authenticated transcript and selected AD continuation; no primitive success is assumed. -/
theorem successful_response_trace (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (accepted : registration.AuthenticatedResponse)
    (success : beaconcrypt.auth.authenticate_response pending (.Some packet) = ok (.Ok accepted)) :
    ∃ (hashRequest : registration.HashRequest) (digest : Array Std.U8 64#usize)
      (request : registration.MldsaVerificationRequest) (adStage : registration.BeaconAdHash),
      operations.hash hashRequest = ok (.Some digest) ∧ operations.verify request = ok true ∧
      request.public_key = pending.binding.server_pin.public_key ∧ request.signature = packet.signature ∧
      request.context = authentication.SIGNING_CONTEXT ∧
      PqxdhRefinement.absBytes request.input =
        Pqxdh.TranscriptAuth.signatureInput .server (PqxdhRefinement.absBytes digest) ∧
      RegistrationInputs.hashBytes hashRequest =
        Pqxdh.TranscriptAuth.responseTranscript (PqxdhRefinement.absBytes pending.binding.init_hash)
          (TranscriptAuthRefinement.absResponse (responseFields packet)) ∧
      adStage.pending = pending ∧ adStage.packet = packet ∧
      PqxdhRefinement.absBytes adStage.input =
        RegistrationAd.preimage pending.binding (RegistrationAd.responseView packet.public) ∧
      completeAd adStage = ok (.Ok accepted) := by
  obtain ⟨stage, admitted, stagePending, stagePacket, parts, requestedHash, hashBytes⟩ :=
    begin_response_some_exact pending packet
  simp only [beaconcrypt.auth.authenticate_response, admitted,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    requestedHash, beaconcrypt.auth.execute_hash, bind_tc_ok] at success
  cases hashed : operations.hash (.Triple parts) <;>
    simp only [hashed, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
  case ok digest =>
    cases digest with
    | none =>
      simp [(malformed_and_hash_failure_exact pending stage).2,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
        core.convert.From.Blanket.from] at success
    | some digest =>
      obtain ⟨verification, resumedHash, verificationPending, verificationPacket,
        request, requestedVerification, requestFields⟩ := response_hash_some_exact stage digest
      simp only [resumedHash, requestedVerification, beaconcrypt.auth.verify_requested, bind_tc_ok] at success
      cases checked : operations.verify request <;>
        simp only [checked, bind_tc_ok, bind_tc_fail, bind_tc_div, reduceCtorEq] at success
      case ok verified =>
        obtain ⟨adStage, gate, adPending, adPacket, adInput⟩ := response_mldsa_gate_exact verification verified
        cases verified with
        | false =>
          simp [gate, core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
            core.convert.From.Blanket.from] at success
        | true =>
          simp only [gate] at success
          have pendingEq := adPending.trans (verificationPending.trans stagePending)
          have packetEq := adPacket.trans (verificationPacket.trans stagePacket)
          refine ⟨.Triple parts, digest, request, adStage, hashed, checked, ?_, ?_,
            requestFields.2.2.1, requestFields.2.2.2.2, hashBytes, pendingEq, packetEq, ?_, success⟩
          · simpa only [stagePending] using requestFields.1
          · simpa only [stagePacket] using requestFields.2.1
          · simpa only [verificationPending, verificationPacket, stagePending, stagePacket] using adInput

/-- The consumed pending control, exact pin, retained request hash and packet survive authentication. -/
theorem successful_response_retains_pending_packet (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (accepted : registration.AuthenticatedResponse)
    (success : beaconcrypt.auth.authenticate_response pending (.Some packet) = ok (.Ok accepted)) :
    accepted.control = pending.control ∧ accepted.packet = packet ∧
      accepted.binding.server_pin = pending.binding.server_pin ∧
      accepted.binding.init_hash = pending.binding.init_hash := by
  obtain ⟨_, _, _, stage, _, _, _, _, _, _, _, pendingEq, packetEq, _, ran⟩ :=
    successful_response_trace pending packet accepted success
  obtain ⟨control, packet, pin, initHash, _⟩ := completeAd_success stage accepted ran
  simpa only [pendingEq, packetEq] using And.intro control (And.intro packet (And.intro pin initHash))

/-- Successful execution verifies the pinned Server signature and retains the actual AD-hash reply. -/
theorem successful_response_was_verified (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) (accepted : registration.AuthenticatedResponse)
    (success : beaconcrypt.auth.authenticate_response pending (.Some packet) = ok (.Ok accepted)) :
    ∃ (hashRequest : registration.HashRequest) (digest : Array Std.U8 64#usize)
      (request : registration.MldsaVerificationRequest) (adRequest : registration.HashRequest)
      (adDigest : Array Std.U8 64#usize),
      operations.hash hashRequest = ok (.Some digest) ∧ operations.verify request = ok true ∧
      request.public_key = pending.binding.server_pin.public_key ∧ request.signature = packet.signature ∧
      request.context = authentication.SIGNING_CONTEXT ∧
      PqxdhRefinement.absBytes request.input =
        Pqxdh.TranscriptAuth.signatureInput .server (PqxdhRefinement.absBytes digest) ∧
      operations.hash adRequest = ok (.Some adDigest) ∧
      RegistrationInputs.hashBytes adRequest =
        RegistrationAd.preimage pending.binding (RegistrationAd.responseView packet.public) ∧
      accepted.binding.session_transcript_hash = adDigest ∧
      SessionBinding.registrationConsistent accepted.binding := by
  obtain ⟨hashRequest, digest, request, stage, hashed, checked, pin, signature, context,
    signingInput, _, _, _, input, ran⟩ := successful_response_trace pending packet accepted success
  obtain ⟨_, _, _, _, adRequest, adDigest, _, adHashed, bytes, retained, consistent⟩ :=
    completeAd_success stage accepted ran
  exact ⟨hashRequest, digest, request, adRequest, adDigest, hashed, checked, pin, signature,
    context, signingInput, adHashed, bytes.trans input, retained, consistent⟩

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

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.completeAd_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.completeAd_success

/-- info: 'BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterResponseAuthentication.successful_response_trace

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
