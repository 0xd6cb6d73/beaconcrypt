-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningHistory
import BeaconcryptCore.Refinement.RegistrationAuthentication
import BeaconcryptCore.Refinement.RegistrationResponse
import BeaconcryptCore.Refinement.RegistrationPublication

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Computational
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationSigningTrace

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigningDispatch

/-- The logged call has the actual selected owner, role, context, hash-derived message and reply. -/
def ObservationMatches (hash : HashOracle) (sign : SignOracle)
    (command : Command) (event : Observation) : Prop :=
  event.publicKey = command.publicKey ∧ event.payload = command.payload ∧
    ∃ request : registration.MldsaSigningRequest,
      request.public_key = event.publicKey ∧ request.role = command.role ∧
      absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes request.input = event.payload.message (hashBytesOracle hash) ∧
      event.reply = replyBytes (sign request)

/-- Server dispatch uses the same exact query and unconditional chronological logging rule. -/
theorem dispatch_server_exact {Encoded : Type} (hash : HashOracle) (sign : SignOracle)
    (hashing : registration.ServerResponseHash) (encoded : core.option.Option Encoded) :
    ∃ result event, dispatch hash sign (.server hashing) encoded = ok result ∧
      result.event = some event ∧ ObservationMatches hash sign (.server hashing) event := by
  obtain ⟨pending, pendingRun, candidate, binding, kernel, ciphertext, message, requestRun⟩ :=
    RegistrationPublication.server_response_hash_refines hashing
      (hash (Command.server hashing).payload.transcript)
  obtain ⟨result, resultRun, event⟩ :=
    submit_server_logs pending (Command.server hashing).payload sign encoded
  refine ⟨result, ⟨pending.binding.server_pin.public_key, (Command.server hashing).payload,
    replyBytes (sign (serverRequest pending))⟩, ?_, event, ?_⟩
  · obtain ⟨hashRequest, hashRun, hashPreimage⟩ := command_request_exact (.server hashing)
    simp only [Command.request] at hashRun
    simp only [dispatch, hashRun, bind_tc_ok, hashPreimage, pendingRun]
    exact resultRun
  · exact ⟨congrArg (fun value : session.CompletedRegistrationBinding => value.server_pin.public_key) binding,
      rfl, serverRequest pending, rfl, rfl, TranscriptAuthInputsRefinement.signing_context_abs,
      message, rfl⟩

theorem dispatch_exact {Encoded : Type} (hash : HashOracle) (sign : SignOracle)
    (command : Command) (encoded : core.option.Option Encoded) :
    ∃ result event, dispatch hash sign command encoded = ok result ∧
      result.event = some event ∧ ObservationMatches hash sign command event :=
  match command with
  | .server hashing => dispatch_server_exact hash sign hashing encoded

/-- Every finite interleaving of actual sign/publication phases admits a complete chronological execution. -/
theorem execution_exists {Encoded : Type} (hash : HashOracle) (sign : SignOracle)
    (commands : List (Command × core.option.Option Encoded)) :
    ∃ events outcomes, RegistrationSigningHistory.Executes hash sign commands events outcomes := by
  induction commands with
  | nil => exact ⟨[], [], .nil⟩
  | cons command commands ih =>
    obtain ⟨result, event, run, logged, _meaning⟩ := dispatch_exact hash sign command.1 command.2
    obtain ⟨events, outcomes, rest⟩ := ih
    exact ⟨event :: events, result.outcome :: outcomes, .cons run logged rest⟩

/-- Every chronological execution matches the exact source query at each position. -/
theorem execution_matches {Encoded : Type} {hash : HashOracle} {sign : SignOracle}
    {commands : List (Command × core.option.Option Encoded)} {events : List Observation}
    {outcomes : List (Publication Encoded)}
    (execution : RegistrationSigningHistory.Executes hash sign commands events outcomes) :
    List.Forall₂ (fun command event => ObservationMatches hash sign command.1 event) commands events := by
  induction execution with
  | nil => exact .nil
  | @cons command encoded result event commands events outcomes run logged rest ih =>
    obtain ⟨expected, expectedEvent, expectedRun, expectedLogged, meaning⟩ :=
      dispatch_exact hash sign command encoded
    have sameResult : expected = result := by simpa using expectedRun.symm.trans run
    have sameEvent : expectedEvent = event := by simpa [sameResult, logged] using expectedLogged.symm
    exact .cons (sameEvent ▸ meaning) ih

private theorem request_preimage_exact (command : Command) (request : registration.HashRequest)
    (run : command.request = ok request) : hashBytes request = command.payload.transcript :=
  (command_request_exact command).elim fun actual facts =>
    (show actual = request by simpa using facts.1.symm.trans run) ▸ facts.2

/-- A source-produced server command signs the actual sealed ciphertext, assigned ID and retained request digest. -/
theorem server_source_payload_exact (before : registration.ServerRecordWrite)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, before.resume ciphertext = ok result ∧
      match result with
      | .Err previous => previous = before.state.candidate.previous_state
      | .Ok hashing => hashing.candidate = before.state.candidate ∧ hashing.binding = before.state.binding ∧
          ciphertext = .Some hashing.ciphertext ∧
          (Command.server hashing).payload = MldsaTranscriptAuth.responsePayload
            (absBytes before.state.binding.init_hash)
            (TranscriptAuthRefinement.absResponse
              (RegistrationPublication.serverResponseFields before.state.candidate hashing.ciphertext)) := by
  obtain ⟨result, run, meaning⟩ :=
    RegistrationPublication.server_seal_preimage_refines before ciphertext
  cases result with
  | Err previous => exact ⟨_, run, meaning⟩
  | Ok hashing =>
    rcases meaning with ⟨candidate, binding, _kernel, body, request, requestRun, bytes⟩
    exact ⟨.Ok hashing, run, candidate, binding, body,
      congrArg (MldsaTranscriptAuth.Payload.mk .server)
        ((request_preimage_exact (.server hashing) request requestRun).symm.trans bytes)⟩

/-- A typed actual verification request with the proved context/message is exactly the old trial acceptance predicate. -/
theorem verification_trial_exact (hash : HashOracle) (verify : MldsaTranscriptAuth.Verify)
    (request : registration.MldsaVerificationRequest) (payload : MldsaTranscriptAuth.Payload)
    (protectedKey : Bool) (events : List Observation)
    (context : absBytes request.context = Pqxdh.TranscriptAuth.signingContext)
    (input : absBytes request.input = payload.message (hashBytesOracle hash)) :
    MldsaTranscriptAuth.Accepted (hashBytesOracle hash) verify
      (RegistrationSigningHistory.trial (absBytes request.public_key) protectedKey events payload
        (absBytes request.signature)) ↔
      protectedKey = true ∧ verify (absBytes request.public_key) (absBytes request.context)
        (absBytes request.input) (absBytes request.signature) = true := by
  simp only [MldsaTranscriptAuth.Accepted, RegistrationSigningHistory.trial,
    absBytes, List.length_map, Array.length_eq, Std.UScalar.ofNatCore_val_eq,
    true_and]
  simp only [absBytes] at context input
  rw [context, input]

def responseCandidate (pending : registration.BeaconPending) (packet : registration.ResponsePacket) :
    MldsaTranscriptAuth.Payload := MldsaTranscriptAuth.responsePayload
      (absBytes pending.binding.init_hash)
      (TranscriptAuthRefinement.absResponse (RegistrationResponse.responseFields packet))

/-- Actual inbound response construction and pinned verification use the exact request-bound model candidate. -/
theorem response_verification_source_exact (hash : HashOracle) (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) :
    ∃ (hashing : registration.ResponseHash) (verifying : registration.ResponseMldsaVerification)
        (request : registration.MldsaVerificationRequest),
      registration.begin_response_authentication pending (.Some packet) = ok (.Ok hashing) ∧
      (∃ hashRequest, hashing.request = ok hashRequest ∧
        hashBytes hashRequest = (responseCandidate pending packet).transcript) ∧
      hashing.resume (.Some (hash (responseCandidate pending packet).transcript)) = ok (.Ok verifying) ∧
      verifying.request = ok request ∧ request.public_key = pending.binding.server_pin.public_key ∧
      request.signature = packet.signature ∧
      absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
      absBytes request.input = (responseCandidate pending packet).message (hashBytesOracle hash) := by
  obtain ⟨hashing, beginRun, retainedPending, retainedPacket, parts, partsRun, preimage⟩ :=
    RegistrationResponse.begin_response_some_exact pending packet
  obtain ⟨verifying, digestRun, _pending, _packet, request, requestRun, key, signature,
      _context, contextBytes, message⟩ :=
    RegistrationResponse.response_hash_some_exact hashing (hash (responseCandidate pending packet).transcript)
  exact ⟨hashing, verifying, request, beginRun, ⟨.Triple parts, partsRun, preimage⟩,
    digestRun, requestRun, by simpa only [retainedPending] using key,
    by simpa only [retainedPacket] using signature, contextBytes, message⟩

end BeaconcryptCore.Refinement.RegistrationSigningDispatch

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.dispatch_server_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.dispatch_server_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.dispatch_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.dispatch_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.execution_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.execution_exists
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.execution_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.execution_matches
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.server_source_payload_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.server_source_payload_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.verification_trial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.verification_trial_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningDispatch.response_verification_source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningDispatch.response_verification_source_exact
