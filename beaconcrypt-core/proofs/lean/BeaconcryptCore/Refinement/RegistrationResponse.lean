-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.PanicFreedom.RegistrationTrivial

/-! Exact incoming response transcript operands and retained pending authentication state. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationResponse

private theorem usize_to_u64 (value : Std.Usize) :
    core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from value =
      ok (core.result.Result.Ok (UScalar.cast .U64 value)) := by
  simp only [core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
    lift, bind_tc_ok]
  simp only [core.num.U64.MAX, core.num.U64.MIN]
  cases System.Platform.numBits_eq
  all_goals simp [*, UScalar.lt_equiv, UScalar.cast_val_eq]
  all_goals norm_num [U64.rMax]
  all_goals have bounds := value.hBounds
  all_goals simp [UScalarTy.numBits, *] at bounds
  all_goals omega

private theorem usize_to_u64_value (value : Std.Usize) :
    (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq
  all_goals simp [UScalarTy.numBits, *]

def responseFields (packet : registration.ResponsePacket) : authentication.ResponseFields := {
  identity_key := packet.public.identity_key
  ephemeral_key := packet.public.ephemeral_key
  kem_cipher_text := packet.public.kem_cipher_text
  app_cipher_text := packet.application
  key_id := packet.public.key_id }

def abortedState (pending : registration.BeaconPending) : pqxdh.BeaconAborted := {
  server_key_id := pending.control.expected_server_binding.identity_key_id }

/-- The actual request has exactly three ordered retained parts. -/
theorem response_hash_request_exact (self : registration.ResponseHash) :
    ∃ parts, registration.ResponseHash.request self = ok (.Triple parts) ∧
      RegistrationInputs.hashBytes (.Triple parts) = absBytes self.prefix ++
        TranscriptAuthParts.absSlice self.packet.application ++ absBytes self.assigned_id := by
  refine ⟨_, rfl, ?_⟩
  change absBytes self.prefix ++ (TranscriptAuthParts.absSlice self.packet.application ++
    (absBytes self.assigned_id ++ [])) = _
  simp only [List.append_nil, List.append_assoc]

/-- Every well-typed packet retains its pending owner and hashes the complete unsigned response transcript. -/
theorem begin_response_some_exact (pending : registration.BeaconPending)
    (packet : registration.ResponsePacket) :
    ∃ next, registration.begin_response_authentication pending (.Some packet) = ok (.Ok next) ∧
      next.pending = pending ∧ next.packet = packet ∧
      ∃ parts, registration.ResponseHash.request next = ok (.Triple parts) ∧
        RegistrationInputs.hashBytes (.Triple parts) =
          Pqxdh.TranscriptAuth.responseTranscript (absBytes pending.binding.init_hash)
            (TranscriptAuthRefinement.absResponse (responseFields packet)) := by
  obtain ⟨buffer, prefixRun, prefixBytes⟩ := TranscriptAuthRefinement.build_response_prefix_abs
    pending.binding.init_hash packet.public.identity_key packet.public.ephemeral_key
    packet.public.kem_cipher_text (UScalar.cast .U64 packet.application.len)
  obtain ⟨assigned, assignedRun, assignedBytes⟩ := TranscriptAuthRefinement.encode_u64_le_abs packet.public.key_id
  refine ⟨{ pending, packet, «prefix» := buffer, assigned_id := assigned }, ?_, rfl, rfl, ?_⟩
  · simp only [registration.begin_response_authentication, core.slice.Slice.len,
      rust_primitives.slice.slice_length, usize_to_u64, session.RegistrationBinding.impl.init_hash,
      prefixRun, assignedRun, bind_tc_ok]
  · obtain ⟨parts, partsRun, partsBytes⟩ := response_hash_request_exact
      { pending, packet, «prefix» := buffer, assigned_id := assigned }
    refine ⟨parts, partsRun, ?_⟩
    rw [partsBytes, prefixBytes, assignedBytes]
    simp [TranscriptAuthRefinement.responsePrefix, Pqxdh.TranscriptAuth.responseTranscript,
      responseFields, TranscriptAuthRefinement.absResponse, Pqxdh.TranscriptAuth.hashField,
      TranscriptAuthParts.absSlice, List.append_assoc]

/-- The selected server pin, supplied packet signature and actual digest determine the exact ML verification request. -/
theorem response_hash_some_exact (self : registration.ResponseHash)
    (digest : Array Std.U8 64#usize) :
    ∃ next, registration.ResponseHash.resume self (.Some digest) = ok (.Ok next) ∧
      next.pending = self.pending ∧ next.packet = self.packet ∧
      ∃ request, registration.ResponseMldsaVerification.request next = ok request ∧
        request.public_key = self.pending.binding.server_pin.public_key ∧
        request.signature = self.packet.signature ∧
        request.context = authentication.SIGNING_CONTEXT ∧
        absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
        absBytes request.input = Pqxdh.TranscriptAuth.signatureInput .server (absBytes digest) := by
  obtain ⟨input, inputRun, inputBytes⟩ :=
    TranscriptAuthInputsRefinement.build_signature_input_abs .Server digest
  refine ⟨{ pending := self.pending, packet := self.packet, input }, ?_, rfl, rfl,
    _, rfl, rfl, rfl, rfl, TranscriptAuthInputsRefinement.signing_context_abs, inputBytes⟩
  simp only [registration.ResponseHash.resume, inputRun, bind_tc_ok]

/-- Malformed packet admission and failed hashing preserve the pending control's exact terminal abort identifier. -/
theorem malformed_and_hash_failure_exact (pending : registration.BeaconPending)
    (self : registration.ResponseHash) :
    registration.begin_response_authentication pending .None = ok (.Err (abortedState pending)) ∧
      registration.ResponseHash.resume self .None = ok (.Err (abortedState self.pending)) := by
  exact ⟨rfl, rfl⟩

/-- Only a successful verification reply publishes the exact retained packet and pending binding. -/
theorem response_mldsa_gate_exact (self : registration.ResponseMldsaVerification) (verified : Bool) :
    registration.ResponseMldsaVerification.resume self verified =
      if verified then ok (.Ok { pending := self.pending, packet := self.packet })
      else ok (.Err (abortedState self.pending)) := by
  rfl

end BeaconcryptCore.Refinement.RegistrationResponse

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_hash_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_hash_request_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.begin_response_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.begin_response_some_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_hash_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_hash_some_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.malformed_and_hash_failure_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.malformed_and_hash_failure_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_mldsa_gate_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_mldsa_gate_exact
