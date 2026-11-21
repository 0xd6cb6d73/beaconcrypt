-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.RegistrationAd

/-! Exact incoming response transcript operands and retained pending authentication state. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 4096

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

/-- Pinned verification selects the exact retained-request and response AD preimage. A false reply aborts before that request is exposed. -/
theorem response_mldsa_gate_exact (self : registration.ResponseMldsaVerification) (verified : Bool) :
    ∃ next, registration.ResponseMldsaVerification.resume self verified =
      (if verified then ok (.Ok next) else ok (.Err (abortedState self.pending))) ∧
      next.pending = self.pending ∧ next.packet = self.packet ∧
      absBytes next.input = RegistrationAd.preimage self.pending.binding
        (RegistrationAd.responseView self.packet.public) := by
  obtain ⟨next, ran, pending, packet, input⟩ := RegistrationAd.verified_response_selects_exact_ad self
  refine ⟨next, ?_, pending, packet, input⟩
  cases verified
  · simp only [registration.ResponseMldsaVerification.resume, Bool.false_eq_true, ↓reduceIte,
      registration.BeaconPending.abort, pqxdh.beacon_abort_init, abortedState, bind_tc_ok]
  · exact ran

/-- The second hash uses the full fixed2638-byte AD encoder result. -/
theorem response_ad_hash_request_exact (self : registration.BeaconAdHash) :
    ∃ request, self.request = ok request ∧ RegistrationInputs.hashBytes request = absBytes self.input :=
  ⟨_, rfl, rfl⟩

/-- The final authentication reply retains control, pin, request digest, packet, exact new digest and assembled AD. -/
theorem response_ad_hash_some_exact (self : registration.BeaconAdHash)
    (digest : Array Std.U8 64#usize) :
    ∃ accepted, self.resume (.Some digest) = ok (.Ok accepted) ∧
      accepted.control = self.pending.control ∧ accepted.packet = self.packet ∧
      accepted.binding.server_pin = self.pending.binding.server_pin ∧
      accepted.binding.init_hash = self.pending.binding.init_hash ∧
      accepted.binding.session_transcript_hash = digest ∧
      SessionBinding.registrationConsistent accepted.binding := by
  obtain ⟨binding, ran, pin, initHash, identity, hash, ad⟩ :=
    SessionBinding.complete_refines self.pending.binding digest
  refine ⟨⟨self.pending.control, binding, self.packet⟩, ?_, rfl, rfl, pin, initHash, hash, ad⟩
  simp [registration.BeaconAdHash.resume, ran]

theorem response_ad_hash_none_exact (self : registration.BeaconAdHash) :
    self.resume .None = ok (.Err (abortedState self.pending)) := rfl

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

/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_request_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_some_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_none_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationResponse.response_ad_hash_none_exact
