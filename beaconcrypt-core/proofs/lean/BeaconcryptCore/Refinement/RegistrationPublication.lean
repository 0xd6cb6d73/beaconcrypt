-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.RegistrationPublication

/-! Exact completion gates and publication of retained registration fields. Primitive execution and native codec laws remain explicit interpreter obligations; the core now owns record metadata and kernel continuations. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RegistrationPublication

/-- Finish retains every authenticated metadata field and the complete populated AD. -/
def completedBinding (binding : session.RegistrationBinding) (assignedId : Std.U64) :
    session.SessionBinding :=
  ⟨binding.server_pin.binding, assignedId, binding.beacon_identity_public_key,
    binding.server_pin.fingerprint, binding.beacon_fingerprint, binding.associated_data⟩

/-- No pending capability is published on encoding failure; success transfers the same control, binding and encoded output. -/
theorem beacon_publication_refines {Encoded : Type} (ready : registration.BeaconInitReady)
    (encoded : core.option.Option Encoded) :
    ready.publish encoded = ok (match encoded with
      | .None => .Err ready.state.original_control
      | .Some output => .Ok
        ⟨⟨ready.state.started.state, ready.binding⟩, output⟩) := by
  cases encoded <;> rfl

/-- Encoding failure returns the exact previous server control; success publishes the same kernel, completed binding and bytes. -/
theorem server_publication_refines {Encoded : Type} (ready : registration.ServerResponseReady)
    (encoded : core.option.Option Encoded) :
    ready.publish encoded = ok (match encoded with
      | .None => .Err ready.candidate.previous_state
      | .Some output => .Ok
        ⟨ready.candidate.next_state, completedBinding ready.binding ready.candidate.key_id,
          ready.kernel, output⟩) := by
  cases encoded <;> rfl

/-- The actual response digest continuation retains the candidate/kernel/ciphertext and selects exact server ML signing operands. -/
theorem server_response_hash_refines (pending : registration.ServerResponseHash)
    (digest : Array Std.U8 64#usize) :
    ∃ next : registration.ServerResponseSigning,
      pending.resume (.Some digest) = ok (.Ok next) ∧
      next.candidate = pending.candidate ∧ next.binding = pending.binding ∧
      next.kernel = pending.kernel ∧ next.ciphertext = pending.ciphertext ∧
      absBytes next.input = Pqxdh.TranscriptAuth.signatureInput .server (absBytes digest) ∧
      next.request = ok
        ⟨pending.binding.server_pin.public_key, .Server, next.input, authentication.SIGNING_CONTEXT⟩ := by
  obtain ⟨input, inputRun, inputBytes⟩ :=
    TranscriptAuthInputsRefinement.build_signature_input_abs .Server digest
  refine ⟨⟨pending.candidate, pending.binding, pending.kernel, pending.ciphertext, input⟩,
    ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp [registration.ServerResponseHash.resume, pqxdh.server_abort_candidate, inputRun]
  · simpa only [TranscriptAuthInputsRefinement.absRole] using inputBytes

/-- The actual signature gate accepts exactly the full ML-DSA width and retains every candidate, kernel and ciphertext field. -/
theorem server_signature_admission_refines (pending : registration.ServerResponseSigning)
    (signature : Slice Std.U8) :
    ∃ result, pending.resume (.Some signature) = ok result ∧
      match result with
      | .Err previous => previous = pending.candidate.previous_state ∧ signature.val.length ≠ 3309
      | .Ok ready => ready.candidate = pending.candidate ∧ ready.binding = pending.binding ∧
        ready.kernel = pending.kernel ∧ ready.ciphertext = pending.ciphertext ∧
        ready.signature.val = signature.val ∧ signature.val.length = 3309 := by
  obtain ⟨converted, convertedRun, convertedFacts⟩ := copied_slice_exact 3309#usize signature
  cases converted with
  | Err error =>
    refine ⟨.Err pending.candidate.previous_state, ?_, rfl, ?_⟩
    · simp [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate, convertedRun]
    · simpa using convertedFacts
  | Ok bytes =>
    refine ⟨.Ok ⟨pending.candidate, pending.binding, pending.kernel, pending.ciphertext, bytes⟩,
      ?_, rfl, rfl, rfl, rfl, convertedFacts.1, ?_⟩
    · simp [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate, convertedRun]
    · simpa using convertedFacts.2

/-- A changed complete owner pin rejects before candidate initialization and returns the current caller control. -/
theorem server_owner_rejects (control : pqxdh.ServerState)
    (current : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8)
    (changed : ¬ BeaconcryptCore.Refinement.SessionBinding.sameServerPin accepted.binding.server_pin current) :
    registration.begin_server_completion control current availability accepted application = ok (.Err control) := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = ok result := ⟨_, rfl⟩
  cases empty <;> simp [registration.begin_server_completion, emptyRun,
    BeaconcryptCore.Refinement.SessionBinding.matches_server_refines, changed]

/-- The actual response-hash request streams its retained prefix, exact ciphertext and assigned-ID suffix in order. -/
theorem server_hash_request_refines (pending : registration.ServerResponseHash) :
    ∃ request, pending.request = ok request ∧ hashBytes request =
      absBytes pending.prefix ++ TranscriptAuthParts.absSlice pending.ciphertext ++ absBytes pending.assigned_id := by
  refine ⟨_, rfl, ?_⟩
  change absBytes pending.prefix ++
    (TranscriptAuthParts.absSlice pending.ciphertext ++ (absBytes pending.assigned_id ++ [])) = _
  simp only [List.append_nil, List.append_assoc]

/-- Exact unsigned response fields selected by the retained server candidate. -/
def serverResponseFields (candidate : pqxdh.ServerRegistrationCandidate) (ciphertext : Slice Std.U8) :
    authentication.ResponseFields :=
  ⟨candidate.server_identity_public_key, candidate.ephemeral_public_key,
    candidate.kem_ciphertext, ciphertext, candidate.key_id⟩

/-- Empty application data returns the exact current control before owner preparation or initial KDF setup. -/
theorem server_empty_application_rejects (control : pqxdh.ServerState)
    (current : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8) (empty : application.val = []) :
    registration.begin_server_completion control current availability accepted application = ok (.Err control) := by
  simp [registration.begin_server_completion, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, Slice.len, empty]

/-- The actual complete-record writer either preserves the old control or retains the same candidate, source-owned kernel and exact encoded ciphertext. -/
def serverSealRetains (before : registration.ServerRecordWrite)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    core.result.Result registration.ServerResponseHash pqxdh.ServerState → Prop
  | .Err previous => previous = before.state.candidate.previous_state
  | .Ok after => after.candidate = before.state.candidate ∧ after.binding = before.state.binding ∧
      after.kernel = before.pending.seal.advanced ∧ ciphertext = .Some after.ciphertext ∧
      authentication.build_response_prefix before.state.binding.init_hash
        before.state.candidate.server_identity_public_key before.state.candidate.ephemeral_public_key
        before.state.candidate.kem_ciphertext (UScalar.cast .U64 after.ciphertext.len) = ok after.prefix ∧
      authentication.encode_u64_le before.state.candidate.key_id = ok after.assigned_id

/-- This continuation consumes the actual writer reply and obtains the kernel from its owned record capability. -/
theorem server_seal_retention_refines (self : registration.ServerRecordWrite)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume ciphertext = ok result ∧ serverSealRetains self ciphertext result := by
  cases ciphertext <;> simp only [registration.ServerRecordWrite.resume,
    pqxdh.server_abort_candidate, BeaconcryptCore.Refinement.RecordEffects.seal_write_finish_exact,
    core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  all_goals dsimp! only
  all_goals try exact ⟨_, rfl, rfl⟩
  simp only [core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize, UScalar.overflowing_add, bind_tc_ok]
  dsimp! only
  have overheadRun : record.MESSAGE_OVERHEAD = ok 80#usize := by
    simpa only [record.MESSAGE_OVERHEAD, record.COMMITMENT_SIZE, commitment.AEAD_TAG_SIZE] using
      usize_add_eq 64#usize 16#usize 80#usize (by simp)
  simp only [overheadRun, bind_tc_ok]
  repeat first | split | exact ⟨_, rfl, rfl⟩
  simp only [bind_tc_ok]
  repeat first | split | exact ⟨_, rfl, rfl⟩
  simp only [bind_tc_ok, session.RegistrationBinding.impl.init_hash,
    pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
    pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
    pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext,
    core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from, lift]
  split
  · exact ⟨_, rfl, rfl⟩
  · split
    · exact ⟨_, rfl, rfl⟩
    · split
      · exact ⟨_, rfl, rfl⟩
      · rename_i encrypted noOverflowPlaintext noOverflowFrame correctLength upper lower
        obtain ⟨responsePrefix, prefixRun⟩ := BeaconcryptCore.PanicFreedom.Authentication.build_response_prefix_total
          self.state.binding.init_hash self.state.candidate.server_identity_public_key
          self.state.candidate.ephemeral_public_key self.state.candidate.kem_ciphertext
          (UScalar.cast .U64 encrypted.len)
        obtain ⟨assignedId, idRun⟩ := BeaconcryptCore.PanicFreedom.Authentication.encode_u64_le_total self.state.candidate.key_id
        simp [prefixRun, pqxdh.ServerRegistrationCandidate.impl.key_id, idRun, serverSealRetains]

/-- The actual final writer continuation builds exactly the model response transcript from its owned candidate and real complete ciphertext. -/
theorem server_seal_preimage_refines (self : registration.ServerRecordWrite)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume ciphertext = ok result ∧
      match result with
      | .Err previous => previous = self.state.candidate.previous_state
      | .Ok next => next.candidate = self.state.candidate ∧ next.binding = self.state.binding ∧
        next.kernel = self.pending.seal.advanced ∧ ciphertext = .Some next.ciphertext ∧
        ∃ request, next.request = ok request ∧ hashBytes request =
          Pqxdh.TranscriptAuth.responseTranscript (absBytes self.state.binding.init_hash)
            (TranscriptAuthRefinement.absResponse (serverResponseFields self.state.candidate next.ciphertext)) := by
  obtain ⟨result, run, retained⟩ := server_seal_retention_refines self ciphertext
  cases result with
  | Err previous => exact ⟨.Err previous, run, retained⟩
  | Ok next =>
    rcases retained with ⟨candidate, binding, kernelEq, ciphertextEq, prefixRun, idRun⟩
    obtain ⟨request, requestRun, requestBytes⟩ := server_hash_request_refines next
    obtain ⟨canonical, canonicalRun, canonicalBytes⟩ := TranscriptAuthRefinement.build_response_prefix_abs
      self.state.binding.init_hash self.state.candidate.server_identity_public_key self.state.candidate.ephemeral_public_key
      self.state.candidate.kem_ciphertext (UScalar.cast .U64 next.ciphertext.len)
    have prefixSame : next.prefix = canonical := by simpa using prefixRun.symm.trans canonicalRun
    obtain ⟨assigned, assignedRun, assignedBytes⟩ :=
      TranscriptAuthRefinement.encode_u64_le_abs self.state.candidate.key_id
    have idSame : next.assigned_id = assigned := by simpa using idRun.symm.trans assignedRun
    have sameLength : (UScalar.cast .U64 next.ciphertext.len).val = next.ciphertext.val.length := by
      calc
        _ = next.ciphertext.len.val := by
          apply UScalar.cast_val_mod_pow_greater_numBits_eq
          cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
        _ = _ := by simp
    refine ⟨.Ok next, run, candidate, binding, kernelEq, ciphertextEq, request, requestRun, ?_⟩
    rw [requestBytes, prefixSame, idSame, canonicalBytes, assignedBytes, sameLength]
    simp [TranscriptAuthRefinement.responsePrefix, TranscriptAuthRefinement.absResponse,
      serverResponseFields, Pqxdh.TranscriptAuth.responseTranscript, Pqxdh.TranscriptAuth.hashField,
      TranscriptAuthParts.absSlice, List.append_assoc]


end BeaconcryptCore.Refinement.RegistrationPublication

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_publication_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_publication_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_signature_admission_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_signature_admission_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_hash_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_hash_request_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_empty_application_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_empty_application_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_seal_preimage_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_seal_preimage_refines
