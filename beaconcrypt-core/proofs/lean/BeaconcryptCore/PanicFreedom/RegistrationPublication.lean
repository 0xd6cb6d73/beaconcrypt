-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.PanicFreedom.Record
import BeaconcryptCore.PanicFreedom.RecordEffectsSend
import BeaconcryptCore.Refinement.RecordEffects
import BeaconcryptCore.PanicFreedom.Structural
import BeaconcryptCore.PanicFreedom.Bytes
import BeaconcryptCore.PanicFreedom.Authentication
import BeaconcryptCore.PanicFreedom.SessionBinding
import BeaconcryptCore.Refinement.RegistrationInputs

/-! Unconditional normal returns for the composed initial-record and registration publication phases. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom.RegistrationPublication

theorem BeaconRecordAead_finish_total (self : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.BeaconRecordAead.finish self plaintext = ok result := by
  obtain ⟨⟨kernel, opened⟩, openedRun⟩ := Record.finish_total self.pending.pending plaintext
  cases opened <;> simp only [registration.BeaconRecordAead.finish,
    pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new,
    record_effects.RecordReceiveAead.finish, openedRun, bind_tc_ok]
  all_goals dsimp! only
  all_goals try exact ⟨_, rfl⟩
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  split
  · exact ⟨_, rfl⟩

  · rename_i opened lengthGood
    have inside : 8 ≤ opened.plaintext.val.length := by
      have large : 8 < opened.plaintext.val.length := by
        simpa [pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE] using lengthGood
      omega
    obtain ⟨⟨boundPart, applicationPart⟩, splitRun⟩ : ∃ parts,
        core.slice.Slice.split_at opened.plaintext pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE = ok parts := by
      simp [core.slice.Slice.split_at, rust_primitives.slice.slice_split_at,
        Aeneas.Std.core.slice.Slice.split_at, pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE, Slice.length, inside]
    obtain ⟨converted, convertedRun⟩ := copied_slice_total 8#usize boundPart
    cases converted with
    | Err error => simp [splitRun, convertedRun]
    | Ok bound =>
      obtain ⟨authenticated, authRun⟩ := authenticate_registration_key_id_binding_ok
        self.agreement.candidate opened.key_id bound
      cases authenticated <;>
        simp [splitRun, convertedRun, authRun, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id,
          session.RegistrationBinding.finish, pqxdh.beacon_commit]

theorem normalize_beacon_open_total (accepted : agreement.BeaconAgreement) (effect : record_effects.RecordReceiveEffect) :
    ∃ result, registration.normalize_beacon_open accepted effect = ok result := by
  cases effect <;> exact ⟨_, rfl⟩

theorem BeaconRecordKdf_request_total (self : registration.BeaconRecordKdf) :
    ∃ result, registration.BeaconRecordKdf.request self = ok result :=
  ⟨_, rfl⟩

theorem BeaconRecordCommitment_transcript_total (self : registration.BeaconRecordCommitment) :
    ∃ result, registration.BeaconRecordCommitment.transcript self = ok result :=
  ⟨_, rfl⟩

theorem BeaconRecordCommitment_transcript_mut_total (self : registration.BeaconRecordCommitment) :
    ∃ result, registration.BeaconRecordCommitment.transcript_mut self = ok result :=
  ⟨_, rfl⟩

theorem BeaconRecordCommitment_supplied_commitment_total (self : registration.BeaconRecordCommitment) :
    ∃ result, registration.BeaconRecordCommitment.supplied_commitment self = ok result :=
  ⟨_, rfl⟩

theorem ServerRecordCommitment_transcript_total (self : registration.ServerRecordCommitment) :
    ∃ result, registration.ServerRecordCommitment.transcript self = ok result :=
  ⟨_, rfl⟩

theorem ServerRecordCommitment_transcript_mut_total (self : registration.ServerRecordCommitment) :
    ∃ result, registration.ServerRecordCommitment.transcript_mut self = ok result :=
  ⟨_, rfl⟩

theorem ServerInitialSeal_request_total (self : registration.ServerInitialSeal) :
    ∃ result, registration.ServerInitialSeal.request self = ok result :=
  ⟨_, rfl⟩

theorem ServerRecordWrite_resume_total (self : registration.ServerRecordWrite)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.ServerRecordWrite.resume self ciphertext = ok result := by
  cases ciphertext <;> simp only [registration.ServerRecordWrite.resume,
    pqxdh.server_abort_candidate, BeaconcryptCore.Refinement.RecordEffects.seal_write_finish_exact,
    core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  all_goals dsimp! only
  all_goals try exact ⟨_, rfl⟩
  simp only [core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize, UScalar.overflowing_add, bind_tc_ok]
  dsimp! only
  have overheadRun : record.MESSAGE_OVERHEAD = ok 80#usize := by
    simpa only [record.MESSAGE_OVERHEAD, record.COMMITMENT_SIZE, commitment.AEAD_TAG_SIZE] using
      usize_add_eq 64#usize 16#usize 80#usize (by simp)
  simp only [overheadRun, bind_tc_ok]
  repeat first | split | exact ⟨_, rfl⟩
  simp only [bind_tc_ok]
  repeat first | split | exact ⟨_, rfl⟩
  simp only [bind_tc_ok, session.RegistrationBinding.impl.init_hash,
    pqxdh.ServerRegistrationCandidate.impl.server_identity_public_key,
    pqxdh.ServerRegistrationCandidate.impl.ephemeral_public_key,
    pqxdh.ServerRegistrationCandidate.impl.kem_ciphertext,
    core.U64.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from, lift]
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · rename_i encrypted noOverflowPlaintext noOverflowFrame correctLength upper lower
        obtain ⟨responsePrefix, prefixRun⟩ := Authentication.build_response_prefix_total
          self.state.binding.init_hash self.state.candidate.server_identity_public_key
          self.state.candidate.ephemeral_public_key self.state.candidate.kem_ciphertext
          (UScalar.cast .U64 encrypted.len)
        obtain ⟨assignedId, idRun⟩ := Authentication.encode_u64_le_total self.state.candidate.key_id
        simp [prefixRun, pqxdh.ServerRegistrationCandidate.impl.key_id, idRun]

theorem begin_beacon_completion_total (accepted : agreement.BeaconAgreement) :
    ∃ result, registration.begin_beacon_completion accepted = ok result :=
  (Structural.pqxdh_concrete_start_beacon_candidate_ratchet_kdf_total
    accepted.candidate accepted.root.bytes).elim fun pending pendingRun =>
      ⟨{ agreement := accepted, pending }, by
        simp [registration.begin_beacon_completion, ratchet.RatchetChain.as_bytes, pendingRun]⟩

theorem begin_server_completion_total (control : pqxdh.ServerState)
    (current_pin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8) :
    ∃ result, registration.begin_server_completion control current_pin availability accepted application =
      ok result := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = ok result := ⟨_, rfl⟩
  obtain ⟨matched, matchRun⟩ := SessionBinding.RegistrationBinding_matches_server_total
    accepted.binding current_pin
  obtain ⟨prepared, prepareRun⟩ := server_prepare_commit_ok control accepted.pending
    current_pin.binding availability
  cases prepared with
  | Err error =>
    cases empty <;> cases matched <;>
      simp [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding,
        emptyRun, matchRun, prepareRun]
  | Ok candidate =>
    obtain ⟨pending, pendingRun⟩ := Structural.pqxdh_concrete_start_server_candidate_ratchet_kdf_total
      candidate accepted.root.bytes
    cases empty <;> cases matched <;>
      simp [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding,
        ratchet.RatchetChain.as_bytes, emptyRun, matchRun, prepareRun, pendingRun]

theorem ServerResponseHash_resume_total (self : registration.ServerResponseHash)
    (digest : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.ServerResponseHash.resume self digest = ok result := by
  cases digest with
  | none => exact ⟨_, rfl⟩
  | some digest =>
    obtain ⟨input, inputRun⟩ := Authentication.build_signature_input_total .Server digest
    simp [registration.ServerResponseHash.resume, pqxdh.server_abort_candidate, inputRun]

theorem ServerResponseSigning_resume_total (self : registration.ServerResponseSigning)
    (signature : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.ServerResponseSigning.resume self signature = ok result := by
  cases signature with
  | none => exact ⟨_, rfl⟩
  | some signature =>
    obtain ⟨converted, convertedRun⟩ := copied_slice_total 3309#usize signature
    cases converted <;>
      simp [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate, convertedRun]

theorem BeaconRecordAead_request_total (self : registration.BeaconRecordAead) :
    ∃ result, registration.BeaconRecordAead.request self = ok result := by
  simpa only [registration.BeaconRecordAead.request, record_effects.RecordReceiveAead.request]
    using Record.request_total self.pending.pending

theorem ServerInitialSeal_resume_total (self : registration.ServerInitialSeal)
    (response : core.option.Option ratchet.RatchetKdfResponse) :
    ∃ result, registration.ServerInitialSeal.resume self response = ok result := by
  cases response with
  | none => exact ⟨_, rfl⟩
  | some response =>
    obtain ⟨sealed, sealRun⟩ := ratchet.concrete.SendKdf.resume_total self.pending.pending response
    exact ⟨.Ok ⟨self.state, ⟨sealed⟩⟩, by
      simp only [registration.ServerInitialSeal.resume, record_effects.RecordSendKdf.resume,
        sealRun, bind_tc_ok]⟩

theorem ServerRecordAead_request_total (self : registration.ServerRecordAead) :
    ∃ result, registration.ServerRecordAead.request self = ok result := by
  cases prefixRun : self.pending.seal.context.prefix <;>
    simp [registration.ServerRecordAead.request, record_effects.SealAead.request,
      ratchet.concrete.SendSeal.impl.material, ratchet.concrete.SendSeal.impl.context,
      ratchet.RatchetMaterial.impl.key, ratchet.RatchetMaterial.impl.nonce,
      ratchet.RatchetKey.as_bytes, ratchet.RatchetNonce.as_bytes,
      record_effects.SealFrameContext.plaintext_request, prefixRun]

theorem ServerRecordAead_resume_total (self : registration.ServerRecordAead)
    (detached : core.option.Option ((Slice Std.U8) × (Array Std.U8 16#usize))) :
    ∃ result, registration.ServerRecordAead.resume self detached = ok result := by
  cases detached with
  | none =>
    exact ⟨.Err self.state.candidate.previous_state, by simp [registration.ServerRecordAead.resume,
      BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact, pqxdh.server_abort_candidate]⟩
  | some detached =>
    obtain ⟨next, nextRun, _⟩ := BeaconcryptCore.Refinement.RecordEffects.seal_aead_supplied_exact
      self.pending detached.1 detached.2
    exact ⟨.Ok ⟨self.state, next⟩, by
      simp only [registration.ServerRecordAead.resume, nextRun, bind_tc_ok]⟩

theorem ServerRecordCommitment_resume_total (self : registration.ServerRecordCommitment)
    (commitment1 : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.ServerRecordCommitment.resume self commitment1 = ok result := by
  obtain ⟨next, nextRun⟩ := RecordEffects.SealCommitment_resume_total self.pending commitment1
  cases next <;> simp [registration.ServerRecordCommitment.resume, nextRun, pqxdh.server_abort_candidate]

theorem ServerRecordWrite_request_total (self : registration.ServerRecordWrite) :
    ∃ result, registration.ServerRecordWrite.request self = ok result := by
  simpa only [registration.ServerRecordWrite.request] using RecordEffectsSend.SealWrite_request_total self.pending

theorem BeaconInitialKdf_resume_total (self : registration.BeaconInitialKdf)
    (response : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, registration.BeaconInitialKdf.resume self response = ok result := by
  cases response with
  | none => exact ⟨_, rfl⟩
  | some response =>
    obtain ⟨kernel, kernelRun⟩ := resume_initial_ratchet_kdf_ok self.pending response
    obtain ⟨effect, effectRun⟩ := RecordEffects.begin_record_receive_total kernel 1#u64
      self.agreement.application_ciphertext self.agreement.binding.associated_data
      self.agreement.candidate.server_binding.identity_key_id
    obtain ⟨result, normal⟩ := normalize_beacon_open_total self.agreement effect
    exact ⟨result, by simpa only [registration.BeaconInitialKdf.resume, kernelRun,
      session.RegistrationBinding.impl.associated_data, pqxdh.BeaconRegistrationCandidate.server_key_id,
      effectRun, bind_tc_ok] using normal⟩

theorem BeaconRecordKdf_resume_total (self : registration.BeaconRecordKdf)
    (response : core.option.Option ratchet.RatchetKdfResponse) :
    ∃ result, registration.BeaconRecordKdf.resume self response = ok result := by
  cases response with
  | none => exact ⟨_, rfl⟩
  | some response =>
    obtain ⟨effect, effectRun⟩ := RecordEffects.RecordReceiveKdf_resume_total self.pending response
    obtain ⟨result, normal⟩ := normalize_beacon_open_total self.agreement effect
    exact ⟨result, by simpa only [registration.BeaconRecordKdf.resume, effectRun, bind_tc_ok] using normal⟩

theorem BeaconRecordCommitment_resume_total (self : registration.BeaconRecordCommitment)
    (matched : Bool) :
    ∃ result, registration.BeaconRecordCommitment.resume self matched = ok result := by
  obtain ⟨effect, effectRun⟩ := RecordEffects.RecordReceiveCommitment_resume_total self.pending matched
  obtain ⟨result, normal⟩ := normalize_beacon_open_total self.agreement effect
  exact ⟨result, by simpa only [registration.BeaconRecordCommitment.resume, effectRun, bind_tc_ok] using normal⟩

theorem ServerInitialKdf_resume_total (self : registration.ServerInitialKdf)
    (response : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, registration.ServerInitialKdf.resume self response = ok result := by
  cases response with
  | none => exact ⟨_, rfl⟩
  | some response =>
    obtain ⟨kernel, kernelRun⟩ := resume_initial_ratchet_kdf_ok self.pending response
    obtain ⟨context, contextRun⟩ := RecordEffects.SealFrameContext_registration_total self.application
      self.candidate.key_id self.candidate.server_identity_key_id self.binding.associated_data
    obtain ⟨start, startRun⟩ := RecordEffectsSend.begin_record_send_total kernel context
    cases start <;> simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate,
      kernelRun, pqxdh.ServerRegistrationCandidate.impl.key_id,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id,
      session.RegistrationBinding.impl.associated_data, contextRun, startRun]

end BeaconcryptCore.PanicFreedom.RegistrationPublication

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordAead_finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordAead_finish_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.normalize_beacon_open_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.normalize_beacon_open_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordKdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordKdf_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_transcript_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_transcript_mut_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_transcript_mut_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_supplied_commitment_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_supplied_commitment_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_transcript_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_transcript_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_transcript_mut_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_transcript_mut_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_beacon_completion_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_beacon_completion_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_server_completion_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_server_completion_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseHash_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseHash_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseSigning_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerResponseSigning_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordAead_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordAead_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordAead_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordCommitment_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerRecordWrite_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialKdf_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordKdf_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconRecordCommitment_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialKdf_resume_total
