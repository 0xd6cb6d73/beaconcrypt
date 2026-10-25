-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.PanicFreedom.Structural
import BeaconcryptCore.PanicFreedom.Bytes
import BeaconcryptCore.PanicFreedom.Authentication
import BeaconcryptCore.PanicFreedom.SessionBinding
import BeaconcryptCore.Refinement.RegistrationInputs

/-! Normal return of outbound registration and completion phases, including arbitrary states and rejected primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom.RegistrationPublication

theorem BeaconInitialOpen_resume_total (self : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (opened : core.option.Option registration.InitialOpened) :
    ∃ result, registration.BeaconInitialOpen.resume self kernel opened = ok result := by
  cases hkernel : self.kernel <;> simp only [registration.BeaconInitialOpen.resume,
    pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new,
    core.option.Option.is_some, ratchet.concrete.ConcreteRatchetKernel.send_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
    ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
    ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
    ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
    core.slice.Slice.len, rust_primitives.slice.slice_length, hkernel, bind_tc_ok]
  all_goals repeat first | split | contradiction | exact ⟨_, rfl⟩
  rename_i io sequenceGood lengthGood
  have inside : 8 ≤ io.plaintext.val.length := by
    have large : 8 < io.plaintext.val.length := by
      simpa [pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE] using lengthGood
    omega
  obtain ⟨⟨boundPart, applicationPart⟩, splitRun⟩ : ∃ parts, core.slice.Slice.split_at io.plaintext
      pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE = ok parts := by
    simp [core.slice.Slice.split_at, rust_primitives.slice.slice_split_at,
      Aeneas.Std.core.slice.Slice.split_at, pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE, Slice.length, inside]
  obtain ⟨converted, convertedRun⟩ := copied_slice_total 8#usize boundPart
  cases converted with
  | Err error => simp [splitRun, convertedRun]
  | Ok bound =>
    obtain ⟨authenticated, authRun⟩ := authenticate_registration_key_id_binding_ok
      self.agreement.candidate io.sender_key_id bound
    cases authenticated <;>
      simp [splitRun, convertedRun, authRun, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id,
        session.RegistrationBinding.finish, pqxdh.beacon_commit]

theorem ServerInitialSeal_resume_total (self : registration.ServerInitialSeal)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.ServerInitialSeal.resume self kernel sequence ciphertext = ok result := by
  cases hkernel : self.kernel <;> simp only [registration.ServerInitialSeal.resume,
    pqxdh.server_abort_candidate, core.option.Option.is_some,
    ratchet.concrete.ConcreteRatchetKernel.send_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
    ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
    ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
    ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
    core.slice.Slice.len, rust_primitives.slice.slice_length, hkernel, bind_tc_ok]
  all_goals repeat first | split | contradiction | exact ⟨_, rfl⟩
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
  · rename_i encrypted noOverflowPlaintext noOverflowFrame correctLength
    split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · obtain ⟨responsePrefix, prefixRun⟩ := Authentication.build_response_prefix_total
          self.binding.init_hash self.candidate.server_identity_public_key
          self.candidate.ephemeral_public_key self.candidate.kem_ciphertext
          (UScalar.cast .U64 encrypted.len)
        obtain ⟨assignedId, idRun⟩ := Authentication.encode_u64_le_total self.candidate.key_id
        simp [prefixRun, pqxdh.ServerRegistrationCandidate.impl.key_id, idRun]

theorem begin_beacon_completion_total (accepted : agreement.BeaconAgreement) :
    ∃ result, registration.begin_beacon_completion accepted = ok result :=
  (Structural.pqxdh_concrete_start_beacon_candidate_ratchet_kdf_total
    accepted.candidate accepted.root.bytes).elim fun pending pendingRun =>
      ⟨{ agreement := accepted, pending }, by
        simp [registration.begin_beacon_completion, ratchet.RatchetChain.as_bytes, pendingRun]⟩

theorem BeaconInitialKdf_resume_total (self : registration.BeaconInitialKdf)
    (response : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, registration.BeaconInitialKdf.resume self response = ok result :=
  match response with
  | .none => ⟨_, rfl⟩
  | .some response =>
    (resume_initial_ratchet_kdf_ok self.pending response).elim fun kernel kernelRun =>
      ⟨.Ok { agreement := self.agreement, kernel := .Some kernel }, by
        simp [registration.BeaconInitialKdf.resume, kernelRun]⟩

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

theorem ServerInitialKdf_resume_total (self : registration.ServerInitialKdf)
    (response : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, registration.ServerInitialKdf.resume self response = ok result := by
  cases response with
  | none => exact ⟨_, rfl⟩
  | some response =>
    obtain ⟨kernel, kernelRun⟩ := resume_initial_ratchet_kdf_ok self.pending response
    obtain ⟨bound, boundRun⟩ := registration_key_id_binding_ok self.candidate.key_id
    simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate, kernelRun,
      pqxdh.ServerRegistrationCandidate.key_id_binding, pqxdh.RegistrationKeyIdBinding.as_bytes,
      boundRun]

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

end BeaconcryptCore.PanicFreedom.RegistrationPublication

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialOpen_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialOpen_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialSeal_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_beacon_completion_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_beacon_completion_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.BeaconInitialKdf_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_server_completion_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.begin_server_completion_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialKdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationPublication.ServerInitialKdf_resume_total

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
