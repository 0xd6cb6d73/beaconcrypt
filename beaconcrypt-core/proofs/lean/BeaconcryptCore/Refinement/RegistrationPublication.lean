-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.RegistrationPublication

/-! Exact completion gates and publication of retained registration fields. Initial-record provenance and native codec/primitive laws remain explicit interpreter obligations. -/

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

/-- Initial opening selects the authenticated response ciphertext, full retained AD and pinned sender at sequence one. -/
theorem beacon_initial_request_refines (pending : registration.BeaconInitialOpen) :
    pending.request = ok
      ⟨pending.agreement.application_ciphertext, pending.agreement.binding.associated_data,
        1#u64, pending.agreement.candidate.server_binding.identity_key_id⟩ :=
  rfl

/-- A missing initial opening always returns the retained terminal control, for any represented kernel. -/
theorem beacon_missing_payload_rejects (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    pending.resume kernel .None = ok
      (.Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  cases previousKernel : pending.kernel <;>
    simp [registration.BeaconInitialOpen.resume, pqxdh.BeaconRegistrationCandidate.server_key_id,
      pqxdh.BeaconAborted.new, core.option.Option.is_some,
      ratchet.concrete.ConcreteRatchetKernel.send_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
      ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
      ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
      ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
      previousKernel]

/-- The accepted initial record keeps the exact kernel and drops only the eight authenticated ID bytes. -/
def completedBeacon (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (opened : registration.InitialOpened) :
    registration.CompletedBeacon :=
  ⟨⟨pending.agreement.candidate.server_binding, pending.agreement.candidate.assigned_key_id⟩,
    completedBinding pending.agreement.binding pending.agreement.candidate.assigned_key_id,
    kernel, opened.plaintext.drop 8#usize⟩

/-- Full initial plaintext admission is exact: sender, all eight ID bytes and a nonempty suffix determine acceptance. -/
theorem beacon_payload_admission_refines (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (opened : registration.InitialOpened)
    (taken : pending.kernel = .None)
    (send : kernel.refined.control.send_sequence = 0#u64)
    (receive : kernel.refined.control.receive_sequence = 1#u64)
    (cache : kernel.refined.control.receive_cache.len = 0#u8)
    (sequence : opened.sequence = 1#u64)
    (nonempty : 8 < opened.plaintext.val.length) :
    pending.resume kernel (.Some opened) = ok
      (if opened.sender_key_id = pending.agreement.candidate.server_binding.identity_key_id ∧
          (opened.plaintext.val.take 8).map absByte =
            Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
        then .Ok (completedBeacon pending kernel opened)
        else .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  obtain ⟨expected, expectedRun, expectedBytes⟩ :=
    registration_key_id_binding_abs pending.agreement.candidate.assigned_key_id
  let boundPart : Slice Std.U8 := ⟨opened.plaintext.val.take 8, by
    have size := opened.plaintext.property
    simp only [List.length_take]
    omega⟩
  let applicationPart := opened.plaintext.drop 8#usize
  have splitRun : core.slice.Slice.split_at opened.plaintext
      pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE = ok (boundPart, applicationPart) := by
    simp [core.slice.Slice.split_at, rust_primitives.slice.slice_split_at,
      Aeneas.Std.core.slice.Slice.split_at, pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE,
      Slice.length, Nat.le_of_lt nonempty, List.splitAt_eq, boundPart, applicationPart, Slice.drop]
  obtain ⟨converted, convertedRun, convertedFacts⟩ := copied_slice_exact 8#usize boundPart
  cases converted with
  | Err error =>
    exact False.elim (convertedFacts (by
      simp [boundPart, List.length_take, Nat.min_eq_left (Nat.le_of_lt nonempty)]))
  | Ok bound =>
    have boundBytes : absBytes bound = (opened.plaintext.val.take 8).map absByte := by
      simp [absBytes, convertedFacts.1, boundPart]
    have longEnough : pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE.val < opened.plaintext.val.length := by
      simpa [pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE] using nonempty
    by_cases sender : opened.sender_key_id = pending.agreement.candidate.server_binding.identity_key_id <;>
      by_cases bytes : (opened.plaintext.val.map absByte).take 8 =
        Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
    all_goals simp [registration.BeaconInitialOpen.resume,
      pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new,
      core.option.Option.is_some, ratchet.concrete.ConcreteRatchetKernel.send_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
      ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
      ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
      ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
      core.slice.Slice.len, rust_primitives.slice.slice_length, taken, send, receive, cache, sequence,
      Nat.not_le.mpr longEnough, splitRun, convertedRun, pqxdh.authenticate_registration_key_id_binding,
      pqxdh.BeaconRegistrationCandidate.key_id_binding, expectedRun, array_eq_abs,
      boundBytes, expectedBytes, sender, bytes, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id,
      session.RegistrationBinding.finish, pqxdh.beacon_commit, completedBeacon, completedBinding,
      applicationPart]

/-- Every invalid initial kernel or unconsumed kernel capability rejects with the retained server ID. -/
theorem beacon_kernel_rejects (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (opened : core.option.Option registration.InitialOpened)
    (bad : pending.kernel ≠ .None ∨ kernel.refined.control.send_sequence.val ≠ 0 ∨
      kernel.refined.control.receive_sequence.val ≠ 1 ∨ kernel.refined.control.receive_cache.len.val ≠ 0) :
    pending.resume kernel opened = ok
      (.Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  cases previousKernel : pending.kernel <;>
    rcases bad with present | send | receive | cache <;>
    simp_all [registration.BeaconInitialOpen.resume, pqxdh.BeaconRegistrationCandidate.server_key_id,
      pqxdh.BeaconAborted.new, core.option.Option.is_some,
      ratchet.concrete.ConcreteRatchetKernel.send_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
      ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
      ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
      ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len]

/-- A later sequence or a plaintext with no application suffix rejects before binding authentication. -/
theorem beacon_plaintext_rejects (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (opened : registration.InitialOpened)
    (bad : opened.sequence.val ≠ 1 ∨ opened.plaintext.val.length ≤ 8) :
    pending.resume kernel (.Some opened) = ok
      (.Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  cases previousKernel : pending.kernel <;>
    rcases bad with sequence | length <;>
    simp_all [registration.BeaconInitialOpen.resume, pqxdh.BeaconRegistrationCandidate.server_key_id,
      pqxdh.BeaconAborted.new, core.option.Option.is_some,
      ratchet.concrete.ConcreteRatchetKernel.send_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
      ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
      ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
      ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
      core.slice.Slice.len, rust_primitives.slice.slice_length, pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE]

/-- The complete extracted first-record gate has this exact result on every represented state and opening reply. -/
theorem beacon_completion_refines (pending : registration.BeaconInitialOpen)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (opened : core.option.Option registration.InitialOpened) :
    pending.resume kernel opened = ok (match opened with
      | .None => .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩
      | .Some plaintext =>
        if pending.kernel.isNone = true ∧ kernel.refined.control.send_sequence.val = 0 ∧
            kernel.refined.control.receive_sequence.val = 1 ∧ kernel.refined.control.receive_cache.len.val = 0 ∧
            plaintext.sequence.val = 1 ∧ 8 < plaintext.plaintext.val.length ∧
            plaintext.sender_key_id = pending.agreement.candidate.server_binding.identity_key_id ∧
            (plaintext.plaintext.val.take 8).map absByte =
              Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
          then .Ok (completedBeacon pending kernel plaintext)
          else .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  cases opened with
  | none => exact beacon_missing_payload_rejects pending kernel
  | some plaintext =>
    cases previousKernel : pending.kernel with
    | some previous =>
      simpa [previousKernel] using beacon_kernel_rejects pending kernel (.Some plaintext)
        (.inl (by simp [previousKernel]))
    | none =>
      by_cases ready : kernel.refined.control.send_sequence.val = 0 ∧
          kernel.refined.control.receive_sequence.val = 1 ∧ kernel.refined.control.receive_cache.len.val = 0
      · rcases ready with ⟨send, receive, cache⟩
        by_cases sequence : plaintext.sequence.val = 1
        · by_cases nonempty : 8 < plaintext.plaintext.val.length
          · have sendScalar : kernel.refined.control.send_sequence = 0#u64 :=
              UScalar.eq_of_val_eq (by simpa using send)
            have receiveScalar : kernel.refined.control.receive_sequence = 1#u64 :=
              UScalar.eq_of_val_eq (by simpa using receive)
            have cacheScalar : kernel.refined.control.receive_cache.len = 0#u8 :=
              UScalar.eq_of_val_eq (by simpa using cache)
            have sequenceScalar : plaintext.sequence = 1#u64 :=
              UScalar.eq_of_val_eq (by simpa using sequence)
            simpa [previousKernel, send, receive, cache, sequence, nonempty] using
              beacon_payload_admission_refines pending kernel plaintext previousKernel sendScalar
                receiveScalar cacheScalar sequenceScalar nonempty
          · simpa [previousKernel, nonempty] using beacon_plaintext_rejects pending kernel plaintext
              (.inr (Nat.le_of_not_gt nonempty))
        · simpa [previousKernel, sequence] using beacon_plaintext_rejects pending kernel plaintext
            (.inl sequence)
      · have bad : kernel.refined.control.send_sequence.val ≠ 0 ∨
            kernel.refined.control.receive_sequence.val ≠ 1 ∨
            kernel.refined.control.receive_cache.len.val ≠ 0 := by
          simpa only [not_and_or] using ready
        have rejected := beacon_kernel_rejects pending kernel (.Some plaintext) (.inr bad)
        rcases bad with send | receive | cache
        · simpa [send] using rejected
        · simpa [receive] using rejected
        · simpa [cache] using rejected

/-- Initial sealing uses the same eight-byte ID prefix and application, complete AD, selected sender/target and sequence one. -/
theorem server_initial_request_refines (pending : registration.ServerInitialSeal) :
    ∃ request, pending.request = ok request ∧
      request.associated_data = pending.binding.associated_data ∧ request.sequence = 1#u64 ∧
      request.sender_key_id = pending.candidate.server_identity_key_id ∧
      request.target_key_id = pending.candidate.key_id ∧
      request.plaintext.val.map TranscriptAuthParts.absSlice =
        [absBytes pending.prefix, TranscriptAuthParts.absSlice pending.application] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- Initial KDF completion derives the full LE64 prefix from the retained candidate and transfers its exact kernel only once. -/
theorem server_kdf_prefix_refines (pending : registration.ServerInitialKdf)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ (kernel : ratchet.concrete.ConcreteRatchetKernel) (bound : pqxdh.RegistrationKeyIdBinding)
        (next : registration.ServerInitialSeal),
      pqxdh.concrete.resume_initial_ratchet_kdf pending.pending response = ok kernel ∧
      pqxdh.registration_key_id_binding pending.candidate.key_id = ok bound ∧
      pending.resume (.Some response) = ok (.Ok next) ∧
      next.candidate = pending.candidate ∧ next.binding = pending.binding ∧
      next.application = pending.application ∧ next.prefix = bound.bytes ∧
      absBytes next.prefix = Pqxdh.LE64 pending.candidate.key_id.val ∧ next.kernel = .Some kernel ∧
      next.take_kernel = ok (.Some kernel, { next with kernel := .None }) := by
  obtain ⟨kernel, kernelRun⟩ :=
    BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending.pending response
  obtain ⟨bound, boundRun, boundBytes⟩ := registration_key_id_binding_abs pending.candidate.key_id
  refine ⟨kernel, bound,
    ⟨pending.candidate, pending.binding, pending.application, bound.bytes, .Some kernel⟩,
    kernelRun, boundRun, ?_, rfl, rfl, rfl, rfl, boundBytes, rfl, rfl⟩
  simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate, kernelRun,
    pqxdh.ServerRegistrationCandidate.key_id_binding, pqxdh.RegistrationKeyIdBinding.as_bytes, boundRun]

/-- A changed complete owner pin rejects before candidate initialization and returns the current caller control. -/
theorem server_owner_rejects (control : pqxdh.ServerState)
    (current : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8)
    (changed : ¬ BeaconcryptCore.Refinement.SessionBinding.sameServerPin accepted.binding.server_pin current) :
    registration.begin_server_completion control current availability accepted application = ok (.Err control) := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = ok result := ⟨_, rfl⟩
  cases empty <;> simp [registration.begin_server_completion, emptyRun,
    BeaconcryptCore.Refinement.SessionBinding.matches_server_refines, changed]

/-- The server seal continuation preserves its owner, binding and actual reply while constructing the response preimage from those same fields. -/
def serverSealRetains (before : registration.ServerInitialSeal)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (ciphertext : core.option.Option (Slice Std.U8)) :
    core.result.Result registration.ServerResponseHash pqxdh.ServerState → Prop
  | .Err previous => previous = before.candidate.previous_state
  | .Ok after => after.candidate = before.candidate ∧ after.binding = before.binding ∧
      after.kernel = kernel ∧ ciphertext = .Some after.ciphertext ∧
      authentication.build_response_prefix before.binding.init_hash
        before.candidate.server_identity_public_key before.candidate.ephemeral_public_key
        before.candidate.kem_ciphertext (UScalar.cast .U64 after.ciphertext.len) = ok after.prefix ∧
      authentication.encode_u64_le before.candidate.key_id = ok after.assigned_id

/-- Every seal reply either returns the previous control or advances the exact retained candidate/kernel/ciphertext with derived transcript fields. -/
theorem server_seal_retention_refines (self : registration.ServerInitialSeal)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume kernel sequence ciphertext = ok result ∧ serverSealRetains self kernel ciphertext result := by
  cases hkernel : self.kernel <;> simp only [registration.ServerInitialSeal.resume,
    pqxdh.server_abort_candidate, core.option.Option.is_some,
    ratchet.concrete.ConcreteRatchetKernel.send_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
    ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
    ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
    ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
    ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
    core.slice.Slice.len, rust_primitives.slice.slice_length, hkernel, bind_tc_ok]
  all_goals repeat first | split | contradiction | exact ⟨_, rfl, rfl⟩
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
  · rename_i encrypted noOverflowPlaintext noOverflowFrame correctLength
    split
    · exact ⟨_, rfl, rfl⟩
    · split
      · exact ⟨_, rfl, rfl⟩
      · obtain ⟨responsePrefix, prefixRun⟩ := BeaconcryptCore.PanicFreedom.Authentication.build_response_prefix_total
          self.binding.init_hash self.candidate.server_identity_public_key
          self.candidate.ephemeral_public_key self.candidate.kem_ciphertext
          (UScalar.cast .U64 encrypted.len)
        obtain ⟨assignedId, idRun⟩ := BeaconcryptCore.PanicFreedom.Authentication.encode_u64_le_total self.candidate.key_id
        simp [prefixRun, pqxdh.ServerRegistrationCandidate.impl.key_id, idRun, serverSealRetains]

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

/-- The actual successful seal continuation requests exactly the model response transcript, with its real ciphertext and retained request digest. -/
theorem server_seal_preimage_refines (self : registration.ServerInitialSeal)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64)
    (ciphertext : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume kernel sequence ciphertext = ok result ∧
      match result with
      | .Err previous => previous = self.candidate.previous_state
      | .Ok next => next.candidate = self.candidate ∧ next.binding = self.binding ∧
        next.kernel = kernel ∧ ciphertext = .Some next.ciphertext ∧
        ∃ request, next.request = ok request ∧ hashBytes request =
          Pqxdh.TranscriptAuth.responseTranscript (absBytes self.binding.init_hash)
            (TranscriptAuthRefinement.absResponse (serverResponseFields self.candidate next.ciphertext)) := by
  obtain ⟨result, run, retained⟩ := server_seal_retention_refines self kernel sequence ciphertext
  cases result with
  | Err previous => exact ⟨.Err previous, run, retained⟩
  | Ok next =>
    rcases retained with ⟨candidate, binding, kernelEq, ciphertextEq, prefixRun, idRun⟩
    obtain ⟨request, requestRun, requestBytes⟩ := server_hash_request_refines next
    obtain ⟨canonical, canonicalRun, canonicalBytes⟩ := TranscriptAuthRefinement.build_response_prefix_abs
      self.binding.init_hash self.candidate.server_identity_public_key self.candidate.ephemeral_public_key
      self.candidate.kem_ciphertext (UScalar.cast .U64 next.ciphertext.len)
    have prefixSame : next.prefix = canonical := by simpa using prefixRun.symm.trans canonicalRun
    obtain ⟨assigned, assignedRun, assignedBytes⟩ :=
      TranscriptAuthRefinement.encode_u64_le_abs self.candidate.key_id
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

/-- Every missing server primitive reply preserves that phase's exact previous control. -/
theorem missing_server_replies_retain_control (initial : registration.ServerInitialKdf)
    (sealing : registration.ServerInitialSeal) (hashed : registration.ServerResponseHash)
    (signing : registration.ServerResponseSigning) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (sequence : Std.U64) :
    initial.resume .None = ok (.Err initial.candidate.previous_state) ∧
    sealing.resume kernel sequence .None = ok (.Err sealing.candidate.previous_state) ∧
    hashed.resume .None = ok (.Err hashed.candidate.previous_state) ∧
    signing.resume .None = ok (.Err signing.candidate.previous_state) := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  cases previousKernel : sealing.kernel <;>
    simp [registration.ServerInitialSeal.resume, pqxdh.server_abort_candidate,
      core.option.Option.is_some, ratchet.concrete.ConcreteRatchetKernel.send_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_sequence,
      ratchet.concrete.ConcreteRatchetKernel.receive_cache_len,
      ratchet.refined.RefinedRatchet.send_sequence, ratchet.refined.RefinedRatchet.receive_sequence,
      ratchet.refined.RefinedRatchet.receive_cache_len, ratchet.control.RatchetState.impl.send_sequence,
      ratchet.control.RatchetState.impl.receive_sequence, ratchet.control.RatchetState.receive_cache_len,
      previousKernel]

/-- Beacon initialization transfers the kernel produced by the actual KDF continuation and retains the complete agreement or its abort ID. -/
theorem beacon_kdf_continuity_refines (pending : registration.BeaconInitialKdf)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ (kernel : ratchet.concrete.ConcreteRatchetKernel) (next : registration.BeaconInitialOpen),
      pqxdh.concrete.resume_initial_ratchet_kdf pending.pending response = ok kernel ∧
      pending.resume (.Some response) = ok (.Ok next) ∧ next.agreement = pending.agreement ∧
      next.kernel = .Some kernel ∧ next.take_kernel = ok (.Some kernel, { next with kernel := .None }) ∧
      pending.resume .None = ok (.Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  obtain ⟨kernel, kernelRun⟩ :=
    BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending.pending response
  refine ⟨kernel, ⟨pending.agreement, .Some kernel⟩, kernelRun, ?_, rfl, rfl, rfl, rfl⟩
  simp [registration.BeaconInitialKdf.resume, kernelRun]

/-- Empty application data returns the exact current control before owner preparation or initial KDF setup. -/
theorem server_empty_application_rejects (control : pqxdh.ServerState)
    (current : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (accepted : agreement.ServerAgreement) (application : Slice Std.U8) (empty : application.val = []) :
    registration.begin_server_completion control current availability accepted application = ok (.Err control) := by
  simp [registration.begin_server_completion, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, Slice.len, empty]

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

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_initial_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_initial_request_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_missing_payload_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_missing_payload_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_payload_admission_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_payload_admission_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_kernel_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_kernel_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_plaintext_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_plaintext_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_completion_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_completion_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_initial_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_initial_request_refines

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

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_kdf_prefix_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_kdf_prefix_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_owner_rejects

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_hash_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_hash_request_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_seal_preimage_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_seal_preimage_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.missing_server_replies_retain_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.missing_server_replies_retain_control

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.beacon_kdf_continuity_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.beacon_kdf_continuity_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublication.server_empty_application_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublication.server_empty_application_rejects
