-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPublication
import BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant

/-! Initial protected records retain source-owned metadata and kernel continuations through actual primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationPublication

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RegistrationRecords

/-- Actual optional plaintext is published with the sender and sequence of the retained receive capability. -/
theorem beacon_record_reply_refines (self : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8)) :
    ∃ (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64),
      ratchet.concrete.ReceiveOpen.sequence self.pending.pending.opening = ok sequence ∧
      self.pending.finish plaintext = ok (kernel,
        match plaintext with
        | .None => .None
        | .Some bytes => .Some (⟨bytes, self.pending.pending.opening.context.sender_kid,
            sequence⟩ : record.OpenedRecord (Slice Std.U8))) := by
  obtain ⟨_, ⟨sequence, sequenceRun⟩⟩ := NativeRecordWrapper.getters_normal self.pending.pending.opening
  obtain ⟨kernel, kernelRun⟩ := ratchet.concrete.ReceiveOpen.finish_result_exact
    self.pending.pending.opening
    (match plaintext with
     | .None => .None
     | .Some bytes => .Some (⟨bytes, self.pending.pending.opening.context.sender_kid,
         sequence⟩ : record.OpenedRecord (Slice Std.U8)))
  refine ⟨kernel, sequence, sequenceRun, ?_⟩
  cases plaintext <;>
    simpa only [record_effects.RecordReceiveAead.finish,
      NativeRecordWrapper.finish_selected self.pending.pending sequence sequenceRun]
      using kernelRun

/-- Successful initial admission retains the actual receive kernel and removes only the authenticated ID prefix. -/
def completedBeacon (pending : registration.BeaconRecordAead)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (plaintext : Slice Std.U8) :
    registration.CompletedBeacon :=
  ⟨⟨pending.agreement.candidate.server_binding, pending.agreement.candidate.assigned_key_id⟩,
    completedBinding pending.agreement.binding pending.agreement.candidate.assigned_key_id,
    kernel, plaintext.drop 8#usize⟩

/-- The complete admitted plaintext checks its actual source-owned sender, all ID bytes and a nonempty suffix. -/
theorem beacon_payload_admission_refines (pending : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (opened : record.OpenedRecord (Slice Std.U8))
    (source : pending.pending.finish plaintext = ok (kernel, .Some opened))
    (nonempty : 8 < opened.plaintext.val.length) :
    pending.finish plaintext = ok
      (if opened.key_id = pending.agreement.candidate.server_binding.identity_key_id ∧
          (opened.plaintext.val.take 8).map absByte =
            Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
        then .Ok (completedBeacon pending kernel opened.plaintext)
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
    by_cases sender : opened.key_id = pending.agreement.candidate.server_binding.identity_key_id <;>
      by_cases bytes : (opened.plaintext.val.map absByte).take 8 =
        Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
    all_goals simp [registration.BeaconRecordAead.finish,
      pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new, source,
      core.slice.Slice.len, rust_primitives.slice.slice_length,
      Nat.not_le.mpr longEnough, splitRun, convertedRun, pqxdh.authenticate_registration_key_id_binding,
      pqxdh.BeaconRegistrationCandidate.key_id_binding, expectedRun, array_eq_abs,
      boundBytes, expectedBytes, sender, bytes, pqxdh.AuthenticatedBeaconRegistration.assigned_key_id,
      session.RegistrationBinding.finish, pqxdh.beacon_commit, completedBeacon, completedBinding,
      applicationPart]


/-- Every actual optional AEAD reply has this exact admission outcome; metadata and kernel come only from the retained record effect. -/
theorem beacon_completion_refines (pending : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8)) :
    ∃ (kernel : ratchet.concrete.ConcreteRatchetKernel) (sequence : Std.U64),
      ratchet.concrete.ReceiveOpen.sequence pending.pending.pending.opening = ok sequence ∧
      pending.pending.finish plaintext = ok (kernel,
        match plaintext with
        | .None => .None
        | .Some bytes => .Some (⟨bytes, pending.pending.pending.opening.context.sender_kid,
            sequence⟩ : record.OpenedRecord (Slice Std.U8))) ∧
      pending.finish plaintext = ok (match plaintext with
        | .None => .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩
        | .Some bytes =>
          if 8 < bytes.val.length ∧
              pending.pending.pending.opening.context.sender_kid =
                pending.agreement.candidate.server_binding.identity_key_id ∧
              (bytes.val.take 8).map absByte =
                Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
            then .Ok (completedBeacon pending kernel bytes)
            else .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  obtain ⟨kernel, sequence, sequenceRun, source⟩ := beacon_record_reply_refines pending plaintext
  refine ⟨kernel, sequence, sequenceRun, source, ?_⟩
  cases plaintext with
  | none => rfl
  | some bytes =>
    by_cases nonempty : 8 < bytes.val.length
    · simpa only [nonempty, true_and] using
        beacon_payload_admission_refines pending (.Some bytes) kernel
          ⟨bytes, pending.pending.pending.opening.context.sender_kid, sequence⟩ source nonempty
    · have short : bytes.val.length ≤ 8 := Nat.le_of_not_gt nonempty
      simp [registration.BeaconRecordAead.finish, pqxdh.BeaconRegistrationCandidate.server_key_id,
        pqxdh.BeaconAborted.new, source, core.slice.Slice.len, rust_primitives.slice.slice_length,
        pqxdh.REGISTRATION_KEY_ID_BINDING_SIZE, short, nonempty]

/-- The actual initial KDF continuation enters record receive with implicit sequence one, exact authenticated ciphertext, complete AD and pinned sender. -/
theorem beacon_initial_request_refines (pending : registration.BeaconInitialKdf)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    pending.resume (.Some response) = (do
      let kernel ← pqxdh.concrete.resume_initial_ratchet_kdf pending.pending response
      let effect ← record_effects.begin_record_receive kernel 1#u64
        pending.agreement.application_ciphertext pending.agreement.binding.associated_data
        pending.agreement.candidate.server_binding.identity_key_id
      registration.normalize_beacon_open pending.agreement effect) := rfl

/-- The actual record KDF reply resumes the same capability before retaining the same agreement in its next phase. -/
theorem beacon_kdf_reply_refines (pending : registration.BeaconRecordKdf)
    (response : ratchet.RatchetKdfResponse) :
    pending.resume (.Some response) = (do
      let effect ← record_effects.RecordReceiveKdf.resume pending.pending response
      registration.normalize_beacon_open pending.agreement effect) := rfl

/-- The actual commitment comparison resumes the retained record effect before any AEAD phase is published. -/
theorem beacon_commitment_reply_refines (pending : registration.BeaconRecordCommitment)
    (matched : Bool) :
    pending.resume matched = (do
      let effect ← record_effects.RecordReceiveCommitment.resume pending.pending matched
      registration.normalize_beacon_open pending.agreement effect) := rfl

/-- Erasing the commitment transcript preserves the complete agreement and the selected record opening. -/
theorem beacon_commitment_transcript_lens_refines (pending : registration.BeaconRecordCommitment) :
    ∃ transcript back, pending.transcript_mut = ok (transcript, back) ∧
      transcript = pending.pending.pending.transcript ∧
      ∀ changed, (back changed).agreement = pending.agreement ∧
        (back changed).pending.pending.opening = pending.pending.pending.opening :=
  ⟨_, _, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Server hash-transcript erasure preserves the retained candidate, binding, selected kernel, ciphertext and tag. -/
theorem server_commitment_transcript_lens_refines (pending : registration.ServerRecordCommitment) :
    ∃ transcript back, pending.transcript_mut = ok (transcript, back) ∧
      transcript = pending.pending.transcript ∧
      ∀ changed, (back changed).state = pending.state ∧
        (back changed).pending.seal = pending.pending.seal ∧
        (back changed).pending.ciphertext = pending.pending.ciphertext ∧
        (back changed).pending.tag = pending.pending.tag :=
  ⟨_, _, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- Every missing server primitive or writer reply returns that exact phase's previous control. -/
theorem missing_server_replies_retain_control (initial : registration.ServerInitialKdf)
    (step : registration.ServerInitialSeal) (aead : registration.ServerRecordAead)
    (commitment1 : registration.ServerRecordCommitment) (written : registration.ServerRecordWrite)
    (hashed : registration.ServerResponseHash) (signing : registration.ServerResponseSigning) :
    initial.resume .None = ok (.Err initial.candidate.previous_state) ∧
    step.resume .None = ok (.Err step.state.candidate.previous_state) ∧
    aead.resume .None = ok (.Err aead.state.candidate.previous_state) ∧
    commitment1.resume .None = ok (.Err commitment1.state.candidate.previous_state) ∧
    written.resume .None = ok (.Err written.state.candidate.previous_state) ∧
    hashed.resume .None = ok (.Err hashed.candidate.previous_state) ∧
    signing.resume .None = ok (.Err signing.candidate.previous_state) := by
  simp [registration.ServerInitialKdf.resume, registration.ServerInitialSeal.resume,
    registration.ServerRecordAead.resume, registration.ServerRecordCommitment.resume,
    registration.ServerRecordWrite.resume, registration.ServerResponseHash.resume,
    registration.ServerResponseSigning.resume, RecordEffects.seal_aead_missing_exact,
    RecordEffects.seal_commitment_missing_exact, RecordEffects.seal_write_finish_exact,
    pqxdh.server_abort_candidate]

/-- Every actual initial KDF response constructs a fresh kernel; no counter or receive cache can be supplied by the interpreter. -/
theorem initial_kernel_control_refines (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ kernel, pqxdh.concrete.resume_initial_ratchet_kdf pending response = ok kernel ∧
      kernel.refined.control.send_sequence = 0#u64 ∧
      kernel.refined.control.receive_sequence = 0#u64 ∧
      kernel.refined.control.receive_cache.len = 0#u8 := by
  obtain ⟨chains, chainsRun⟩ := BeaconcryptCore.PanicFreedom.split_initial_ratchet_kdf_output_ok
    response.bytes pending.initialization
  simp [pqxdh.concrete.resume_initial_ratchet_kdf,
    pqxdh.concrete.InitialRatchetKdfResponse.as_bytes, chainsRun, pqxdh.InitialRatchetChains.into_parts,
    ratchet.concrete.ConcreteRatchetKernel.new, ratchet.concrete.ConcreteRatchetKernel.from_counters,
    ratchet.refined.RefinedRatchet.from_counters, ratchet.control.RatchetState.from_counters,
    ratchet.control.SequenceCache.empty, ratchet.refined.empty_material_slots]

/-- Exact source-owned initial seal context, including the entire populated AD and LE64 prefix. -/
def serverRecordContext (pending : registration.ServerInitialKdf) (bound : pqxdh.RegistrationKeyIdBinding) :
    record_effects.SealFrameContext :=
  ⟨pending.application, .Some bound.bytes, pending.binding.associated_data,
    pending.candidate.key_id, pending.candidate.server_identity_key_id, .Raw⟩

/-- The actual initial KDF constructs sequence one and the exact prefix/context before handing out the first record KDF request. -/
theorem server_kdf_prefix_refines (pending : registration.ServerInitialKdf)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ (kernel : ratchet.concrete.ConcreteRatchetKernel) (bound : pqxdh.RegistrationKeyIdBinding)
        (next : registration.ServerInitialSeal),
      pqxdh.concrete.resume_initial_ratchet_kdf pending.pending response = ok kernel ∧
      pqxdh.registration_key_id_binding pending.candidate.key_id = ok bound ∧
      absBytes bound.bytes = Pqxdh.LE64 pending.candidate.key_id.val ∧
      pending.resume (.Some response) = ok (.Ok next) ∧
      next.state = ⟨pending.candidate, pending.binding, pending.application⟩ ∧
      next.pending.pending.entry = kernel ∧
      next.pending.pending.context = serverRecordContext pending bound ∧
      next.pending.pending.sequence.val = 1 ∧
      next.request = ok next.pending.pending.request ∧
      next.pending.pending.request.input = kernel.refined.send_chain.bytes ∧
      next.pending.pending.request.info = ratchet.SYM_RATCHET_INFO := by
  obtain ⟨kernel, kernelRun, sendZero, receiveZero, cacheZero⟩ :=
    initial_kernel_control_refines pending.pending response
  obtain ⟨bound, boundRun, boundBytes⟩ := registration_key_id_binding_abs pending.candidate.key_id
  let context := serverRecordContext pending bound
  have contextRun : record_effects.SealFrameContext.registration pending.application
      pending.candidate.key_id pending.candidate.server_identity_key_id pending.binding.associated_data = ok context := by
    simp [record_effects.SealFrameContext.registration, boundRun,
      pqxdh.RegistrationKeyIdBinding.as_bytes, context, serverRecordContext]
  have nonmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX := by
    rw [sendZero]
    decide
  obtain ⟨selected, selectedRun, entry, retainedContext, input, info, sequence⟩ :=
    ratchet.concrete.begin_send_nonexhausted_exact kernel context nonmax
  have recordRun : record_effects.begin_record_send kernel context = ok (.KdfRequested ⟨selected⟩) := by
    have prefixRun : context.prefix = .Some bound.bytes := rfl
    obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty context.plaintext = ok result := ⟨_, rfl⟩
    cases empty with
    | false => simp [record_effects.begin_record_send, emptyRun, selectedRun]
    | true => simp [record_effects.begin_record_send, emptyRun, prefixRun,
        core.option.Option.is_none, core.option.Option.is_some, selectedRun]
  let next : registration.ServerInitialSeal :=
    ⟨⟨pending.candidate, pending.binding, pending.application⟩, ⟨selected⟩⟩
  refine ⟨kernel, bound, next, kernelRun, boundRun, boundBytes, ?_, rfl,
    entry, retainedContext, ?_, rfl, input, info⟩
  · simp [registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate,
      kernelRun, pqxdh.ServerRegistrationCandidate.impl.key_id,
      pqxdh.ServerRegistrationCandidate.impl.server_identity_key_id,
      session.RegistrationBinding.impl.associated_data, contextRun, recordRun, next]
  · simpa [sendZero] using sequence

/-- The actual first record KDF reply retains the initial context and sequence while selecting its own material and advanced kernel. -/
theorem server_step_kdf_refines (pending : registration.ServerInitialSeal)
    (response : ratchet.RatchetKdfResponse) :
    ∃ next : registration.ServerRecordAead,
      pending.resume (.Some response) = ok (.Ok next) ∧ next.state = pending.state ∧
      next.pending.seal.context = pending.pending.pending.context ∧
      next.pending.seal.sequence = pending.pending.pending.sequence ∧
      next.pending.seal.advanced.refined.control = pending.pending.pending.committed_control := by
  obtain ⟨stepped, stepRun⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
  simp [registration.ServerInitialSeal.resume, record_effects.RecordSendKdf.resume,
    ratchet.concrete.SendKdf.resume, stepRun]

/-- The actual detached AEAD reply supplies the retained ciphertext/tag and exact source-owned CTX preimage. -/
theorem server_aead_reply_refines (pending : registration.ServerRecordAead)
    (ciphertext : Slice Std.U8) (tag : Std.Array Std.U8 16#usize) :
    ∃ next : registration.ServerRecordCommitment,
      pending.resume (.Some (ciphertext, tag)) = ok (.Ok next) ∧ next.state = pending.state ∧
      next.pending.seal = pending.pending.seal ∧ next.pending.ciphertext = ciphertext ∧ next.pending.tag = tag ∧
      absBytes next.pending.transcript.bytes = Pqxdh.ctxPreimage
        (absBytes pending.pending.seal.material.key.bytes, absBytes pending.pending.seal.material.nonce.bytes)
        ⟨absBytes pending.pending.seal.context.associated_data, pending.pending.seal.sequence.val,
          pending.pending.seal.context.sender_kid.val⟩ (absBytes tag) := by
  obtain ⟨next, nextRun, retained, actualCiphertext, actualTag, transcript⟩ :=
    RecordEffects.seal_aead_supplied_exact pending.pending ciphertext tag
  exact ⟨⟨pending.state, next⟩, by
    simp only [registration.ServerRecordAead.resume, nextRun, bind_tc_ok],
    rfl, retained, actualCiphertext, actualTag, transcript⟩

/-- A supplied commitment preserves the same state, selected seal capability and exact detached AEAD result. -/
theorem server_commitment_reply_refines (pending : registration.ServerRecordCommitment)
    (commitment1 : Std.Array Std.U8 64#usize) :
    ∃ next : registration.ServerRecordWrite,
      pending.resume (.Some commitment1) = ok (.Ok next) ∧ next.state = pending.state ∧
      next.pending.seal = pending.pending.seal ∧ next.pending.ciphertext = pending.pending.ciphertext ∧
      next.pending.tag = pending.pending.tag ∧ next.pending.commitment = commitment1 :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Metadata of the actual record operation selected by this retained registration agreement. -/
def recordMetadata (expected : agreement.BeaconAgreement) (effect : record_effects.RecordReceiveEffect) : Prop :=
  RecordEffectsReceiveInvariant.RecordReceiveMetadata expected.candidate.server_binding.identity_key_id 1#u64
    expected.binding.associated_data expected.application_ciphertext effect

/-- Every live registration phase retains the same agreement and the actual record operation's admitted metadata. -/
def BeaconPhaseMetadata (expected : agreement.BeaconAgreement) : registration.BeaconInitialOpen → Prop
  | .KdfRequested pending => pending.agreement = expected ∧ recordMetadata expected (.KdfRequested pending.pending)
  | .CommitmentRequested pending => pending.agreement = expected ∧ recordMetadata expected (.CommitmentRequested pending.pending)
  | .AeadRequested pending => pending.agreement = expected ∧ recordMetadata expected (.AeadRequested pending.pending)

/-- Rejection returns the retained pin; a live result keeps the complete source invariant. -/
def beaconMetadataOutcome (expected : agreement.BeaconAgreement) :
    core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted → Prop
  | .Err aborted => aborted = ⟨expected.candidate.server_binding.identity_key_id⟩
  | .Ok phase => BeaconPhaseMetadata expected phase

/-- The actual registration normalizer retains both the complete agreement and admitted record metadata. -/
theorem normalize_beacon_metadata (expected : agreement.BeaconAgreement)
    (effect : record_effects.RecordReceiveEffect) (metadata : recordMetadata expected effect) :
    ∃ result, registration.normalize_beacon_open expected effect = ok result ∧
      beaconMetadataOutcome expected result := by
  cases effect with
  | Rejected kernel => exact ⟨_, rfl, rfl⟩
  | KdfRequested pending => exact ⟨_, rfl, rfl, metadata⟩
  | CommitmentRequested pending => exact ⟨_, rfl, rfl, metadata⟩
  | AeadRequested pending => exact ⟨_, rfl, rfl, metadata⟩

/-- The actual initial constructor establishes implicit sequence one, pinned sender, full AD and exact authenticated ciphertext metadata. -/
theorem beacon_initial_metadata (pending : registration.BeaconInitialKdf)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    ∃ result, pending.resume (.Some response) = ok result ∧
      beaconMetadataOutcome pending.agreement result := by
  obtain ⟨kernel, kernelRun⟩ := BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending.pending response
  obtain ⟨effect, effectRun, metadata⟩ := RecordEffectsReceiveInvariant.begin_metadata kernel
    pending.agreement.candidate.server_binding.identity_key_id 1#u64
    pending.agreement.binding.associated_data pending.agreement.application_ciphertext
  obtain ⟨result, normalized, retained⟩ := normalize_beacon_metadata pending.agreement effect metadata
  exact ⟨result, by simpa only [beacon_initial_request_refines, kernelRun, effectRun, bind_tc_ok]
    using normalized, retained⟩

/-- Every actual typed KDF reply keeps the same reachable source invariant; missing replies return the retained abort ID. -/
theorem beacon_kdf_metadata (expected : agreement.BeaconAgreement) (pending : registration.BeaconRecordKdf)
    (response : core.option.Option ratchet.RatchetKdfResponse)
    (origin : BeaconPhaseMetadata expected (.KdfRequested pending)) :
    ∃ result, pending.resume response = ok result ∧ beaconMetadataOutcome expected result := by
  rcases origin with ⟨agreementEq, metadata⟩
  subst expected
  cases response with
  | none => exact ⟨_, rfl, rfl⟩
  | some response =>
    obtain ⟨effect, effectRun, kept⟩ := RecordEffectsReceiveInvariant.kdf_metadata
      pending.agreement.candidate.server_binding.identity_key_id 1#u64
      pending.agreement.binding.associated_data pending.agreement.application_ciphertext
      pending.pending response metadata
    obtain ⟨result, normalized, retained⟩ := normalize_beacon_metadata pending.agreement effect kept
    exact ⟨result, by simpa only [beacon_kdf_reply_refines, effectRun, bind_tc_ok]
      using normalized, retained⟩

/-- Both actual comparison outcomes preserve reachable metadata whenever a live registration phase remains. -/
theorem beacon_commitment_metadata (expected : agreement.BeaconAgreement)
    (pending : registration.BeaconRecordCommitment) (matched : Bool)
    (origin : BeaconPhaseMetadata expected (.CommitmentRequested pending)) :
    ∃ result, pending.resume matched = ok result ∧ beaconMetadataOutcome expected result := by
  rcases origin with ⟨agreementEq, metadata⟩
  subst expected
  obtain ⟨effect, effectRun, kept⟩ := RecordEffectsReceiveInvariant.commitment_metadata
    pending.agreement.candidate.server_binding.identity_key_id 1#u64
    pending.agreement.binding.associated_data pending.agreement.application_ciphertext
    pending.pending matched metadata
  obtain ⟨result, normalized, retained⟩ := normalize_beacon_metadata pending.agreement effect kept
  exact ⟨result, by simpa only [beacon_commitment_reply_refines, effectRun, bind_tc_ok]
    using normalized, retained⟩

/-- The actual borrowed transcript setter preserves reachable metadata for every replacement, including secret erasure. -/
theorem beacon_transcript_metadata (expected : agreement.BeaconAgreement)
    (pending : registration.BeaconRecordCommitment)
    (origin : BeaconPhaseMetadata expected (.CommitmentRequested pending)) :
    ∃ current put, pending.transcript_mut = ok (current, put) ∧
      ∀ transcript, BeaconPhaseMetadata expected (.CommitmentRequested (put transcript)) :=
  ⟨_, _, rfl, fun _ => origin⟩

/-- The reachable core phases force sequence one and pinned sender; actual plaintext then needs only the full ID prefix and nonempty suffix admission. -/
theorem beacon_reachable_completion_refines (pending : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8))
    (origin : BeaconPhaseMetadata pending.agreement (.AeadRequested pending)) :
    ∃ kernel, pending.pending.pending.opening.context.associated_data = pending.agreement.binding.associated_data ∧
      pending.pending.finish plaintext = ok (kernel,
        match plaintext with
        | .None => .None
        | .Some bytes => .Some (⟨bytes, pending.agreement.candidate.server_binding.identity_key_id,
            1#u64⟩ : record.OpenedRecord (Slice Std.U8))) ∧
      pending.finish plaintext = ok (match plaintext with
        | .None => .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩
        | .Some bytes =>
          if 8 < bytes.val.length ∧ (bytes.val.take 8).map absByte =
              Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
            then .Ok (completedBeacon pending kernel bytes)
            else .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩) := by
  obtain ⟨sender, associatedData, selectedSequence⟩ := RecordEffectsReceiveInvariant.aead_metadata_fields
    pending.agreement.candidate.server_binding.identity_key_id 1#u64
    pending.agreement.binding.associated_data pending.agreement.application_ciphertext
    pending.pending origin.2
  obtain ⟨kernel, sequence, sequenceRun, source, completed⟩ := beacon_completion_refines pending plaintext
  have sequenceEq : sequence = 1#u64 := by simpa using sequenceRun.symm.trans selectedSequence
  refine ⟨kernel, associatedData, ?_, ?_⟩
  · cases plaintext <;> simpa [sender, sequenceEq] using source
  · cases plaintext <;> simpa [sender] using completed

end BeaconcryptCore.Refinement.RegistrationRecords

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_record_reply_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_record_reply_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_payload_admission_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_payload_admission_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_completion_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_completion_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_initial_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_initial_request_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_kdf_reply_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_kdf_reply_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_reply_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_reply_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_transcript_lens_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_transcript_lens_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.server_commitment_transcript_lens_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.server_commitment_transcript_lens_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.missing_server_replies_retain_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.missing_server_replies_retain_control

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.initial_kernel_control_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.initial_kernel_control_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.server_kdf_prefix_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.server_kdf_prefix_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.server_step_kdf_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.server_step_kdf_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.server_aead_reply_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.server_aead_reply_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.server_commitment_reply_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.server_commitment_reply_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.normalize_beacon_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.normalize_beacon_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_initial_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_initial_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_kdf_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_kdf_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_commitment_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_transcript_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_transcript_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationRecords.beacon_reachable_completion_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRecords.beacon_reachable_completion_refines
