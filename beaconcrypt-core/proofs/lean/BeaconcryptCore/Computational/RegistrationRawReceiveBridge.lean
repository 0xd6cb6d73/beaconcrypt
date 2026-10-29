-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationPostRootServices
import BeaconcryptCore.Computational.RawCtxOwnerResult

/-!
The Beacon's initial record service exposes typed optional hash and plaintext replies to the existing source receive program. The actual registration continuation supplies the populated binding before record admission; the final plaintext/assigned-ID gate remains explicit. Native plaintext representation is retained at the primitive boundary, so an absent or unrepresentable reply cannot become a successful registration.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationRawReceiveBridge

abbrev PrimitiveSpec :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) +
    ((Pqxdh.Bytes →ₒ core.option.Option (Std.Array Std.U8 64#usize)) +
      (RawCtxSourceOpen.BaseInput →ₒ core.option.Option (Slice Std.U8)))

abbrev Spec := RegistrationRecordPrimitives.Spec + PrimitiveSpec

def nativeAdapter : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp Spec)
  | .ratchetKdf request => do
      let response ← Spec.query (.inr (.inl request))
      pure (.Some response)
  | .hash transcript => Spec.query (.inr (.inr (.inl (absBytes transcript.bytes))))
  | .openAead request => Spec.query (.inr (.inr (.inr (RegistrationRecordPrimitives.openInput request))))
  | request => Spec.query (.inl request)

def modelAdapter : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp Spec)
  | .inl request => Spec.query (.inr (.inl request))
  | .inr (.inl bytes) => do
      let digest ← Spec.query (.inr (.inr (.inl bytes)))
      pure ((RegistrationRawSealBridge.toOption digest).map absBytes)
  | .inr (.inr input) => do
      let plaintext ← Spec.query (.inr (.inr (.inr input)))
      pure ((RegistrationRawSealBridge.toOption plaintext).map TranscriptAuthParts.absSlice)

def mapOpened (opened : record.OpenedRecord (Slice Std.U8)) : record.OpenedRecord Pqxdh.Bytes :=
  ⟨TranscriptAuthParts.absSlice opened.plaintext, opened.key_id, opened.seq⟩

theorem finish_map (pending : record_effects.RecordReceiveAead) (sequence : Std.U64)
    (sequenceRun : pending.pending.opening.sequence = .ok sequence)
    (plaintext : core.option.Option (Slice Std.U8)) :
    pending.finish (RawCtxOwnerResult.mapReply TranscriptAuthParts.absSlice plaintext) = (do
      let result ← pending.finish plaintext
      .ok (result.1, RawCtxOwnerResult.mapReply mapOpened result.2)) := by
  cases plaintext with
  | none =>
      simpa only [record_effects.RecordReceiveAead.finish, record.OpenAead.finish,
        RawCtxOwnerResult.mapReply] using
        (RawCtxOwnerResult.finish_map pending.pending.opening
          (.None : core.option.Option (record.OpenedRecord (Slice Std.U8))) mapOpened)
  | some bytes =>
      simpa only [record_effects.RecordReceiveAead.finish, record.OpenAead.finish,
        RawCtxOwnerResult.mapReply, ReceiveOpen.impl.context, sequenceRun, bind_tc_ok, mapOpened] using
        (RawCtxOwnerResult.finish_map pending.pending.opening
          (.Some ⟨bytes, pending.pending.opening.context.sender_kid, sequence⟩) mapOpened)

def completed (agreement : agreement.BeaconAgreement) (kernel : ConcreteRatchetKernel) (plaintext : Slice Std.U8) :
    registration.CompletedBeacon :=
  ⟨⟨agreement.candidate.server_binding, agreement.candidate.assigned_key_id⟩,
    BeaconcryptCore.Refinement.RegistrationPublication.completedBinding agreement.binding agreement.candidate.assigned_key_id,
    kernel, plaintext.drop 8#usize⟩

def finishAdmission (agreement : agreement.BeaconAgreement) (received : RecordEffectsReceiveProgram.Result) :
    RustM RegistrationBeaconRecordExecutor.Result :=
  match received.2 with
  | .None => .ok (.Err ⟨agreement.candidate.server_binding.identity_key_id⟩)
  | .Some opened =>
      match RegistrationAuthenticationShared.openedBytes (some opened.plaintext) with
      | .None => .ok (.Err ⟨agreement.candidate.server_binding.identity_key_id⟩)
      | .Some plaintext =>
          if opened.keyId = agreement.candidate.server_binding.identity_key_id ∧ opened.sequence = 1#u64 ∧
              8 < plaintext.val.length ∧ (plaintext.val.take 8).map absByte =
                Pqxdh.LE64 agreement.candidate.assigned_key_id.val then
            .ok (.Ok (completed agreement received.1 plaintext))
          else .ok (.Err ⟨agreement.candidate.server_binding.identity_key_id⟩)

/-- The native final gate and the source byte result retain the same kernel and both failure/success outcomes for every represented primitive reply. -/
theorem admission_exact (pending : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8))
    (origin : BeaconPhaseMetadata pending.agreement (.AeadRequested pending)) :
    ∃ kernel,
      (do
        let received ← pending.pending.finish (RawCtxOwnerResult.mapReply TranscriptAuthParts.absSlice plaintext)
        .ok (received.1, RawCtxOwnerResult.mapReply RecordEffectsReceiveProgram.decryptedOf received.2)) =
          .ok (kernel, match plaintext with
            | .None => .None
            | .Some bytes => .Some ⟨TranscriptAuthParts.absSlice bytes,
                pending.agreement.candidate.server_binding.identity_key_id, 1#u64⟩) ∧
      pending.finish plaintext = finishAdmission pending.agreement (kernel, match plaintext with
        | .None => .None
        | .Some bytes => .Some ⟨TranscriptAuthParts.absSlice bytes,
            pending.agreement.candidate.server_binding.identity_key_id, 1#u64⟩) := by
  obtain ⟨sender, _ad, sequenceRun⟩ :=
    BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.aead_metadata_fields
      pending.agreement.candidate.server_binding.identity_key_id 1#u64 pending.agreement.binding.associated_data
      pending.agreement.application_ciphertext pending.pending origin.2
  obtain ⟨kernel, _ad, finished, admitted⟩ := beacon_reachable_completion_refines pending plaintext origin
  refine ⟨kernel, ?_, ?_⟩
  · rw [finish_map pending.pending 1#u64 sequenceRun, finished]
    cases plaintext <;> rfl
  · rw [admitted]
    cases plaintext with
    | none => rfl
    | some bytes =>
        simp only [finishAdmission, RegistrationRawSealBridge.opened_roundtrip, completed, completedBeacon,
          true_and]
        split_ifs <;> rfl

def finishModel (agreement : agreement.BeaconAgreement) : RustM RecordEffectsReceiveProgram.Result →
    RustM RegistrationBeaconRecordExecutor.Result
  | .ok received => finishAdmission agreement received
  | .fail error => .fail error
  | .div => .div

def finishSource (pending : record_effects.RecordReceiveAead) (plaintext : core.option.Option Pqxdh.Bytes) :
    RustM RecordEffectsReceiveProgram.Result := do
  let received ← pending.finish plaintext
  .ok (received.1, RawCtxOwnerResult.mapReply RecordEffectsReceiveProgram.decryptedOf received.2)

private theorem bind_result_pure {Domain Input Output : Type} {oracle : OracleSpec Domain}
    (result : RustM Input) (next : Input → RustM Output) :
    RawCtxInterpretedOpening.bindResult result (fun value => (pure (next value) : OracleComp oracle _)) =
      pure (result >>= next) := by
  cases result <;> rfl

theorem source_aead_program (pending : record_effects.RecordReceiveAead) :
    RecordEffectsReceiveProgram.executeAead pending =
      RawCtxInterpretedOpening.bindResult pending.request (fun request => do
        let plaintext ← match request with
          | .None => pure core.option.Option.None
          | .Some request => RawCtxSourceOpen.OpenSpec.query (.inr (RecordEffectsReceiveProgram.aeadQuery request))
        pure (finishSource pending plaintext)) := by
  simp only [RecordEffectsReceiveProgram.executeAead]
  apply congrArg (RawCtxInterpretedOpening.bindResult pending.request)
  funext request
  cases request <;> apply bind_congr <;> intro plaintext <;> exact bind_result_pure _ _

def model (erased : Std.Array Std.U8 357#usize) (agreement : agreement.BeaconAgreement)
    (effect : record_effects.RecordReceiveEffect) : OracleComp Spec (RustM RegistrationBeaconRecordExecutor.Result) :=
  finishModel agreement <$> simulateQ modelAdapter (RecordEffectsReceiveProgram.execute erased effect)

def normalized (agreement : agreement.BeaconAgreement) (effect : record_effects.RecordReceiveEffect) :
    OracleComp Spec (RustM RegistrationBeaconRecordExecutor.Result) :=
  simulateQ nativeAdapter (match registration.normalize_beacon_open agreement effect with
  | .ok (.Ok phase) => RegistrationBeaconRecordExecutor.program phase
  | .ok (.Err aborted) => pure (.ok (.Err aborted))
  | .fail error => pure (.fail error)
  | .div => pure .div)

theorem aead_exact (pending : registration.BeaconRecordAead)
    (origin : BeaconPhaseMetadata pending.agreement (.AeadRequested pending)) :
    simulateQ nativeAdapter (RegistrationBeaconRecordExecutor.program (.AeadRequested pending)) =
      finishModel pending.agreement <$> simulateQ (modelAdapter ∘ₛ RawCtxSourceOpen.openLift)
        (RecordEffectsReceiveProgram.executeAead pending.pending) := by
  obtain ⟨request, requested⟩ :=
    BeaconcryptCore.PanicFreedom.RecordEffects.RecordReceiveAead_request_total pending.pending
  rw [RegistrationBeaconRecordExecutor.program.eq_def, source_aead_program]
  simp only [registration.BeaconRecordAead.request, requested,
    RegistrationBeaconRecordExecutor.continueWith, RawCtxInterpretedOpening.bindResult]
  cases request with
  | none =>
      obtain ⟨kernel, finished, admitted⟩ := admission_exact pending .None origin
      change finishSource pending.pending .None = RustM.ok (kernel, .None) at finished
      simp only [simulateQ_pure, pure_bind, map_pure, finished, finishModel]
      exact congrArg pure admitted
  | some request =>
      simp only [simulateQ_bind, simulateQ_spec_query, nativeAdapter, QueryImpl.apply_compose,
        RawCtxSourceOpen.openLift, modelAdapter, bind_assoc, pure_bind, map_bind,
        RegistrationRecordPrimitives.openInput, RecordEffectsReceiveProgram.aeadQuery]
      apply bind_congr
      intro plaintext
      obtain ⟨kernel, finished, admitted⟩ := admission_exact pending plaintext origin
      cases plaintext with
      | none =>
          change finishSource pending.pending .None = RustM.ok (kernel, .None) at finished
          simp only [RegistrationRawSealBridge.toOption, Option.map_none, simulateQ_pure,
            map_pure, finished, finishModel]
          exact congrArg pure admitted
      | some bytes =>
          change finishSource pending.pending (.Some (TranscriptAuthParts.absSlice bytes)) =
            RustM.ok (kernel, .Some ⟨TranscriptAuthParts.absSlice bytes,
              pending.agreement.candidate.server_binding.identity_key_id, 1#u64⟩) at finished
          simp only [RegistrationRawSealBridge.toOption, Option.map_some, simulateQ_pure,
            map_pure, finished, finishModel]
          exact congrArg pure admitted

theorem commitment_exact (erased : Std.Array Std.U8 357#usize) (pending : registration.BeaconRecordCommitment)
    (origin : BeaconPhaseMetadata pending.agreement (.CommitmentRequested pending)) :
    simulateQ nativeAdapter (RegistrationBeaconRecordExecutor.program (.CommitmentRequested pending)) =
      finishModel pending.agreement <$> simulateQ (modelAdapter ∘ₛ RawCtxSourceOpen.openLift)
        (RecordEffectsReceiveProgram.executeCommitment erased pending.pending) := by
  rw [RegistrationBeaconRecordExecutor.program.eq_def]
  simp only [
    registration.BeaconRecordCommitment.transcript, record_effects.RecordReceiveCommitment.transcript,
    record.OpenCommitment.impl.transcript, RegistrationBeaconRecordExecutor.continueWith,
    RecordEffectsReceiveProgram.executeCommitment, commitment.CommitmentTranscript.as_bytes,
    RawCtxInterpretedOpening.bindResult, simulateQ_bind, simulateQ_spec_query, nativeAdapter,
    QueryImpl.apply_compose, RawCtxSourceOpen.openLift, modelAdapter, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro digest
  have openingOrigin : BeaconPhaseMetadata pending.agreement
      (.AeadRequested ⟨pending.agreement, ⟨⟨pending.pending.pending.opening⟩⟩⟩) := ⟨rfl, origin.2⟩
  cases digest with
  | none =>
      simp only [registration.BeaconRecordCommitment.supplied_commitment,
        record_effects.RecordReceiveCommitment.supplied_commitment, record.OpenCommitment.supplied_commitment,
        ReceiveOpen.impl.context, bind_tc_ok, RegistrationBeaconRecordExecutor.commitmentMatches,
        registration.BeaconRecordCommitment.resume, record_effects.RecordReceiveCommitment.transcript_mut,
        commitment.CommitmentTranscript.as_mut_bytes,
        RegistrationRawSealBridge.toOption, Option.map_none, RecordEffectsReceiveProgram.compareDigest,
        record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume, Bool.false_eq_true, ite_false,
        ReceiveOpen.reject, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate]
      rfl
  | some digest =>
      simp only [registration.BeaconRecordCommitment.supplied_commitment,
        record_effects.RecordReceiveCommitment.supplied_commitment, record.OpenCommitment.supplied_commitment,
        ReceiveOpen.impl.context, bind_tc_ok, RegistrationBeaconRecordExecutor.commitmentMatches,
        registration.BeaconRecordCommitment.resume, record_effects.RecordReceiveCommitment.transcript_mut,
        commitment.CommitmentTranscript.as_mut_bytes,
        RegistrationRawSealBridge.toOption, Option.map_some, RecordEffectsReceiveProgram.compareDigest]
      generalize matchedRun : decide (absBytes digest =
        absBytes pending.pending.pending.opening.context.commitment) = matched
      cases matched with
      | false =>
          simp only [record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume,
            Bool.false_eq_true, ite_false, ReceiveOpen.reject, bind_tc_ok,
            registration.normalize_beacon_open, pqxdh.beacon_abort_candidate]
          rfl
      | true =>
          simp only [record_effects.RecordReceiveCommitment.resume, record.OpenCommitment.resume,
            ite_true, bind_tc_ok, registration.normalize_beacon_open]
          exact aead_exact _ openingOrigin

theorem normalized_exact (erased : Std.Array Std.U8 357#usize) (agreement : agreement.BeaconAgreement)
    (effect : record_effects.RecordReceiveEffect) (metadata : recordMetadata agreement effect) :
    normalized agreement effect = model erased agreement effect := by
  cases effectEq : effect with
  | Rejected kernel =>
      simp only [normalized, registration.normalize_beacon_open, pqxdh.beacon_abort_candidate, bind_tc_ok,
        model, RecordEffectsReceiveProgram.execute.eq_def, simulateQ_pure, map_pure, finishModel, finishAdmission]
  | AeadRequested pending =>
      simpa only [normalized, registration.normalize_beacon_open, model,
        RecordEffectsReceiveProgram.execute.eq_def, QueryImpl.simulateQ_compose] using
        aead_exact (⟨agreement, pending⟩ : registration.BeaconRecordAead) ⟨rfl, by simpa only [effectEq] using metadata⟩
  | CommitmentRequested pending =>
      simpa only [normalized, registration.normalize_beacon_open, model,
        RecordEffectsReceiveProgram.execute.eq_def, QueryImpl.simulateQ_compose] using
        commitment_exact erased (⟨agreement, pending⟩ : registration.BeaconRecordCommitment)
          ⟨rfl, by simpa only [effectEq] using metadata⟩
  | KdfRequested pending =>
      change simulateQ nativeAdapter
        (RegistrationBeaconRecordExecutor.program (.KdfRequested ⟨agreement, pending⟩)) = _
      rw [RegistrationBeaconRecordExecutor.program.eq_def, model, RecordEffectsReceiveProgram.execute_kdf]
      simp only [registration.BeaconRecordKdf.request, record_effects.RecordReceiveKdf.request,
        ReceiveKdf.impl.request, RegistrationBeaconRecordExecutor.continueWith,
        simulateQ_bind, simulateQ_spec_query, nativeAdapter, modelAdapter, bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro response
      obtain ⟨next, resumed, kept⟩ :=
        BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.kdf_metadata
          agreement.candidate.server_binding.identity_key_id 1#u64 agreement.binding.associated_data
          agreement.application_ciphertext pending response (by simpa only [recordMetadata, effectEq] using metadata)
      have actualResume : (⟨agreement, pending⟩ : registration.BeaconRecordKdf).resume (.Some response) =
          registration.normalize_beacon_open agreement next := by
        simp only [beacon_kdf_reply_refines, resumed, bind_tc_ok]
      rw [actualResume]
      simp only [resumed, RawCtxInterpretedOpening.bindResult]
      have ih := normalized_exact erased agreement next kept
      cases normalizedRun : registration.normalize_beacon_open agreement next with
      | ok result => cases result <;> simpa only [normalized, model, normalizedRun] using ih
      | fail error => simpa only [normalized, model, normalizedRun] using ih
      | div => simpa only [normalized, model, normalizedRun] using ih
termination_by RecordEffectsReceiveRank.rank effect
decreasing_by simpa only [effectEq] using RecordEffectsReceiveRank.resume_decreasing pending response next resumed

noncomputable def primitiveImplementation {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl PrimitiveSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => simulateQ (MldsaSharedSource.implementation source writer) (MldsaSharedNative.recordLift (.inl request))
  | .inr (.inl bytes) => simulateQ (MldsaSharedSource.implementation source writer) (do
      let digest ← MldsaSharedNative.authLift ((), bytes)
      pure (.Some (RegistrationAuthenticationShared.digestArray digest)))
  | .inr (.inr input) => simulateQ (MldsaSharedSource.implementation source writer) (do
      let result ← MldsaSharedNative.recordLift (.inr (.inr (.inl input)))
      pure (RegistrationAuthenticationShared.openedBytes result))

noncomputable def implementation {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl Spec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)
  | .inl request => RegistrationRecordPrimitives.implementation source writer request
  | .inr request => primitiveImplementation source writer request

private theorem map_state_apply {State Input Output : Type} (mapResult : Input → Output)
    (work : StateT State ProbComp Input) (state : State) :
    (mapResult <$> work) state = Prod.map mapResult id <$> work state := by
  change (work state >>= fun result => pure (mapResult result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

theorem query_projection {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (request : RegistrationRecordPrimitives.Request) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (implementation source writer) (nativeAdapter request)).run state =
      (RegistrationRecordPrimitives.implementation source writer request).run state := by
  cases request with
  | rootKdf request => rfl
  | initialKdf request => rfl
  | ratchetKdf request => rfl
  | openAead request => rfl
  | «seal» request => rfl
  | write request => cases request <;> rfl
  | hash request =>
      rw [RegistrationRecordPrimitives.hash_exact]
      simp only [nativeAdapter, simulateQ_spec_query, implementation, primitiveImplementation,
        MldsaSharedNative.authLift, simulateQ_map, simulateQ_spec_query,
        StateT.run, map_state_apply, MldsaSharedSource.implementation,
        MldsaSharedNative.primitives, MldsaSharedNative.authentication, bind_pure_comp,
        Functor.map_map]
      rfl

theorem program_projection {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RegistrationRecordPrimitives.Spec Result) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (implementation source writer) (simulateQ nativeAdapter work)).run state =
      (simulateQ (RegistrationRecordPrimitives.implementation source writer) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_projection, ih]

end BeaconcryptCore.Computational.RegistrationRawReceiveBridge

/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.finish_map
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.admission_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.admission_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.source_aead_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.source_aead_program
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.aead_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.aead_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.commitment_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.commitment_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.normalized_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.normalized_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.query_projection
/-- info: 'BeaconcryptCore.Computational.RegistrationRawReceiveBridge.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRawReceiveBridge.program_projection
