-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields

/-! The actual checked Beacon commitment and final AEAD request use the same selected key, nonce and complete admitted context. This connects source-built transcript fields to the concrete open callback operands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.NativeRecordWrapper
open BeaconcryptCore.Refinement.CommitmentSurface
open RegistrationNativeBeaconRecordTrace (Trace)

/-- The reached AEAD request uses exactly the six fields whose actual source transcript was hashed, and the original response ciphertext body with tag. -/
theorem request {S : Type} (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (expected : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (before after : S)
    (trace : Trace implementation phase completed before after)
    (metadata : BeaconPhaseMetadata expected phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase) :
    ∃ fields : Fields, trace.transcript.bytes = productionInput fields ∧
      fields.associatedData = expected.binding.associated_data ∧ fields.sequence = 1#u64 ∧
      fields.senderId = expected.candidate.server_binding.identity_key_id ∧
      fields.tag.val = (expected.application_ciphertext.val.take (expected.application_ciphertext.val.length - 64)).drop
        (expected.application_ciphertext.val.length - 80) ∧
      trace.supplied.val = expected.application_ciphertext.val.drop (expected.application_ciphertext.val.length - 64) ∧
      trace.aeadRequest.key = fields.key ∧ trace.aeadRequest.nonce = fields.nonce ∧
      trace.aeadRequest.associated_data = fields.associatedData ∧
      trace.aeadRequest.ciphertext.val = expected.application_ciphertext.val.take (expected.application_ciphertext.val.length - 64) := by
  have kept := RegistrationNativeBeaconRecordFields.along_prefix implementation expected trace.leading metadata
  obtain ⟨material, sequence, selected, sequenced, built⟩ :=
    RegistrationNativeBeaconCommitmentGenuine.along_prefix implementation trace.leading genuine
  let current : Fields := selectedFields trace.commitmentState.pending.pending.opening material sequence
  obtain ⟨fields, encoded, ad, seq, sender, tag, supplied⟩ :=
    RegistrationNativeBeaconRecordFields.transcript implementation expected phase completed before after trace metadata genuine
  have requested := trace.hashRequested
  change (.ok trace.commitmentState.pending.pending.transcript : RustM commitment.CommitmentTranscript) = .ok trace.transcript at requested
  have currentEncoded : trace.transcript.bytes = productionInput current :=
    (congrArg commitment.CommitmentTranscript.bytes (RustM.ok.inj requested)).symm.trans built
  have fieldsEq : fields = current := production_commitment_input_is_injective (encoded.symm.trans currentEncoded)
  have resumed : trace.commitmentState.resume true = .ok (.Ok (.AeadRequested
      ⟨trace.commitmentState.agreement, ⟨⟨trace.commitmentState.pending.pending.opening⟩⟩⟩)) := rfl
  have actual := trace.hashResumed
  rw [trace.matched] at actual
  have aeadEq : trace.aead = ⟨trace.commitmentState.agreement, ⟨⟨trace.commitmentState.pending.pending.opening⟩⟩⟩ := by
    simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq, registration.BeaconInitialOpen.AeadRequested.injEq] using actual.symm.trans resumed
  have selectedRequest := request_selected ⟨trace.commitmentState.pending.pending.opening⟩ material selected
  have aeadRequested := trace.aeadRequested
  rw [aeadEq] at aeadRequested
  change record.OpenAead.request ⟨trace.commitmentState.pending.pending.opening⟩ = .ok (.Some trace.aeadRequest) at aeadRequested
  have requestEq : trace.aeadRequest = ⟨material.key.bytes, material.nonce.bytes,
      trace.commitmentState.pending.pending.opening.context.base_ciphertext,
      trace.commitmentState.pending.pending.opening.context.associated_data⟩ := by
    have same := RustM.ok.inj (aeadRequested.symm.trans selectedRequest)
    injection same
  refine ⟨fields, encoded, ad, seq, sender, tag, supplied, ?_, ?_, ?_, ?_⟩
  · rw [requestEq, fieldsEq]; rfl
  · rw [requestEq, fieldsEq]; rfl
  · rw [requestEq, fieldsEq]; rfl
  · rw [requestEq]
    exact kept.2.2.1

end BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields.request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconOpenFields.request
