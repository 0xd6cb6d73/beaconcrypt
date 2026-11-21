-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace

/-! Actual Server record trace fields retain the original source context and exact CTX preimage. These equations derive public binding/sequence contents from reached source resumes, independently of a private-root equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRecordFields
open RegistrationRecordPrimitives (Spec)
open RegistrationNativeServerRecordTrace (Trace)
open BeaconcryptCore.Refinement.RegistrationRecords
variable {S : Type}

/-- Forgetting states from an actual trace produces the original source path using exactly its actual replies. -/
theorem path (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (trace : Trace implementation initial completed before after) : RegistrationServerRecordExecutor.Path initial completed :=
  ⟨trace.initialReply, trace.ratchet, trace.initialResumed, trace.ratchetReply, trace.aead, trace.ratchetResumed,
    trace.aeadReply, trace.commitmentState, trace.aeadResumed, trace.digestReply, trace.writer, trace.hashResumed,
    trace.writeReply, trace.writeResumed⟩

/-- The actual selected AEAD capability has the initializer's full AD151/context and implicit sequence one. -/
theorem context (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (trace : Trace implementation initial completed before after) :
    ∃ bound, pqxdh.registration_key_id_binding initial.candidate.key_id = .ok bound ∧
      trace.aead.pending.seal.context = serverRecordContext initial bound ∧ trace.aead.pending.seal.sequence.val = 1 := by
  have initialResumed := trace.initialResumed
  cases initialChoice : trace.initialReply with
  | none => simp [initialChoice, registration.ServerInitialKdf.resume, pqxdh.server_abort_candidate] at initialResumed
  | some initialResponse =>
    rw [initialChoice] at initialResumed
    obtain ⟨kernel, bound, next, _kernelRun, boundRun, _boundBytes, resumed, _stateSame, _entry, initialContext, initialSequence, _rest⟩ :=
      server_kdf_prefix_refines initial initialResponse
    have nextEq : next = trace.ratchet := by
      simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq] using resumed.symm.trans initialResumed
    have stepResumed := trace.ratchetResumed
    cases stepChoice : trace.ratchetReply with
    | none => simp [stepChoice, registration.ServerInitialSeal.resume, pqxdh.server_abort_candidate] at stepResumed
    | some response =>
      rw [stepChoice] at stepResumed
      obtain ⟨aead, resumed, _state, stepContext, stepSequence, _control⟩ := server_step_kdf_refines trace.ratchet response
      have aeadEq : aead = trace.aead := by
        simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq] using resumed.symm.trans stepResumed
      refine ⟨bound, boundRun, ?_, ?_⟩
      · rw [← aeadEq, stepContext, ← nextEq]
        exact initialContext
      · rw [← aeadEq, stepSequence, ← nextEq]
        exact initialSequence

/-- The actually hashed commitment is the source-built preimage of the reached AEAD key, nonce, full AD, tag, sequence and sender. -/
theorem transcript (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (trace : Trace implementation initial completed before after) :
    ∃ ciphertext tag, trace.aeadReply = .Some (ciphertext, tag) ∧
      trace.commitmentState.pending.seal = trace.aead.pending.seal ∧
      trace.commitmentState.pending.ciphertext = ciphertext ∧ trace.commitmentState.pending.tag = tag ∧
      absBytes trace.transcript.bytes = Pqxdh.ctxPreimage
        (absBytes trace.aead.pending.seal.material.key.bytes, absBytes trace.aead.pending.seal.material.nonce.bytes)
        ⟨absBytes trace.aead.pending.seal.context.associated_data, trace.aead.pending.seal.sequence.val,
          trace.aead.pending.seal.context.sender_kid.val⟩ (absBytes tag) := by
  have requested := trace.hashRequested
  change (.ok trace.commitmentState.pending.transcript : RustM commitment.CommitmentTranscript) = .ok trace.transcript at requested
  have transcriptEq : trace.commitmentState.pending.transcript = trace.transcript := RustM.ok.inj requested
  have actual := trace.aeadResumed
  cases replyEq : trace.aeadReply with
  | none => simp [replyEq, registration.ServerRecordAead.resume, BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact,
      pqxdh.server_abort_candidate] at actual
  | some pair =>
    rcases pair with ⟨ciphertext, tag⟩
    rw [replyEq] at actual
    obtain ⟨next, resumed, _state, sealEq, ciphertextEq, tagEq, preimage⟩ := server_aead_reply_refines trace.aead ciphertext tag
    have nextEq : next = trace.commitmentState := by
      simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq] using resumed.symm.trans actual
    refine ⟨ciphertext, tag, rfl, ?_, ?_, ?_, ?_⟩
    · rw [← nextEq]; exact sealEq
    · rw [← nextEq]; exact ciphertextEq
    · rw [← nextEq]; exact tagEq
    · rw [← transcriptEq, ← nextEq]
      exact preimage

end BeaconcryptCore.Computational.RegistrationNativeServerRecordFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.context

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordFields.transcript
