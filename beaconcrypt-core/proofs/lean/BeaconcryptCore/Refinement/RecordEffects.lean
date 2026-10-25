-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RecordEffectsComposition
import BeaconcryptCore.Refinement.PqxdhCommitment
import BeaconcryptCore.Refinement.RatchetEffect

/-! Byte and transaction specifications for the extracted record controller. Primitive results remain explicit replies; the core selects requests, retains capabilities and publishes exact results. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RecordEffects

/-- The commitment request contains the exact retained AEAD transcript in the existing CTX byte model. -/
theorem seal_aead_supplied_exact (pending : record_effects.SealAead) (ciphertext : Slice Std.U8)
    (tag : Std.Array Std.U8 16#usize) :
    ∃ next : record_effects.SealCommitment,
      pending.resume (.Some (ciphertext, tag)) = ok (.CommitmentRequested next) ∧
      next.seal = pending.seal ∧ next.ciphertext = ciphertext ∧ next.tag = tag ∧
      absBytes next.transcript.bytes = Pqxdh.ctxPreimage
        (absBytes pending.seal.material.key.bytes, absBytes pending.seal.material.nonce.bytes)
        ⟨absBytes pending.seal.context.associated_data, pending.seal.sequence.val,
          pending.seal.context.sender_kid.val⟩ (absBytes tag) := by
  obtain ⟨transcript, transcriptRun, transcriptBytes⟩ := build_commitment_transcript_abs
    pending.seal.material.key.bytes pending.seal.material.nonce.bytes
    pending.seal.context.associated_data tag pending.seal.sequence pending.seal.context.sender_kid
  refine ⟨⟨pending.seal, ciphertext, tag, transcript⟩, ?_, rfl, rfl, rfl, transcriptBytes⟩
  simp only [record_effects.SealAead.resume, ratchet.concrete.SendSeal.impl.material,
    ratchet.concrete.SendSeal.impl.context, ratchet.concrete.SendSeal.impl.sequence,
    ratchet.RatchetMaterial.impl.key, ratchet.RatchetMaterial.impl.nonce,
    ratchet.RatchetKey.as_bytes, ratchet.RatchetNonce.as_bytes, bind_tc_ok]
  dsimp! only
  simp only [transcriptRun, bind_tc_ok]

/-- A rejected seal returns the exact already-advanced send kernel and no output. -/
theorem reject_send_exact (pending : ratchet.concrete.SendSeal record_effects.SealFrameContext) :
    record_effects.reject_send pending = ok (pending.advanced, .None) :=
  ratchet.concrete.SendSeal.finish_returns_interpreter_result pending
    (.None : core.option.Option Unit)

/-- AEAD failure keeps the send advance and emits no commitment or writer capability. -/
theorem seal_aead_missing_exact (pending : record_effects.SealAead) :
    pending.resume .None = ok (.Rejected pending.seal.advanced) := by
  simp only [record_effects.SealAead.resume, reject_send_exact, bind_tc_ok]
  rfl

/-- Commitment failure also keeps exactly the already-advanced send kernel. -/
theorem seal_commitment_missing_exact (pending : record_effects.SealCommitment) :
    pending.resume .None = ok (.Rejected pending.seal.advanced) := by
  simp only [record_effects.SealCommitment.resume, reject_send_exact, bind_tc_ok]
  rfl

/-- A supplied commitment preserves the exact ciphertext, tag and selected send capability. -/
theorem seal_commitment_supplied_exact (pending : record_effects.SealCommitment)
    (commitment : Std.Array Std.U8 64#usize) :
    pending.resume (.Some commitment) =
      ok (.WriteRequested ⟨pending.seal, pending.ciphertext, pending.tag, commitment⟩) := rfl

/-- Every writer outcome publishes the same advanced kernel; successful output carries exact target and sequence. -/
theorem seal_write_finish_exact {Output : Type} (pending : record_effects.SealWrite)
    (written : core.option.Option Output) :
    pending.finish written = ok (pending.seal.advanced,
      match written with
      | .None => .None
      | .Some ciphertext => .Some ({
          ciphertext, key_id := pending.seal.context.target_kid,
          seq := pending.seal.sequence } : record_effects.SealedRecord Output)) := by
  cases written <;> simp only [record_effects.SealWrite.finish,
    ratchet.concrete.SendSeal.impl.context, ratchet.concrete.SendSeal.impl.sequence,
    ratchet.concrete.SendSeal.finish_returns_interpreter_result, bind_tc_ok]

end BeaconcryptCore.Refinement.RecordEffects

/-- info: 'BeaconcryptCore.Refinement.RecordEffects.seal_aead_supplied_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.seal_aead_supplied_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffects.reject_send_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.reject_send_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.seal_aead_missing_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.seal_commitment_missing_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffects.seal_commitment_supplied_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.seal_commitment_supplied_exact
/-- info: 'BeaconcryptCore.Refinement.RecordEffects.seal_write_finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RecordEffects.seal_write_finish_exact
