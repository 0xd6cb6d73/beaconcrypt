-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRecordFields

/-! The actual Server first-record writer emits precisely the reached detached ciphertext, tag and returned commitment digest. The transcript fields and raw byte equation come from source continuations and the actual callback, without a message or root-equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRawSource
open PqxdhServerAuthExperiment (Setup Codec)
open BeaconcryptCore.Refinement.CommitmentSurface
open BeaconcryptCore.Refinement.PqxdhSurface
open BeaconcryptCore.Refinement.ProtocolComposition
open BeaconcryptCore.Refinement.RegistrationRecords
open RegistrationNativeServerRecordTrace (Trace)
variable {n : Nat} {ι KemSK Auxiliary Reader Encoded S : Type} {base : OracleSpec ι}

/-- The actual Server commitment bytes are the production encoding of its actual six source fields. -/
theorem fields (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (trace : Trace implementation initial completed before after) :
    ∃ (ciphertext : Slice U8) (tag : Std.Array U8 16#usize) (input : Fields),
      trace.aeadReply = .Some (ciphertext, tag) ∧ input.key = trace.aead.pending.seal.material.key.bytes ∧
      input.nonce = trace.aead.pending.seal.material.nonce.bytes ∧ input.associatedData = initial.binding.associated_data ∧
      input.sequence = 1#u64 ∧ input.senderId = initial.candidate.server_identity_key_id ∧ input.tag = tag ∧
      trace.transcript.bytes = productionInput input := by
  obtain ⟨ciphertext, tag, replied, _seal, _ciphertext, _tag, encoded⟩ :=
    RegistrationNativeServerRecordFields.transcript implementation initial completed before after trace
  obtain ⟨bound, _boundRun, context, sequence⟩ := RegistrationNativeServerRecordFields.context implementation initial completed before after trace
  let input : Fields := ⟨trace.aead.pending.seal.material.key.bytes, trace.aead.pending.seal.material.nonce.bytes,
    trace.aead.pending.seal.context.associated_data, tag, trace.aead.pending.seal.sequence, trace.aead.pending.seal.context.sender_kid⟩
  refine ⟨ciphertext, tag, input, replied, rfl, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · exact congrArg record_effects.SealFrameContext.associated_data context
  · exact UScalar.eq_of_val_eq sequence
  · exact congrArg record_effects.SealFrameContext.sender_kid context
  · exact bytes_eq_of_abs_eq (encoded.trans (productionInput_abs input).symm)

private theorem opened (bytes : Pqxdh.Bytes) (result : Slice U8)
    (actual : RegistrationAuthenticationShared.openedBytes (some bytes) = .Some result) :
    TranscriptAuthParts.absSlice result = bytes := by
  simp only [RegistrationAuthenticationShared.openedBytes] at actual
  split at actual
  · cases actual
    simp only [TranscriptAuthParts.absSlice, List.map_map, Function.comp_def, absByte_concreteByte]
    change List.map id bytes = bytes
    exact List.map_id bytes
  · cases actual

/-- Actual raw writer support fixes the exact complete ciphertext/tag/commitment byte concatenation. -/
theorem frame (setup : Setup base KemSK) (codec : Codec Reader Encoded)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (before after : RegistrationWorldAgreement.State n Auxiliary)
    (trace : Trace (RegistrationWorldRecords.handler setup codec) initial completed before after)
    (digest : CtxRomAuth.CtxDigest) (hashed : trace.digestReply = .Some (RegistrationAuthenticationShared.digestArray digest)) :
    ∃ ciphertext tag, trace.aeadReply = .Some (ciphertext, tag) ∧
      TranscriptAuthParts.absSlice completed.ciphertext = TranscriptAuthParts.absSlice ciphertext ++ absBytes tag ++ digest.toList := by
  obtain ⟨ciphertext, tag, replied, sealEq, encrypted, tagged, _encoded⟩ :=
    RegistrationNativeServerRecordFields.transcript (RegistrationWorldRecords.handler setup codec) initial completed before after trace
  obtain ⟨bound, _boundRun, context, _sequence⟩ :=
    RegistrationNativeServerRecordFields.context (RegistrationWorldRecords.handler setup codec) initial completed before after trace
  obtain ⟨writer, resumed, _state, writerSeal, writerCipher, writerTag, writerCommitment⟩ :=
    server_commitment_reply_refines trace.commitmentState (RegistrationAuthenticationShared.digestArray digest)
  have hashResumed := trace.hashResumed
  rw [hashed] at hashResumed
  have writerEq : writer = trace.writer := by
    simpa only [RustM.ok.injEq, core.result.Result.Ok.injEq] using resumed.symm.trans hashResumed
  have retained := writerSeal.trans sealEq
  have cipher := writerCipher.trans encrypted
  have tagEq := writerTag.trans tagged
  rw [writerEq] at retained cipher tagEq writerCommitment
  let parts := Std.Array.make 3#usize [ciphertext, Std.Array.to_slice tag, Std.Array.to_slice (RegistrationAuthenticationShared.digestArray digest)]
  have requested : trace.writer.request = .ok (.Raw parts) := by
    simp only [registration.ServerRecordWrite.request, record_effects.SealWrite.request,
      core.array.Array.as_slice, rust_primitives.slice.array_as_slice, retained, cipher, tagEq, writerCommitment,
      ratchet.concrete.SendSeal.impl.context, context, serverRecordContext, bind_tc_ok]
    rfl
  have requestEq : trace.writeRequest = .Raw parts := RustM.ok.inj (trace.writeRequested.symm.trans requested)
  have projected : (trace.writeReply, RegistrationWorldAgreement.project after) ∈ support
      ((RegistrationRecordPrimitives.implementation setup.source codec.frameWrite (.write (.Raw parts))).run
        (RegistrationWorldAgreement.project trace.fourth)) := by
    rw [← RegistrationWorldRecords.handler_project setup codec (.write (.Raw parts)) trace.fourth, support_map]
    exact Set.mem_image_of_mem (Prod.map id RegistrationWorldAgreement.project) (requestEq ▸ trace.writeCalled)
  rw [RegistrationRecordPrimitives.raw_write_exact, support_pure, Set.mem_singleton_iff] at projected
  have replyEq : RegistrationAuthenticationShared.openedBytes (some (RegistrationRecordPrimitives.partsBytes parts)) = trace.writeReply := (congrArg Prod.fst projected).symm
  obtain ⟨result, finished, retention⟩ := BeaconcryptCore.Refinement.RegistrationPublication.server_seal_retention_refines trace.writer trace.writeReply
  have resultEq : result = .Ok completed := RustM.ok.inj (finished.symm.trans trace.writeResumed)
  cases resultEq
  have bytes := opened _ completed.ciphertext (replyEq.trans retention.2.2.2.1)
  refine ⟨ciphertext, tag, replied, ?_⟩
  have partsEq : RegistrationRecordPrimitives.partsBytes parts = TranscriptAuthParts.absSlice ciphertext ++ absBytes tag ++
      absBytes (RegistrationAuthenticationShared.digestArray digest) := by
    simp only [parts, RegistrationRecordPrimitives.partsBytes, Std.Array.make, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, TranscriptAuthParts.absSlice, Std.Array.to_slice,
      absBytes, List.append_assoc]
  rw [partsEq, RegistrationAuthenticationShared.digest_array_bytes] at bytes
  exact bytes

end BeaconcryptCore.Computational.RegistrationNativeServerRawSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRawSource.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRawSource.fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRawSource.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRawSource.frame
