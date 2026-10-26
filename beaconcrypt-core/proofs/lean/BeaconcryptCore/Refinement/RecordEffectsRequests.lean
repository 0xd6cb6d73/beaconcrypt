-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RecordEffects
import BeaconcryptCore.Refinement.TranscriptAuthParts

/-! Exact byte and metadata specifications for actual outbound record requests, covering ordinary raw/framed payloads and the source-owned registration prefix. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RecordEffectsRequests

def plaintextBytes : record_effects.SealPlaintextRequest → Pqxdh.Bytes
  | .Single application => TranscriptAuthParts.absSlice application
  | .Prefixed assigned application => absBytes assigned ++ TranscriptAuthParts.absSlice application

def contextPlaintext (context : record_effects.SealFrameContext) : Pqxdh.Bytes :=
  (match context.prefix with | .None => [] | .Some assigned => absBytes assigned) ++
    TranscriptAuthParts.absSlice context.plaintext

def writeBytes : record_effects.RecordWriteRequest → Pqxdh.Bytes
  | .Raw parts | .Frame parts _ _ => TranscriptAuthParts.absParts parts

/-- Ordinary payload admission retains all metadata and sends exactly the borrowed application bytes. -/
theorem context_new_exact (application : Slice Std.U8) (target sender : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) (encoding : record_effects.RecordEncoding) :
    record_effects.SealFrameContext.new application target sender associatedData encoding =
      ok ⟨application, .None, associatedData, target, sender, encoding⟩ := by
  rfl

/-- The registration prefix is exactly LE64 of the assigned key; the application and full associated data are retained. -/
theorem registration_context_exact (application : Slice Std.U8) (assigned sender : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) :
    ∃ context, record_effects.SealFrameContext.registration application assigned sender associatedData = ok context ∧
      context.plaintext = application ∧ context.associated_data = associatedData ∧
      context.target_kid = assigned ∧ context.sender_kid = sender ∧ context.encoding = .Raw ∧
      contextPlaintext context = Pqxdh.LE64 assigned.val ++ TranscriptAuthParts.absSlice application := by
  obtain ⟨binding, run, bytes⟩ := registration_key_id_binding_abs assigned
  refine ⟨⟨application, .Some binding.bytes, associatedData, assigned, sender, .Raw⟩, ?_, rfl, rfl,
    rfl, rfl, rfl, ?_⟩
  · simp only [record_effects.SealFrameContext.registration, run,
      pqxdh.RegistrationKeyIdBinding.as_bytes, bind_tc_ok]
  · exact congrArg (fun preimage => preimage ++ TranscriptAuthParts.absSlice application) bytes

/-- Actual plaintext requests encode precisely the optional retained prefix followed by the same application. -/
theorem plaintext_request_exact (context : record_effects.SealFrameContext) :
    ∃ request, context.plaintext_request = ok request ∧ plaintextBytes request = contextPlaintext context := by
  cases prefixEq : context.prefix with
  | none =>
    exact ⟨.Single context.plaintext,
      by simp [record_effects.SealFrameContext.plaintext_request, prefixEq],
      by simp [plaintextBytes, contextPlaintext, prefixEq]⟩
  | some assigned =>
    exact ⟨.Prefixed assigned context.plaintext,
      by simp [record_effects.SealFrameContext.plaintext_request, prefixEq],
      by simp [plaintextBytes, contextPlaintext, prefixEq]⟩

/-- The actual AEAD request uses the selected key/nonce, complete retained associated data and exact payload bytes. -/
theorem aead_request_exact (pending : record_effects.SealAead) :
    ∃ request, pending.request = ok request ∧ request.key = pending.seal.material.key.bytes ∧
      request.nonce = pending.seal.material.nonce.bytes ∧
      request.associated_data = pending.seal.context.associated_data ∧
      plaintextBytes request.plaintext = contextPlaintext pending.seal.context := by
  obtain ⟨plaintext, run, bytes⟩ := plaintext_request_exact pending.seal.context
  refine ⟨⟨pending.seal.material.key.bytes, pending.seal.material.nonce.bytes,
    pending.seal.context.associated_data, plaintext⟩, ?_, rfl, rfl, rfl, bytes⟩
  simp only [record_effects.SealAead.request, ratchet.concrete.SendSeal.impl.material,
    ratchet.concrete.SendSeal.impl.context, ratchet.RatchetMaterial.impl.key,
    ratchet.RatchetMaterial.impl.nonce, ratchet.RatchetKey.as_bytes,
    ratchet.RatchetNonce.as_bytes, bind_tc_ok, run]

/-- Both wire encodings request ciphertext, detached tag and supplied commitment in that order; framed metadata comes from the retained capability. -/
theorem write_request_exact (pending : record_effects.SealWrite) :
    ∃ request, pending.request = ok request ∧
      writeBytes request = TranscriptAuthParts.absSlice pending.ciphertext ++
        absBytes pending.tag ++ absBytes pending.commitment ∧
      match request with
      | .Raw _ => pending.seal.context.encoding = .Raw
      | .Frame _ sequence sender => pending.seal.context.encoding = .Frame ∧
          sequence = pending.seal.sequence ∧ sender = pending.seal.context.sender_kid := by
  let parts := Std.Array.make 3#usize
    [pending.ciphertext, pending.tag.to_slice, pending.commitment.to_slice]
  cases encodingEq : pending.seal.context.encoding with
  | Raw =>
    refine ⟨.Raw parts, ?_, ?_, rfl⟩
    · simp [record_effects.SealWrite.request, ratchet.concrete.SendSeal.impl.context,
        core.array.Array.as_slice, rust_primitives.slice.array_as_slice, encodingEq, parts]
    · simp [writeBytes, parts, TranscriptAuthParts.absParts, TranscriptAuthParts.absSlice,
        absBytes, Std.Array.make, Std.Array.to_slice, List.append_assoc]
      dsimp! only [TranscriptAuthParts.absSlice]
      simp
      rfl
  | Frame =>
    refine ⟨.Frame parts pending.seal.sequence pending.seal.context.sender_kid,
      ?_, ?_, rfl, rfl, rfl⟩
    · simp [record_effects.SealWrite.request, ratchet.concrete.SendSeal.impl.context,
        ratchet.concrete.SendSeal.impl.sequence, core.array.Array.as_slice,
        rust_primitives.slice.array_as_slice, encodingEq, parts]
    · simp [writeBytes, parts, TranscriptAuthParts.absParts, TranscriptAuthParts.absSlice,
        absBytes, Std.Array.make, Std.Array.to_slice, List.append_assoc]
      dsimp! only [TranscriptAuthParts.absSlice]
      simp
      rfl

/--
info: 'BeaconcryptCore.Refinement.RecordEffectsRequests.context_new_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms context_new_exact
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsRequests.registration_context_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms registration_context_exact
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsRequests.plaintext_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms plaintext_request_exact
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsRequests.aead_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms aead_request_exact
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsRequests.write_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms write_request_exact

end BeaconcryptCore.Refinement.RecordEffectsRequests
