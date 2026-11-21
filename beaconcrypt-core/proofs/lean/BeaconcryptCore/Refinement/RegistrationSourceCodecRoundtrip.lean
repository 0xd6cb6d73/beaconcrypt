-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPublicReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual public buffer serializers and public decoders compose on the written prefix. The entire mutable output slice, including its original length and unused suffix, remains in the result. Allocation is outside these buffer-taking functions. -/
namespace BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip
open beaconcrypt_parse RegistrationSerializerReachableSource

theorem init [RegistrationValidatorPrimitive.Operations]
    (other : OtherBranches) (value : transport.initkex) (output : Slice U8)
    (shape : RegistrationSerializerInitBytes.InitShape value) (room : 1490 ≤ output.length) :
    ∃ after front spare,
      @extraction_encode_init (operations other) value output = .ok (1490#usize, after) ∧
      after.length = output.length ∧
      core.slice.Slice.split_at after 1490#usize = .ok (front, spare) ∧
      front.val = 134#u8 :: RegistrationSerializerInitBytes.payload value ∧
      spare.val = output.val.drop 1490 ∧
      extraction_decode_init front = .ok (.Some value) := by
  obtain ⟨after, encoded, length, bytes⟩ := RegistrationSerializerInitBytes.public_bytes other value output shape room
  have position : (1490#usize).val = (134#u8 :: RegistrationSerializerInitBytes.payload value).length := by
    simp only [List.length_cons, RegistrationPublicReadback.init_payload_length value shape]
    scalar_tac
  obtain ⟨front, spare, split, frontBytes, spareBytes⟩ := RegistrationHeaderJump.split_prefix
    after 1490#usize _ _ bytes position
  exact ⟨after, front, spare, encoded, length, split, frontBytes, spareBytes,
    RegistrationPublicReadback.decode_init front value frontBytes shape⟩

theorem response [RegistrationValidatorPrimitive.Operations]
    (other : OtherBranches) (value : transport.kexresponse) (output : Slice U8)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value)
    (room : RegistrationSerializerResponseBytes.totalLength value ≤ output.length)
    (admitted : RegistrationSerializerResponseBytes.totalLength value ≤ BeaconcryptCore.Computational.CborSizing.maxMessageSize) :
    ∃ after front spare,
      @extraction_encode_response (operations other) value output =
        .ok (RegistrationSerializerResponseBytes.finalCursor value, after) ∧
      after.length = output.length ∧
      core.slice.Slice.split_at after (RegistrationSerializerResponseBytes.finalCursor value) = .ok (front, spare) ∧
      front.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value ∧
      spare.val = output.val.drop (RegistrationSerializerResponseBytes.totalLength value) ∧
      extraction_decode_response front = .ok (.Some value) := by
  obtain ⟨after, encoded, length, bytes, cursor⟩ := RegistrationSerializerResponseBytes.public_bytes other value output shape room admitted
  have position : (RegistrationSerializerResponseBytes.finalCursor value).val =
      (136#u8 :: RegistrationSerializerResponseBytes.payload value).length := by
    rw [cursor, List.length_cons]
    exact (RegistrationPublicReadback.response_payload_length value shape).symm
  obtain ⟨front, spare, split, frontBytes, spareBytes⟩ := RegistrationHeaderJump.split_prefix
    after (RegistrationSerializerResponseBytes.finalCursor value) _ _ bytes position
  exact ⟨after, front, spare, encoded, length, split, frontBytes, spareBytes,
    RegistrationPublicReadback.decode_response front value frontBytes shape admitted⟩

end BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip

/-- info: 'BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSourceCodecRoundtrip.response
