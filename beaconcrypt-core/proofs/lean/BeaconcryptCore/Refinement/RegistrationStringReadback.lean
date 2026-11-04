-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationShallowString
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual cbor_read of a bounded canonical byte-string segment returns the
original source factory result, including its borrowed payload. The actual
shallow serializer supplies precisely this bounded segment through actual
standard splitting at its derived cursor; spare buffer bytes remain separate.
Complete container/parser validation and public dispatcher remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationStringReadback
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical
open RegistrationShallowString RegistrationStringFactory
abbrev RawOption := cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177

set_option backward.isDefEq.respectTransparency false in
theorem read_factory (input source : Slice U8)
    (contents : input.val = encodedBytes cbor_major_type_byte_string (lengthValue source) ++ source.val) :
    (do let parsed ← cbor_read input; .ok ((.Some parsed) : RawOption)) = extraction_mk_byte_string source := by
  have majorBound : cbor_major_type_byte_string.val < 8 := by simp [cbor_major_type_byte_string]
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by
    simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := RegistrationHeaderJump.split_prefix
    input (writtenCount (lengthValue source))
    (encodedBytes cbor_major_type_byte_string (lengthValue source)) source.val contents
    (encoded_length cbor_major_type_byte_string (lengthValue source)).symm
  have sameTail : tail = source := by apply Subtype.ext; exact tailBytes
  subst tail
  have readFront : read_header front = .ok (normalHeader cbor_major_type_byte_string (lengthValue source)) :=
    RegistrationHeaderCanonicalRead.read_encoded front _ _ [] (by simpa using frontBytes) majorBound notSimple
  unfold cbor_read
  rw [RegistrationHeaderCanonicalRead.jump_encoded input _ _ source.val contents majorBound]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok]
  have update (before after : header) :
      Array.update (Array.repeat 1#usize before) 0#usize after = .ok (Array.repeat 1#usize after) := rfl
  have index (after : header) : Array.index_usize (Array.repeat 1#usize after) 0#usize = .ok after := rfl
  rw [update, bind_tc_ok, index]
  simp [RegistrationHeaderCanonicalRead.normal_major, cbor_major_type_byte_string,
    cbor_major_type_uint64, cbor_major_type_neg_int64, cbor_major_type_text_string]
  rw [factory_normal]
  have compare : (lengthValue source ≤ (UScalar.cast .U64 max_simple_value_additional_info)) ↔
      (lengthValue source).val < 24 := by
    simp only [max_simple_value_additional_info]
    change (lengthValue source ≤ 23#u64) ↔ _
    scalar_tac
  simp only [mk_raw_uint64, lift, bind_tc_ok, compare]
  simp only [UScalar.lt_equiv,
    show (256#u64 : U64).val = 256 by rfl,
    show (65536#u64 : U64).val = 65536 by rfl,
    show (4294967296#u64 : U64).val = 4294967296 by rfl]
  unfold normalHeader
  split_ifs <;> simp only [bind_tc_ok, cbor_major_type_byte_string]

set_option backward.isDefEq.respectTransparency false in
theorem serializer_readback (out source : Slice U8)
    (space : (writtenCount (lengthValue source)).val + source.length ≤ out.length) :
    ∃ after front tail,
      sourceSerialize out source = .ok
        (Usize.wrapping_add (writtenCount (lengthValue source)) source.len, after) ∧
      after.length = out.length ∧
      core.slice.Slice.split_at after
        (Usize.wrapping_add (writtenCount (lengthValue source)) source.len) = .ok (front, tail) ∧
      front.val = encodedBytes cbor_major_type_byte_string (lengthValue source) ++ source.val ∧
      tail.val = out.val.drop ((writtenCount (lengthValue source)).val + source.length) ∧
      (do let parsed ← cbor_read front; .ok ((.Some parsed) : RawOption)) = extraction_mk_byte_string source := by
  obtain ⟨after, serialized, sameLength, bytes, count⟩ := RegistrationShallowString.codec out source space
  have contents : after.val =
      (encodedBytes cbor_major_type_byte_string (lengthValue source) ++ source.val) ++
        out.val.drop ((writtenCount (lengthValue source)).val + source.length) := by
    simpa only [List.append_assoc] using bytes
  have position : (Usize.wrapping_add (writtenCount (lengthValue source)) source.len).val =
      (encodedBytes cbor_major_type_byte_string (lengthValue source) ++ source.val).length := by
    rw [List.length_append]
    exact count
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := RegistrationHeaderJump.split_prefix after
    (Usize.wrapping_add (writtenCount (lengthValue source)) source.len) _ _ contents position
  exact ⟨after, front, tail, serialized, sameLength, splitInput, frontBytes, tailBytes,
    read_factory front source frontBytes⟩

end BeaconcryptCore.Refinement.RegistrationStringReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringReadback.read_factory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringReadback.read_factory

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringReadback.serializer_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringReadback.serializer_readback
