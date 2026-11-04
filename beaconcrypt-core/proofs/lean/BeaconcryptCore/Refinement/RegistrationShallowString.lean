-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationStringFactory
import BeaconcryptCore.Refinement.RegistrationByteCopy
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual prepared ByteString factory and original shallow serializer branch
compose with the actual header writer, both mutable splits, every U8 clone, byte
copy and both writebacks. Output prefix, payload, untouched suffix, slice length
and nonwrapping cursor are derived from capacity. Public dispatcher and parser
composition remain separate obligations. -/
namespace BeaconcryptCore.Refinement.RegistrationShallowString
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical RegistrationStringFactory

abbrev lengthValue (source : Slice U8) : U64 := UScalar.cast .U64 source.len

def sourceSerialize (out source : Slice U8) : RustM (Usize × Slice U8) := do
  let raw ← extraction_mk_byte_string source
  match raw with
  | .Some (.CBOR_Case_String string) => extraction_serialize_shallow_string string out 0#usize
  | _ => .fail .panic

set_option backward.isDefEq.respectTransparency false in
theorem source_serialize (out source : Slice U8)
    (space : (writtenCount (lengthValue source)).val + source.length ≤ out.length) :
    ∃ after, sourceSerialize out source = .ok
      (Usize.wrapping_add (writtenCount (lengthValue source)) source.len, after) ∧
      after.length = out.length ∧
      after.val = (written out cbor_major_type_byte_string (lengthValue source)).val.take
        (writtenCount (lengthValue source)).val ++ source.val ++
        (written out cbor_major_type_byte_string (lengthValue source)).val.drop
          ((writtenCount (lengthValue source)).val + source.length) := by
  change (writtenCount (lengthValue source)).val + source.val.length ≤ out.val.length at space
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by
    simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  obtain ⟨size, factory, raw⟩ := factory_exists source
  have argument : raw_uint64_as_argument cbor_major_type_byte_string
      (raw_uint64.mk size (lengthValue source)) = .ok (normalHeader cbor_major_type_byte_string (lengthValue source)) := by
    have result := source_normal cbor_major_type_byte_string (lengthValue source)
    unfold sourceHeader at result
    rw [raw] at result
    simpa only [bind_tc_ok] using result
  have writer := source_write out cbor_major_type_byte_string (lengthValue source) (by omega) notSimple
  simp only [sourceWrite, source_normal, bind_tc_ok] at writer
  have outputLength := written_length out cbor_major_type_byte_string (lengthValue source)
  obtain ⟨after, copied, afterLength, afterBytes⟩ := RegistrationByteCopy.copy_into
    (written out cbor_major_type_byte_string (lengthValue source))
    (writtenCount (lengthValue source)) source (by rw [outputLength]; exact space)
  refine ⟨after, ?_, afterLength.trans outputLength, afterBytes⟩
  unfold sourceSerialize
  rw [factory]
  simp only [bind_tc_ok]
  unfold extraction_serialize_shallow_string cbor_raw_with_perm_get_header_d cbor_raw_get_header_d
  dsimp only
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok, lift]
  rw [argument]
  simp only [bind_tc_ok]
  rw [writer]
  simp [RegistrationHeaderCanonicalRead.normal_major, uncurry]
  have add (left right : Usize) : core.num.Usize.wrapping_add left right = .ok (Usize.wrapping_add left right) := rfl
  rw [add]
  unfold RegistrationByteCopy.copyInto at copied
  simp only [bind_tc_ok] at copied ⊢
  cases first : core.slice.Slice.split_at_mut
      (written out cbor_major_type_byte_string (lengthValue source))
      (writtenCount (lengthValue source)) with
  | fail error => simp only [first, bind_tc_fail, reduceCtorEq] at copied
  | div => simp only [first, bind_tc_div, reduceCtorEq] at copied
  | ok result =>
    rcases result with ⟨⟨front, remaining⟩, back⟩
    simp only [first, bind_tc_ok, uncurry] at copied ⊢
    cases second : core.slice.Slice.split_at_mut remaining source.len with
    | fail error => simp only [second, bind_tc_fail, reduceCtorEq] at copied
    | div => simp only [second, bind_tc_div, reduceCtorEq] at copied
    | ok result1 =>
      rcases result1 with ⟨⟨destination, tail⟩, back1⟩
      simp only [second, bind_tc_ok, uncurry] at copied ⊢
      cases copying : core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy destination source with
      | fail error => simp only [copying, bind_tc_fail, reduceCtorEq] at copied
      | div => simp only [copying, bind_tc_div, reduceCtorEq] at copied
      | ok copiedBytes =>
        simp only [copying, bind_tc_ok, RustM.ok.injEq] at copied ⊢
        exact congrArg (fun updated =>
          (Usize.wrapping_add (writtenCount (lengthValue source)) source.len, updated)) copied

set_option backward.isDefEq.respectTransparency false in
theorem header_parts (out source : Slice U8)
    (space : (writtenCount (lengthValue source)).val ≤ out.val.length) :
    (written out cbor_major_type_byte_string (lengthValue source)).val.take
        (writtenCount (lengthValue source)).val = encodedBytes cbor_major_type_byte_string (lengthValue source) ∧
    (written out cbor_major_type_byte_string (lengthValue source)).val.drop
        ((writtenCount (lengthValue source)).val + source.length) =
      out.val.drop ((writtenCount (lengthValue source)).val + source.length) := by
  have bytes := written_bytes out cbor_major_type_byte_string (lengthValue source) space
  have length := encoded_length cbor_major_type_byte_string (lengthValue source)
  have dropped : (written out cbor_major_type_byte_string (lengthValue source)).val.drop
      (writtenCount (lengthValue source)).val = out.val.drop (writtenCount (lengthValue source)).val := by
    rw [bytes]
    exact List.drop_left' length
  constructor
  · rw [bytes]
    exact List.take_left' length
  · rw [← List.drop_drop (i := source.length) (j := (writtenCount (lengthValue source)).val),
      dropped, List.drop_drop]

set_option backward.isDefEq.respectTransparency false in
theorem cursor_value (out source : Slice U8)
    (space : (writtenCount (lengthValue source)).val + source.length ≤ out.length) :
    (Usize.wrapping_add (writtenCount (lengthValue source)) source.len).val =
      (writtenCount (lengthValue source)).val + source.length := by
  rw [Usize.wrapping_add_val_eq, Slice.len_val]
  apply Nat.mod_eq_of_lt
  rw [UScalar.size_def]
  have bound := out.len.hBounds
  simp only [Slice.len_val] at bound
  change (writtenCount (lengthValue source)).val + source.val.length < 2 ^ UScalarTy.Usize.numBits
  change (writtenCount (lengthValue source)).val + source.val.length ≤ out.val.length at space
  change out.val.length < 2 ^ UScalarTy.Usize.numBits at bound
  omega

set_option backward.isDefEq.respectTransparency false in
theorem codec (out source : Slice U8)
    (space : (writtenCount (lengthValue source)).val + source.length ≤ out.length) :
    ∃ after, sourceSerialize out source = .ok
      (Usize.wrapping_add (writtenCount (lengthValue source)) source.len, after) ∧
      after.length = out.length ∧
      after.val = encodedBytes cbor_major_type_byte_string (lengthValue source) ++ source.val ++
        out.val.drop ((writtenCount (lengthValue source)).val + source.length) ∧
      (Usize.wrapping_add (writtenCount (lengthValue source)) source.len).val =
        (encodedBytes cbor_major_type_byte_string (lengthValue source)).length + source.length := by
  obtain ⟨after, result, sameLength, bytes⟩ := source_serialize out source space
  have capacity : (writtenCount (lengthValue source)).val ≤ out.val.length := by
    change (writtenCount (lengthValue source)).val + source.val.length ≤ out.val.length at space
    omega
  have parts := header_parts out source capacity
  refine ⟨after, result, sameLength, ?_, ?_⟩
  · rw [parts.1, parts.2] at bytes
    exact bytes
  · rw [cursor_value out source space, encoded_length]

end BeaconcryptCore.Refinement.RegistrationShallowString

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowString.source_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowString.source_serialize

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowString.header_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowString.header_parts

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowString.cursor_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowString.cursor_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowString.codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowString.codec
