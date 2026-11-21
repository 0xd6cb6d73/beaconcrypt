-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationFlatHeader
import BeaconcryptCore.Refinement.RegistrationArrayRotation
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Actual generated jump_raw_data_item executes one successful source loop iteration for a canonical unsigned integer or bounded byte string, then terminates. The derived cursor includes the complete payload and the final source counter is zero. Arbitrary following bytes remain outside the skipped item. -/
namespace BeaconcryptCore.Refinement.RegistrationFlatSkip
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump RegistrationFlatHeader
open RegistrationCodecArraySingleton

def empty : Slice U8 := ⟨[], by simp⟩
theorem split_zero (input : Slice U8) :
    core.slice.Slice.split_at input 0#usize = .ok (empty, input) := by
  simp [CoreModels.core.slice.Slice.split_at, CoreModels.rust_primitives.slice.slice_split_at,
    Aeneas.Std.core.slice.Slice.split_at, List.splitAt_eq, Slice.length, empty]
  apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem jump_loop_unfold (input : Slice U8) (offset count : Array Usize 1#usize) (condition : Bool) :
    jump_raw_data_item_loop input offset count condition =
      (jump_raw_data_item_loop.body input offset count condition >>= fun result =>
        match result with
        | .cont (offsetNext, countNext, conditionNext) =>
          jump_raw_data_item_loop input offsetNext countNext conditionNext
        | .done result => .ok result) := by
  unfold jump_raw_data_item_loop
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem uint_body (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    jump_raw_data_item_loop.body input (pack 0#usize) (pack 1#usize) true =
      .ok (.cont (pack (writtenCount value), pack 0#usize, false)) := by
  have majorBound : cbor_major_type_uint64.val < 8 := by simp [cbor_major_type_uint64]
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  have notString : cbor_major_type_uint64 ≠ cbor_major_type_byte_string := by simp [cbor_major_type_uint64, cbor_major_type_byte_string]
  have notText : cbor_major_type_uint64 ≠ cbor_major_type_text_string := by simp [cbor_major_type_uint64, cbor_major_type_text_string]
  have notArray : cbor_major_type_uint64 ≠ cbor_major_type_array := by simp [cbor_major_type_uint64, cbor_major_type_array]
  have notMap : cbor_major_type_uint64 ≠ cbor_major_type_map := by simp [cbor_major_type_uint64, cbor_major_type_map]
  have notTagged : cbor_major_type_uint64 ≠ cbor_major_type_tagged := by simp [cbor_major_type_uint64, cbor_major_type_tagged]
  obtain ⟨front, tail, splitInput, frontBytes, _, readFront⟩ := header_parts input _ value rest contents majorBound notSimple
  have countFront := count_leaf front _ value [] (by simpa using frontBytes) majorBound notSimple notArray notMap notTagged
  simp only [jump_raw_data_item_loop.body, ↓reduceIte, index_pack,
    jump_encoded input _ value rest contents majorBound, bind_tc_ok, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero,
    splitInput, readFront,
    jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call,
    normal_major, notString, notText, update_pack, core.slice.Slice.len,
    rust_primitives.slice.slice_length, beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2,
    countFront]
  have sub11 : Usize.wrapping_sub 1#usize 1#usize = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationHeaderSize.sub_value _ _ (by omega)]
    rfl
  rw [sub11, RegistrationSerializerStages.add_usize 0#usize 0#usize 0#usize (by simp)]
  simp [bind_tc_ok]

set_option backward.isDefEq.respectTransparency false in
theorem uint (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    jump_raw_data_item input 0#usize = .ok (writtenCount value) := by
  simp only [jump_raw_data_item, show Array.repeat 1#usize = @pack Usize from rfl,
    index_pack, bind_tc_ok]
  have running : decide (1#usize > 0#usize) = true := by simp
  rw [jump_loop_unfold, running, uint_body input value rest contents]
  simp only [bind_tc_ok]
  rw [jump_loop_unfold]
  simp only [jump_raw_data_item_loop.body, Bool.false_eq_true, ↓reduceIte, bind_tc_ok, index_pack]

theorem cast_length (payload : Slice U8) :
    UScalar.cast .Usize (UScalar.cast .U64 payload.len) = payload.len := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq, RegistrationStringFactory.length_cast]
  rw [Nat.mod_eq_of_lt (by simpa only [Slice.len_val] using payload.len.hBounds)]
  exact (Slice.len_val payload).symm

theorem add_source (left right : Usize) :
    core.num.Usize.wrapping_add left right = .ok (Usize.wrapping_add left right) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem bytes_body (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    jump_raw_data_item_loop.body input (pack 0#usize) (pack 1#usize) true =
      .ok (.cont (pack (RegistrationSerializerFields.byteCount payload), pack 0#usize, false)) := by
  have majorBound : cbor_major_type_byte_string.val < 8 := by simp [cbor_major_type_byte_string]
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  have notArray : cbor_major_type_byte_string ≠ cbor_major_type_array := by simp [cbor_major_type_byte_string, cbor_major_type_array]
  have notMap : cbor_major_type_byte_string ≠ cbor_major_type_map := by simp [cbor_major_type_byte_string, cbor_major_type_map]
  have notTagged : cbor_major_type_byte_string ≠ cbor_major_type_tagged := by simp [cbor_major_type_byte_string, cbor_major_type_tagged]
  have fit : (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length ≤ input.length := by
    have lengths := congrArg List.length contents
    simp only [List.length_append, encoded_length] at lengths
    change input.length = (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length + rest.length at lengths
    omega
  have sizeValue := RegistrationSerializerFields.byte_count_value input payload fit
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input _ _ (payload.val ++ rest)
    (by simpa only [List.append_assoc] using contents) majorBound notSimple
  obtain ⟨item, suffix, splitItem, itemBytes, _⟩ := split_prefix input
    (RegistrationSerializerFields.byteCount payload)
    (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val)
    rest contents (by rw [sizeValue, List.length_append, encoded_length])
  have countItem := count_leaf item _ _ payload.val itemBytes majorBound notSimple notArray notMap notTagged
  simp only [jump_raw_data_item_loop.body, ↓reduceIte, index_pack,
    jump_encoded input _ _ (payload.val ++ rest) (by simpa only [List.append_assoc] using contents) majorBound,
    bind_tc_ok, split_zero, uncurry, RegistrationHeaderValidation.sub_source,
    RegistrationArrayRotation.sub_zero, splitInput, readFront,
    jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call,
    normal_major, ↓reduceIte, argument_normal, lift, cast_length, add_source,
    show Usize.wrapping_add (writtenCount (UScalar.cast .U64 payload.len)) payload.len =
      RegistrationSerializerFields.byteCount payload from rfl,
    update_pack, splitItem, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, countItem]
  have sub11 : Usize.wrapping_sub 1#usize 1#usize = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationHeaderSize.sub_value _ _ (by omega)]
    rfl
  rw [sub11]
  simp [RegistrationArrayRotation.add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem bytes (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    jump_raw_data_item input 0#usize = .ok (RegistrationSerializerFields.byteCount payload) := by
  simp only [jump_raw_data_item, show Array.repeat 1#usize = @pack Usize from rfl,
    index_pack, bind_tc_ok]
  have running : decide (1#usize > 0#usize) = true := by simp
  rw [jump_loop_unfold, running, bytes_body input payload rest contents]
  simp only [bind_tc_ok]
  rw [jump_loop_unfold]
  simp only [jump_raw_data_item_loop.body, Bool.false_eq_true, ↓reduceIte, bind_tc_ok, index_pack]

end BeaconcryptCore.Refinement.RegistrationFlatSkip

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.split_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.split_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.jump_loop_unfold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.jump_loop_unfold

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.uint_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.uint_body

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.uint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.uint

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.cast_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.cast_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.add_source' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.add_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.bytes_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.bytes_body

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatSkip.bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatSkip.bytes
