-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationArrayGcd
import BeaconcryptCore.Refinement.RegistrationHeaderSize
import BeaconcryptCore.Refinement.RegistrationByteCopy

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow

set_option autoImplicit false
set_option warningAsError true

/-! Source pipeline reduction for a count-six array and a one-byte header. The actual outer rotation loop, mutable split back function, retained tail and returned cursor remain explicit; no rotation, parser or readback law is assumed. -/

namespace BeaconcryptCore.Refinement.RegistrationArraySerializeSix
open beaconcrypt_parse.cbordetveraux

def raw6 : raw_uint64 := { size := 0#u8, value := 6#u64 }
def header6 : header := .mk (.mk 4#u8 6#u8) .LongArgumentOther
def cursor (offset : Usize) : Usize := Usize.wrapping_add offset 1#usize
def mutated (before : Slice U8) (offset : Usize) : Slice U8 :=
  before.set offset 134#u8

private theorem index_singleton (value : Usize) :
    Array.index_usize (Array.repeat 1#usize value) 0#usize = .ok value := rfl

theorem mk_raw6 : mk_raw_uint64 6#u64 = .ok raw6 := by
  simp only [mk_raw_uint64, max_simple_value_additional_info, lift, bind_tc_ok]
  rfl

theorem raw_argument8 : raw_uint64_as_argument cbor_major_type_array raw6 = .ok header6 := by
  simp only [raw_uint64_as_argument, raw6, cbor_major_type_array]
  rfl

theorem cursor_value (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) : (cursor offset).val = offset.val + 1 := by
  rw [cursor, Usize.wrapping_add_val_eq, UScalar.size_def,
    show (1#usize : Usize).val = 1 from rfl]
  exact Nat.mod_eq_of_lt (by
    have bound := before.len.hBounds
    rw [Slice.len_val] at bound
    omega)

theorem cursor_sub_one (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) : Usize.wrapping_sub (cursor offset) 1#usize = offset := by
  apply UScalar.eq_of_val_eq
  rw [RegistrationHeaderSize.sub_value _ _ (by
      rw [cursor_value before offset room]
      exact Nat.succ_le_succ (Nat.zero_le _)), cursor_value before offset room,
    show (1#usize : Usize).val = 1 from rfl, Nat.add_sub_cancel]

theorem write_header6 (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) :
    write_header header6 before offset = .ok (cursor offset, mutated before offset) := by
  simp only [header6, write_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    RegistrationHeaderBits.set_additional, RegistrationHeaderBits.set_major,
    RegistrationArrayIndex.wrapping_add,
    RegistrationArrayIndex.wrapping_sub, bind_tc_ok]
  simp only [additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    show (6#u8 : U8) ≠ 24#u8 by decide, show (6#u8 : U8) ≠ 25#u8 by decide,
    show (6#u8 : U8) ≠ 26#u8 by decide, show (6#u8 : U8) ≠ 27#u8 by decide, ite_false,
    show RegistrationHeaderBits.packed 4#u8 6#u8 = 134#u8 from rfl]
  rw [show Usize.wrapping_sub (Usize.wrapping_add offset 1#usize) 1#usize = offset from
    cursor_sub_one before offset room]
  simp [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq,
    List.getElem?_eq_getElem room, cursor, mutated, uncurry]

theorem size_header6 (capacity : Usize) (room : 0 < capacity.val) :
    size_header header6 (Array.to_slice (Array.repeat 1#usize capacity)) =
      .ok (true, RegistrationHeaderSize.cell (Usize.wrapping_sub capacity 1#usize)) := by
  change size_header (.mk (.mk 4#u8 6#u8) .LongArgumentOther)
    (RegistrationHeaderSize.cell capacity) = _
  rw [RegistrationHeaderSize.short _ _ _ _ (by decide)]
  simp only [show ¬capacity < 1#usize by scalar_tac, ite_false]

theorem remaining_value (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) :
    (Usize.wrapping_sub before.len offset).val = before.length - offset.val := by
  rw [RegistrationHeaderSize.sub_value _ _ (by simpa only [Slice.len_val] using Nat.le_of_lt room),
    Slice.len_val]

theorem entry6_to_loop (before : Slice U8) (offset : Usize)
    (positive : 0 < offset.val) (room : offset.val < before.length) :
    extraction_array_entry 6#u64 before offset = (do
      let ((front, tail), back) ←
        core.slice.Slice.split_at_mut (mutated before offset) (cursor offset)
      let rotated ← extraction_serialize_array_loop1 offset front 1#usize front.len
        (Array.repeat 1#usize 0#usize) true
      .ok (cursor offset, back (rotated, tail))) := by
  simp only [extraction_array_entry, mk_raw6, bind_tc_ok, extraction_serialize_array,
    RegistrationArrayIndex.slice_len, RegistrationArrayIndex.wrapping_sub, raw_argument8,
    lift, bind_tc_ok]
  simp only [Array.to_slice_mut, uncurry,
    size_header6 _ (by rw [remaining_value before offset room]; omega),
    write_header6 before offset room, bind_tc_ok, ite_true]
  obtain ⟨front, tail, back, splitSource, frontLength, _⟩ :=
    RegistrationByteCopy.split_mut_success (mutated before offset) (cursor offset) (by
      rw [cursor_value before offset room]
      simpa only [mutated, Slice.set_length] using Nat.succ_le_of_lt room)
  simp only [splitSource, bind_tc_ok, uncurry]
  have consecutive : front.len.val = offset.val + 1 := by
    simpa only [Slice.len_val] using frontLength.trans (cursor_value before offset room)
  simp only [show offset ≠ 0#usize by scalar_tac,
    show offset ≠ front.len by scalar_tac, ite_false]
  simp only [index_singleton, bind_tc_ok,
    show decide (offset > 0#usize) = true by simpa only [decide_eq_true_eq] using
      (show offset > 0#usize by scalar_tac),
    RegistrationArrayGcd.gcd_consecutive front.len offset positive consecutive,
    RegistrationArrayGcd.wrapping_div_one]
  rfl

theorem entry6_zero (before : Slice U8) (nonempty : 0 < before.length) :
    extraction_array_entry 6#u64 before 0#usize = .ok (1#usize, mutated before 0#usize) := by
  simp only [extraction_array_entry, mk_raw6, bind_tc_ok, extraction_serialize_array,
    RegistrationArrayIndex.slice_len, RegistrationArrayIndex.wrapping_sub, raw_argument8,
    lift, Array.to_slice_mut, uncurry,
    size_header6 (Usize.wrapping_sub before.len 0#usize) (by
      simpa only [remaining_value before 0#usize nonempty,
      show (0#usize : Usize).val = 0 from rfl, Nat.sub_zero] using nonempty),
    write_header6 before 0#usize nonempty, bind_tc_ok, ite_true]
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success (mutated before 0#usize) (cursor 0#usize) (by
      rw [cursor_value before 0#usize nonempty]
      simpa only [mutated, Slice.set_length, show (0#usize : Usize).val = 0 from rfl]
        using Nat.succ_le_of_lt nonempty)
  have restored : back (front, tail) = mutated before 0#usize := Subtype.ext (by
    rw [(backLaw front tail frontLength tailLength).1, frontBytes, tailBytes,
      List.take_append_drop])
  rw [splitSource]
  simp only [bind_tc_ok, uncurry, restored,
    show cursor 0#usize = 1#usize from UScalar.eq_of_val_eq (by
      simpa only [show (0#usize : Usize).val = 0 from rfl,
        show (1#usize : Usize).val = 1 from rfl, Nat.zero_add]
        using cursor_value before 0#usize nonempty)]

theorem mutated_take (before : Slice U8) (offset : Usize) :
    (mutated before offset).val.take offset.val = before.val.take offset.val := by
  rw [mutated, Slice.set_val_eq, List.take_set,
    List.set_eq_of_length_le (by simp only [List.length_take]; omega)]

theorem mutated_front (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) :
    (mutated before offset).val.take (offset.val + 1) =
      before.val.take offset.val ++ [134#u8] := by
  rw [List.take_succ_eq_append_getElem (by simpa only [mutated, Slice.set_length] using room)]
  rw [mutated_take]
  simp only [mutated, Slice.set_val_eq, List.getElem_set_self]

theorem mutated_tail (before : Slice U8) (offset : Usize) :
    (mutated before offset).val.drop (offset.val + 1) = before.val.drop (offset.val + 1) := by
  rw [mutated, Slice.set_val_eq, List.drop_set, ite_eq_left (Nat.lt_succ_self _)]

theorem rotated_header_front (before : Slice U8) (offset : Usize)
    (room : offset.val < before.length) :
    ((mutated before offset).val.take (offset.val + 1)).drop offset.val ++
      ((mutated before offset).val.take (offset.val + 1)).take offset.val =
      134#u8 :: before.val.take offset.val := by
  rw [mutated_front before offset room]
  have takeLength : (before.val.take offset.val).length = offset.val :=
    List.length_take_of_le (Nat.le_of_lt room)
  rw [List.drop_left' takeLength, List.take_left' takeLength]
  rfl

end BeaconcryptCore.Refinement.RegistrationArraySerializeSix

/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mk_raw6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mk_raw6
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.raw_argument8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.raw_argument8
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.cursor_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.cursor_value
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.cursor_sub_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.cursor_sub_one
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.write_header6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.write_header6
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.size_header6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.size_header6
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.remaining_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.remaining_value
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.entry6_to_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.entry6_to_loop
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.entry6_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.entry6_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_take
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_front' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_front
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.mutated_tail

/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySerializeSix.rotated_header_front' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySerializeSix.rotated_header_front
