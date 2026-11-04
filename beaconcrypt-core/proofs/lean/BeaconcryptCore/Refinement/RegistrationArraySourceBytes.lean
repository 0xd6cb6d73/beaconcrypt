-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationArraySerialize
import BeaconcryptCore.Refinement.RegistrationArrayRotation

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

/-! Exact count-eight execution of the extracted array entry for every offset with room for its one-byte header. The theorem accounts for the returned cursor and every output byte, including the untouched suffix. It assumes no parser, readback, wrapper-allocation or desired codec law. -/

namespace BeaconcryptCore.Refinement.RegistrationArraySourceBytes
open beaconcrypt_parse.cbordetveraux RegistrationArraySerialize

theorem entry8_positive (before : Slice U8) (offset : Usize)
    (positive : 0 < offset.val) (room : offset.val < before.length) :
    ∃ after, extraction_array_entry 8#u64 before offset = .ok (cursor offset, after) ∧
      after.length = before.length ∧
      after.val = 136#u8 :: before.val.take offset.val ++ before.val.drop (offset.val + 1) := by
  obtain ⟨front, tail, back, splitSource, frontLength, tailLength, frontBytes, tailBytes, backLaw⟩ :=
    RegistrationByteCopy.split_mut_success (mutated before offset) (cursor offset) (by
      rw [cursor_value before offset room]
      simpa only [mutated, Slice.set_length] using Nat.succ_le_of_lt room)
  obtain ⟨rotated, actualRotation, rotatedLength, rotatedBytes⟩ :=
    RegistrationArrayRotation.rotate_one front offset
      (frontLength.trans (cursor_value before offset room)) positive
  refine ⟨back (rotated, tail), ?_, ?_, ?_⟩
  · rw [entry8_to_loop before offset positive room, splitSource]
    simp only [bind_tc_ok, uncurry,
      show extraction_serialize_array_loop1 offset front 1#usize front.len
        (Array.repeat 1#usize 0#usize) true = .ok rotated from actualRotation]
  · simpa only [mutated, Slice.set_length] using
      (backLaw rotated tail (rotatedLength.trans frontLength) tailLength).2
  · rw [(backLaw rotated tail (rotatedLength.trans frontLength) tailLength).1, rotatedBytes]
    simp only [frontBytes, tailBytes, cursor_value before offset room,
      rotated_header_front before offset room, mutated_tail]

theorem entry8 (before : Slice U8) (offset : Usize) (room : offset.val < before.length) :
    ∃ after, extraction_array_entry 8#u64 before offset = .ok (cursor offset, after) ∧
      after.length = before.length ∧
      after.val = 136#u8 :: before.val.take offset.val ++ before.val.drop (offset.val + 1) := by
  by_cases positive : 0 < offset.val
  · exact entry8_positive before offset positive room
  · have zero : offset = 0#usize := UScalar.eq_of_val_eq (by change offset.val = 0; omega)
    subst offset
    have cursorZero : cursor 0#usize = 1#usize := UScalar.eq_of_val_eq (by
      simpa only [show (0#usize : Usize).val = 0 from rfl,
        show (1#usize : Usize).val = 1 from rfl, Nat.zero_add]
        using cursor_value before 0#usize room)
    refine ⟨mutated before 0#usize, ?_, ?_, ?_⟩
    · simpa only [cursorZero] using entry8_zero before room
    · exact Slice.set_length _ _ _
    · simpa only [mutated, show (0#usize : Usize).val = 0 from rfl, Nat.zero_add,
        List.take_zero, List.cons_append, List.nil_append,
        show RegistrationHeaderBits.packed 4#u8 8#u8 = 136#u8 from rfl] using
        RegistrationHeaderWrite.short_bytes before 4#u8 8#u8 room

end BeaconcryptCore.Refinement.RegistrationArraySourceBytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySourceBytes.entry8_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySourceBytes.entry8_positive
/-- info: 'BeaconcryptCore.Refinement.RegistrationArraySourceBytes.entry8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArraySourceBytes.entry8
