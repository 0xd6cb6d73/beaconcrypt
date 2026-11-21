-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderWrite
import BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual source header writes and reads for 16-bit and 32-bit arguments at
offset zero. Every written octet, untouched suffix and same-length slice is
derived from the source body; complete public codec composition remains separate. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits
open RegistrationHeaderNarrowWord
open RegistrationHeaderWrite (update_set)

private theorem add01 : core.num.Usize.wrapping_add 0#usize 1#usize = .ok 1#usize := by
  change RustM.ok (Usize.wrapping_add 0#usize 1#usize) = RustM.ok 1#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
private theorem sub11 : core.num.Usize.wrapping_sub 1#usize 1#usize = .ok 0#usize := by
  change RustM.ok (Usize.wrapping_sub 1#usize 1#usize) = RustM.ok 0#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_sub_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]


namespace Header16
private theorem low_octet (value : U16) :
    UScalar.cast .U8 value = Word16.octet value 0 := by
  simp [Word16.octet, UScalar.cast, BitVec.zeroExtend]

def written (out : Slice U8) (major : U8) (value : U16) : Slice U8 :=
  ((out.set 0#usize (packed major 25#u8)).set 1#usize (Word16.octet value 8)).set 2#usize (Word16.octet value 0)

set_option backward.isDefEq.respectTransparency false in
theorem write (out : Slice U8) (major : U8) (value : U16)
    (space : 3 ≤ out.val.length) :
    write_header (header.mk (initial_byte_t.mk major 25#u8) (.LongArgumentU16 value))
      out 0#usize = .ok (3#usize, written out major value) := by
  have sub3 : core.num.Usize.wrapping_sub 3#usize 1#usize = .ok 2#usize := by
    change RustM.ok (Usize.wrapping_sub 3#usize 1#usize) = RustM.ok 2#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub2 : core.num.Usize.wrapping_sub 2#usize 1#usize = .ok 1#usize := by
    change RustM.ok (Usize.wrapping_sub 2#usize 1#usize) = RustM.ok 1#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have addSize : core.num.Usize.wrapping_add 1#usize 2#usize = .ok 3#usize := by
    change RustM.ok (Usize.wrapping_add 1#usize 2#usize) = RustM.ok 3#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_add_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  simp only [write_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bind_tc_ok, add01, sub11, set_additional, set_major]
  have nonempty : 0 < out.val.length := by omega
  simp only [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq,
    show (0#usize).val = 0 by scalar_tac, List.getElem?_eq_getElem nonempty,
    bind_tc_ok, uncurry, additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    show (25#u8 : U8) ≠ 24#u8 by decide, ↓reduceIte, addSize, sub3, sub2, Word16.divide_256, lift]
  simp only [Word16.shifted_octet]
  rw [low_octet]
  simp (disch := scalar_tac) only [update_set, bind_tc_ok]
  rfl

theorem length (out : Slice U8) (major : U8) (value : U16) :
    (written out major value).length = out.length := by
  simp only [written, Slice.set_length]

theorem bytes (out : Slice U8) (major : U8) (value : U16)
    (space : 3 ≤ out.val.length) :
    (written out major value).val = packed major 25#u8 :: Word16.octet value 8 :: Word16.octet value 0 :: out.val.drop 3 := by
  obtain ⟨byte0, tail0, shape0⟩ := List.exists_cons_of_length_pos (l := out.val) (by omega)
  have space0 : 2 ≤ tail0.length := by
    rw [shape0] at space
    simp only [List.length_cons] at space
    omega
  obtain ⟨byte1, tail1, shape1⟩ := List.exists_cons_of_length_pos (l := tail0) (by omega)
  have space1 : 1 ≤ tail1.length := by
    rw [shape1] at space0
    simp only [List.length_cons] at space0
    omega
  obtain ⟨byte2, tail2, shape2⟩ := List.exists_cons_of_length_pos (l := tail1) (by omega)
  simp [written, Slice.set_val_eq, shape0, shape1, shape2]

theorem readback (out : Slice U8) (major : U8) (value : U16)
    (space : 3 ≤ out.val.length) (majorBound : major.val < 8) :
    read_header (written out major value) = .ok
      (header.mk (initial_byte_t.mk major 25#u8) (.LongArgumentU16 value)) := by
  exact RegistrationHeaderNarrowReadback.read_u16 _ major value _
    (bytes out major value space) majorBound

end Header16

namespace Header32
private theorem shr_twice (value : U32) (left right : Nat) :
    Word32.shr (Word32.shr value left) right = Word32.shr value (left + right) := by
  apply U32.bv_eq_imp_eq
  exact (BitVec.shiftRight_add value.bv left right).symm

private theorem low_octet (value : U32) :
    UScalar.cast .U8 value = Word32.octet value 0 := by
  simp [Word32.octet, UScalar.cast, BitVec.zeroExtend]

def written (out : Slice U8) (major : U8) (value : U32) : Slice U8 :=
  ((((out.set 0#usize (packed major 26#u8)).set 1#usize (Word32.octet value 24)).set 2#usize (Word32.octet value 16)).set 3#usize (Word32.octet value 8)).set 4#usize (Word32.octet value 0)

set_option backward.isDefEq.respectTransparency false in
theorem write (out : Slice U8) (major : U8) (value : U32)
    (space : 5 ≤ out.val.length) :
    write_header (header.mk (initial_byte_t.mk major 26#u8) (.LongArgumentU32 value))
      out 0#usize = .ok (5#usize, written out major value) := by
  have sub5 : core.num.Usize.wrapping_sub 5#usize 1#usize = .ok 4#usize := by
    change RustM.ok (Usize.wrapping_sub 5#usize 1#usize) = RustM.ok 4#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub4 : core.num.Usize.wrapping_sub 4#usize 1#usize = .ok 3#usize := by
    change RustM.ok (Usize.wrapping_sub 4#usize 1#usize) = RustM.ok 3#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub3 : core.num.Usize.wrapping_sub 3#usize 1#usize = .ok 2#usize := by
    change RustM.ok (Usize.wrapping_sub 3#usize 1#usize) = RustM.ok 2#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub2 : core.num.Usize.wrapping_sub 2#usize 1#usize = .ok 1#usize := by
    change RustM.ok (Usize.wrapping_sub 2#usize 1#usize) = RustM.ok 1#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have addSize : core.num.Usize.wrapping_add 1#usize 4#usize = .ok 5#usize := by
    change RustM.ok (Usize.wrapping_add 1#usize 4#usize) = RustM.ok 5#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_add_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  simp only [write_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bind_tc_ok, add01, sub11, set_additional, set_major]
  have nonempty : 0 < out.val.length := by omega
  simp only [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq,
    show (0#usize).val = 0 by scalar_tac, List.getElem?_eq_getElem nonempty,
    bind_tc_ok, uncurry, additional_info_long_argument_8_bits, additional_info_long_argument_16_bits, additional_info_long_argument_32_bits,
    show (26#u8 : U8) ≠ 24#u8 by decide, show (26#u8 : U8) ≠ 25#u8 by decide, ↓reduceIte, addSize, sub5, sub4, sub3, sub2, Word32.divide_256, lift]
  simp only [shr_twice, Nat.reduceAdd, Word32.shifted_octet]
  rw [low_octet]
  simp (disch := scalar_tac) only [update_set, bind_tc_ok]
  rfl

theorem length (out : Slice U8) (major : U8) (value : U32) :
    (written out major value).length = out.length := by
  simp only [written, Slice.set_length]

theorem bytes (out : Slice U8) (major : U8) (value : U32)
    (space : 5 ≤ out.val.length) :
    (written out major value).val = packed major 26#u8 :: Word32.octet value 24 :: Word32.octet value 16 :: Word32.octet value 8 :: Word32.octet value 0 :: out.val.drop 5 := by
  obtain ⟨byte0, tail0, shape0⟩ := List.exists_cons_of_length_pos (l := out.val) (by omega)
  have space0 : 4 ≤ tail0.length := by
    rw [shape0] at space
    simp only [List.length_cons] at space
    omega
  obtain ⟨byte1, tail1, shape1⟩ := List.exists_cons_of_length_pos (l := tail0) (by omega)
  have space1 : 3 ≤ tail1.length := by
    rw [shape1] at space0
    simp only [List.length_cons] at space0
    omega
  obtain ⟨byte2, tail2, shape2⟩ := List.exists_cons_of_length_pos (l := tail1) (by omega)
  have space2 : 2 ≤ tail2.length := by
    rw [shape2] at space1
    simp only [List.length_cons] at space1
    omega
  obtain ⟨byte3, tail3, shape3⟩ := List.exists_cons_of_length_pos (l := tail2) (by omega)
  have space3 : 1 ≤ tail3.length := by
    rw [shape3] at space2
    simp only [List.length_cons] at space2
    omega
  obtain ⟨byte4, tail4, shape4⟩ := List.exists_cons_of_length_pos (l := tail3) (by omega)
  simp [written, Slice.set_val_eq, shape0, shape1, shape2, shape3, shape4]

theorem readback (out : Slice U8) (major : U8) (value : U32)
    (space : 5 ≤ out.val.length) (majorBound : major.val < 8) :
    read_header (written out major value) = .ok
      (header.mk (initial_byte_t.mk major 26#u8) (.LongArgumentU32 value)) := by
  exact RegistrationHeaderNarrowReadback.read_u32 _ major value _
    (bytes out major value space) majorBound

end Header32

end BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.write

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header16.readback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.write

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite.Header32.readback
