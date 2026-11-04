-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderReadback
import BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual original header reader on every 16-bit and 32-bit octet prefix,
with arbitrary following bytes and ordinary major-type bounds. Canonical width
validation and complete public codecs are separate obligations. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits RegistrationHeaderReadback
open RegistrationHeaderNarrowWord

set_option backward.isDefEq.respectTransparency false in
theorem read_u16 (input : Slice U8) (major : U8) (value : U16) (rest : List U8)
    (contents : input.val = packed major 25#u8 :: Word16.octet value 8 :: Word16.octet value 0 :: rest)
    (majorBound : major.val < 8) :
    read_header input = .ok (header.mk (initial_byte_t.mk major 25#u8) (.LongArgumentU16 value)) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_first input _ _ contents
  unfold read_header
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major 25#u8 [] frontBytes majorBound (by scalar_tac)]
  simp only [bind_tc_ok, additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    show (25#u8 : U8) ≠ 24#u8 by decide, ↓reduceIte]
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, tailBytes,
    Word16.wrapping_mul, Word16.wrapping_add, lift]
  change Word16.readWord (Word16.octet value 8) (Word16.octet value 0) = value
  exact Word16.read_word_octets value

set_option backward.isDefEq.respectTransparency false in
theorem read_u32 (input : Slice U8) (major : U8) (value : U32) (rest : List U8)
    (contents : input.val = packed major 26#u8 :: Word32.octet value 24 :: Word32.octet value 16 :: Word32.octet value 8 :: Word32.octet value 0 :: rest)
    (majorBound : major.val < 8) :
    read_header input = .ok (header.mk (initial_byte_t.mk major 26#u8) (.LongArgumentU32 value)) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_first input _ _ contents
  unfold read_header
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major 26#u8 [] frontBytes majorBound (by scalar_tac)]
  simp only [bind_tc_ok, additional_info_long_argument_8_bits, additional_info_long_argument_16_bits, additional_info_long_argument_32_bits,
    show (26#u8 : U8) ≠ 24#u8 by decide, show (26#u8 : U8) ≠ 25#u8 by decide, ↓reduceIte]
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
  simp only [sub3, sub2, bind_tc_ok]
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, tailBytes,
    Word32.wrapping_mul, Word32.wrapping_add, lift]
  change Word32.readWord (Word32.octet value 24) (Word32.octet value 16) (Word32.octet value 8) (Word32.octet value 0) = value
  exact Word32.read_word_octets value

end BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback.read_u16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback.read_u16

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback.read_u32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowReadback.read_u32
