-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightWord
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Generic octet preservation under widening gives exact fixed-word images of U8, U16 and U32 values. Combining the actual mutable argument-word implementation with original standard from_be_bytes proves every long-argument width, including arbitrary U64 values. No minimal-width or parser success law is a premise. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightWordValues
open beaconcrypt_parse RegistrationPreflightWord

def octet {type : UScalarTy} (value : UScalar type) (amount : Nat) : U8 :=
  ⟨(value.bv >>> amount).setWidth 8⟩

set_option backward.isDefEq.respectTransparency false in
theorem cast_octet {type : UScalarTy} (value : UScalar type) (amount : Nat) (width : type.numBits ≤ 64) :
    FrameCodecWord.octet (UScalar.cast .U64 value) amount = octet value amount := by
  apply UScalar.eq_of_val_eq
  change (((UScalar.cast .U64 value).bv >>> amount).setWidth 8).toNat =
    ((value.bv >>> amount).setWidth 8).toNat
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  change ((UScalar.cast .U64 value).val >>> amount) % 256 = (value.val >>> amount) % 256
  have fits : value.val < 2 ^ 64 := by
    have bound := value.hBounds
    have powers : 2 ^ type.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) width
    omega
  rw [UScalar.cast_val_eq]
  change ((value.val % 2 ^ 64) >>> amount) % 256 = (value.val >>> amount) % 256
  rw [Nat.mod_eq_of_lt fits]

theorem octet_zero {type : UScalarTy} (value : UScalar type) (amount : Nat) (width : type.numBits ≤ amount) :
    octet value amount = 0#u8 := by
  unfold octet
  rw [BitVec.ushiftRight_eq_zero width]
  apply UScalar.eq_of_val_eq
  change ((0 : BitVec type.numBits).setWidth 8).toNat = 0
  simp

theorem octet_low (value : U8) : octet value 0 = value := by
  unfold octet
  simp only [BitVec.ushiftRight_zero]
  rfl
theorem word_byte (value : U8) :
    (FrameCodecWord.word (UScalar.cast .U64 value)).val =
      [ 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, value ] := by
  have lower (amount : Nat) := cast_octet value amount (by decide)
  simp only [FrameCodecWord.word, lower]
  simp only [octet_zero value 56 (by decide), octet_zero value 48 (by decide), octet_zero value 40 (by decide), octet_zero value 32 (by decide), octet_zero value 24 (by decide), octet_zero value 16 (by decide), octet_zero value 8 (by decide), octet_low]

set_option backward.isDefEq.respectTransparency false in
theorem argument_byte (input : Slice U8) (value : U8)
    (contents : input.val = [ value ]) :
    beaconcrypt_parse.extraction_argument_word input 1#usize = .ok (UScalar.cast .U64 value) := by
  have length : input.length = (1#usize).val := by simp [Slice.length, contents]
  have same : padded input 1#usize length (by decide) = FrameCodecWord.word (UScalar.cast .U64 value) := by
    apply Subtype.ext
    rw [word_byte]
    change List.replicate 7 0#u8 ++ input.val = _
    rw [contents]
    rfl
  rw [argument_word input 1#usize length (by decide), same, from_word]

theorem word_word16 (value : U16) :
    (FrameCodecWord.word (UScalar.cast .U64 value)).val =
      [ 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, RegistrationHeaderNarrowWord.Word16.octet value 8, RegistrationHeaderNarrowWord.Word16.octet value 0 ] := by
  have lower (amount : Nat) := cast_octet value amount (by decide)
  simp only [FrameCodecWord.word, lower]
  simp only [octet_zero value 56 (by decide), octet_zero value 48 (by decide), octet_zero value 40 (by decide), octet_zero value 32 (by decide), octet_zero value 24 (by decide), octet_zero value 16 (by decide)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem argument_word16 (input : Slice U8) (value : U16)
    (contents : input.val = [ RegistrationHeaderNarrowWord.Word16.octet value 8, RegistrationHeaderNarrowWord.Word16.octet value 0 ]) :
    beaconcrypt_parse.extraction_argument_word input 2#usize = .ok (UScalar.cast .U64 value) := by
  have length : input.length = (2#usize).val := by simp [Slice.length, contents]
  have same : padded input 2#usize length (by decide) = FrameCodecWord.word (UScalar.cast .U64 value) := by
    apply Subtype.ext
    rw [word_word16]
    change List.replicate 6 0#u8 ++ input.val = _
    rw [contents]
    rfl
  rw [argument_word input 2#usize length (by decide), same, from_word]

theorem word_word32 (value : U32) :
    (FrameCodecWord.word (UScalar.cast .U64 value)).val =
      [ 0#u8, 0#u8, 0#u8, 0#u8, RegistrationHeaderNarrowWord.Word32.octet value 24, RegistrationHeaderNarrowWord.Word32.octet value 16, RegistrationHeaderNarrowWord.Word32.octet value 8, RegistrationHeaderNarrowWord.Word32.octet value 0 ] := by
  have lower (amount : Nat) := cast_octet value amount (by decide)
  simp only [FrameCodecWord.word, lower]
  simp only [octet_zero value 56 (by decide), octet_zero value 48 (by decide), octet_zero value 40 (by decide), octet_zero value 32 (by decide)]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem argument_word32 (input : Slice U8) (value : U32)
    (contents : input.val = [ RegistrationHeaderNarrowWord.Word32.octet value 24, RegistrationHeaderNarrowWord.Word32.octet value 16, RegistrationHeaderNarrowWord.Word32.octet value 8, RegistrationHeaderNarrowWord.Word32.octet value 0 ]) :
    beaconcrypt_parse.extraction_argument_word input 4#usize = .ok (UScalar.cast .U64 value) := by
  have length : input.length = (4#usize).val := by simp [Slice.length, contents]
  have same : padded input 4#usize length (by decide) = FrameCodecWord.word (UScalar.cast .U64 value) := by
    apply Subtype.ext
    rw [word_word32]
    change List.replicate 4 0#u8 ++ input.val = _
    rw [contents]
    rfl
  rw [argument_word input 4#usize length (by decide), same, from_word]

set_option backward.isDefEq.respectTransparency false in
theorem argument_word64 (input : Slice U8) (value : U64)
    (contents : input.val = (FrameCodecWord.word value).val) :
    beaconcrypt_parse.extraction_argument_word input 8#usize = .ok value := by
  have length : input.length = (8#usize).val := by
    rw [Slice.length, contents]
    exact (FrameCodecWord.word value).property
  have same : padded input 8#usize length (by decide) = FrameCodecWord.word value := by
    apply Subtype.ext
    exact contents
  rw [argument_word input 8#usize length (by decide), same, from_word]

end BeaconcryptCore.Refinement.RegistrationPreflightWordValues

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.cast_octet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.cast_octet

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.octet_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.octet_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.octet_low' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.octet_low

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_word16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_word16

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word16

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_word32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.word_word32

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word32

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWordValues.argument_word64
