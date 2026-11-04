-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The source 16-bit and 32-bit argument arithmetic, including division by 256
and reconstruction from every big-endian octet. No byte parser/serializer law is
assumed; actual header IO composition is proved separately. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord

namespace Word16

def octet (value : U16) (amount : Nat) : U8 :=
  ⟨(value.bv >>> amount).setWidth 8⟩

theorem wrapping_add (left right : U16) :
    core.num.U16.wrapping_add left right = .ok (U16.wrapping_add left right) := rfl

theorem wrapping_mul (left right : U16) :
    core.num.U16.wrapping_mul left right = .ok (U16.wrapping_mul left right) := rfl

def shr (value : U16) (amount : Nat) : U16 := ⟨value.bv >>> amount⟩

theorem divide_256 (value : U16) :
    _root_.core.num.U16.wrapping_div value 256#u16 = .ok (shr value 8) := by
  unfold _root_.core.num.U16.wrapping_div UScalar.div
  have nonzero : ((256#u16).bv != 0) = true := by decide
  rw [nonzero]
  simp only [ite_true]
  congr 1
  apply U16.bv_eq_imp_eq
  apply BitVec.eq_of_toNat_eq
  change (value.bv / (256 : BitVec 16)).toNat = (value.bv >>> 8).toNat
  rw [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shifted_octet (value : U16) (amount : Nat) :
    UScalar.cast .U8 (shr value amount) = octet value amount := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem append_bit_byte (value : BitVec 16) (byte : BitVec 8) :
    byte.setWidth 16 + value * (256 : BitVec 16) = (value ++ byte).setWidth 16 := by
  rw [show (256 : BitVec 16) = BitVec.twoPow 16 8 by decide,
    BitVec.mul_twoPow_eq_shiftLeft]
  rw [BitVec.shiftLeft_eq_concat_of_lt (by decide),
    BitVec.setWidth_eq_append (by decide)]
  change (0#8 ++ byte) + (value.extractLsb' 0 8 ++ 0#8) = (value ++ byte).setWidth 16
  rw [BitVec.zero_append_add_append_zero]
  rw [BitVec.setWidth_append]
  norm_num
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 16)]

def appendByte (value : U16) (byte : U8) : U16 :=
  U16.wrapping_add (UScalar.cast .U16 byte) (U16.wrapping_mul value 256#u16)

theorem append_byte (value : U16) (byte : U8) :
    appendByte value byte = (⟨(value.bv ++ byte.bv).setWidth 16⟩ : U16) := by
  apply U16.bv_eq_imp_eq
  change byte.bv.setWidth 16 + value.bv * (256 : BitVec 16) = _
  exact append_bit_byte value.bv byte.bv

set_option backward.isDefEq.respectTransparency false in
private theorem narrow_append_byte {width : Nat} (headBits : BitVec width) (byte : BitVec 8) :
    (headBits.setWidth 16 ++ byte).setWidth 16 = (headBits ++ byte).setWidth 16 := by
  rw [BitVec.setWidth_append, BitVec.setWidth_append]
  norm_num

def readWord (b0 b1 : U8) : U16 :=
  appendByte (UScalar.cast .U16 b0) b1

set_option backward.isDefEq.respectTransparency false in
theorem read_word_concat (b0 b1 : U8) :
    (readWord b0 b1).bv = (b0.bv ++ b1.bv) := by
  simp only [readWord, append_byte, UScalar.cast, U16.bv, BitVec.zeroExtend, UScalarTy.numBits]
  simp only [narrow_append_byte]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_word_octets (value : U16) :
    readWord (octet value 8) (octet value 0) = value := by
  apply U16.bv_eq_imp_eq
  have joined := read_word_concat (octet value 8) (octet value 0)
  refine joined.trans ?_
  simp only [octet, U8.bv, BitVec.setWidth_ushiftRight_eq_extractLsb]
  repeat' rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

end Word16

namespace Word32

def octet (value : U32) (amount : Nat) : U8 :=
  ⟨(value.bv >>> amount).setWidth 8⟩

theorem wrapping_add (left right : U32) :
    core.num.U32.wrapping_add left right = .ok (U32.wrapping_add left right) := rfl

theorem wrapping_mul (left right : U32) :
    core.num.U32.wrapping_mul left right = .ok (U32.wrapping_mul left right) := rfl

def shr (value : U32) (amount : Nat) : U32 := ⟨value.bv >>> amount⟩

theorem divide_256 (value : U32) :
    _root_.core.num.U32.wrapping_div value 256#u32 = .ok (shr value 8) := by
  unfold _root_.core.num.U32.wrapping_div UScalar.div
  have nonzero : ((256#u32).bv != 0) = true := by decide
  rw [nonzero]
  simp only [ite_true]
  congr 1
  apply U32.bv_eq_imp_eq
  apply BitVec.eq_of_toNat_eq
  change (value.bv / (256 : BitVec 32)).toNat = (value.bv >>> 8).toNat
  rw [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shifted_octet (value : U32) (amount : Nat) :
    UScalar.cast .U8 (shr value amount) = octet value amount := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem append_bit_byte (value : BitVec 32) (byte : BitVec 8) :
    byte.setWidth 32 + value * (256 : BitVec 32) = (value ++ byte).setWidth 32 := by
  rw [show (256 : BitVec 32) = BitVec.twoPow 32 8 by decide,
    BitVec.mul_twoPow_eq_shiftLeft]
  rw [BitVec.shiftLeft_eq_concat_of_lt (by decide),
    BitVec.setWidth_eq_append (by decide)]
  change (0#24 ++ byte) + (value.extractLsb' 0 24 ++ 0#8) = (value ++ byte).setWidth 32
  rw [BitVec.zero_append_add_append_zero]
  rw [BitVec.setWidth_append]
  norm_num
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 24 ≤ 32)]

def appendByte (value : U32) (byte : U8) : U32 :=
  U32.wrapping_add (UScalar.cast .U32 byte) (U32.wrapping_mul value 256#u32)

theorem append_byte (value : U32) (byte : U8) :
    appendByte value byte = (⟨(value.bv ++ byte.bv).setWidth 32⟩ : U32) := by
  apply U32.bv_eq_imp_eq
  change byte.bv.setWidth 32 + value.bv * (256 : BitVec 32) = _
  exact append_bit_byte value.bv byte.bv

set_option backward.isDefEq.respectTransparency false in
private theorem narrow_append_byte {width : Nat} (headBits : BitVec width) (byte : BitVec 8) :
    (headBits.setWidth 32 ++ byte).setWidth 32 = (headBits ++ byte).setWidth 32 := by
  rw [BitVec.setWidth_append, BitVec.setWidth_append]
  norm_num

def readWord (b0 b1 b2 b3 : U8) : U32 :=
  appendByte (appendByte (appendByte (UScalar.cast .U32 b0) b1) b2) b3

set_option backward.isDefEq.respectTransparency false in
theorem read_word_concat (b0 b1 b2 b3 : U8) :
    (readWord b0 b1 b2 b3).bv = (((b0.bv ++ b1.bv) ++ b2.bv) ++ b3.bv) := by
  simp only [readWord, append_byte, UScalar.cast, U32.bv, BitVec.zeroExtend, UScalarTy.numBits]
  simp only [narrow_append_byte]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_word_octets (value : U32) :
    readWord (octet value 24) (octet value 16) (octet value 8) (octet value 0) = value := by
  apply U32.bv_eq_imp_eq
  have joined := read_word_concat (octet value 24) (octet value 16) (octet value 8) (octet value 0)
  refine joined.trans ?_
  simp only [octet, U8.bv, BitVec.setWidth_ushiftRight_eq_extractLsb]
  repeat' rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

end Word32

end BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.wrapping_add' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.wrapping_add

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.wrapping_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.wrapping_mul

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.divide_256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.divide_256

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.shifted_octet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.shifted_octet

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.append_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.append_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.read_word_concat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.read_word_concat

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.read_word_octets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word16.read_word_octets

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.wrapping_add' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.wrapping_add

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.wrapping_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.wrapping_mul

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.divide_256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.divide_256

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.shifted_octet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.shifted_octet

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.append_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.append_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.read_word_concat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.read_word_concat

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.read_word_octets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNarrowWord.Word32.read_word_octets
