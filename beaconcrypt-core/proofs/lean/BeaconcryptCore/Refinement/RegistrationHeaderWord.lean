-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs
import BeaconcryptCore.Refinement.FrameCodecWord
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact standard arithmetic and source big-endian word steps. Dividing by 256
produces the source high octets; the source multiply/add recurrence reconstructs
all eight octets of an arbitrary U64. Actual slice/header IO and complete public
codec/source composition are separate obligations. All checking is in the kernel. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderWord
open FrameCodecWord

theorem wrapping_add (left right : U64) :
    core.num.U64.wrapping_add left right = .ok (U64.wrapping_add left right) := rfl

theorem wrapping_mul (left right : U64) :
    core.num.U64.wrapping_mul left right = .ok (U64.wrapping_mul left right) := rfl

def shr (value : U64) (amount : Nat) : U64 := ⟨value.bv >>> amount⟩

theorem divide_256 (value : U64) :
    _root_.core.num.U64.wrapping_div value 256#u64 = .ok (shr value 8) := by
  unfold _root_.core.num.U64.wrapping_div UScalar.div
  have nonzero : ((256#u64).bv != 0) = true := by decide
  rw [nonzero]
  simp only [ite_true]
  congr 1
  apply U64.bv_eq_imp_eq
  apply BitVec.eq_of_toNat_eq
  change (value.bv / (256 : BitVec 64)).toNat = (value.bv >>> 8).toNat
  rw [BitVec.toNat_udiv, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

theorem shifted_octet (value : U64) (amount : Nat) :
    UScalar.cast .U8 (shr value amount) = octet value amount := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem append_bit_byte (value : BitVec 64) (byte : BitVec 8) :
    byte.setWidth 64 + value * (256 : BitVec 64) = (value ++ byte).setWidth 64 := by
  rw [show (256 : BitVec 64) = BitVec.twoPow 64 8 by decide,
    BitVec.mul_twoPow_eq_shiftLeft]
  rw [BitVec.shiftLeft_eq_concat_of_lt (by decide),
    BitVec.setWidth_eq_append (by decide)]
  change (0#56 ++ byte) + (value.extractLsb' 0 56 ++ 0#8) = (value ++ byte).setWidth 64
  rw [BitVec.zero_append_add_append_zero]
  rw [BitVec.setWidth_append]
  norm_num
  rw [BitVec.setWidth_eq_extractLsb' (by decide : 56 ≤ 64)]

def appendByte (value : U64) (byte : U8) : U64 :=
  U64.wrapping_add (UScalar.cast .U64 byte) (U64.wrapping_mul value 256#u64)

theorem append_byte (value : U64) (byte : U8) :
    appendByte value byte = (⟨(value.bv ++ byte.bv).setWidth 64⟩ : U64) := by
  apply U64.bv_eq_imp_eq
  change byte.bv.setWidth 64 + value.bv * (256 : BitVec 64) = _
  exact append_bit_byte value.bv byte.bv

set_option backward.isDefEq.respectTransparency false in
private theorem narrow_append_byte {width : Nat} (headBits : BitVec width) (byte : BitVec 8) :
    (headBits.setWidth 64 ++ byte).setWidth 64 = (headBits ++ byte).setWidth 64 := by
  rw [BitVec.setWidth_append, BitVec.setWidth_append]
  norm_num

def readWord8 (b0 b1 b2 b3 b4 b5 b6 b7 : U8) : U64 :=
  appendByte (appendByte (appendByte (appendByte (appendByte (appendByte
    (appendByte (UScalar.cast .U64 b0) b1) b2) b3) b4) b5) b6) b7

set_option backward.isDefEq.respectTransparency false in
theorem read_word_concat (b0 b1 b2 b3 b4 b5 b6 b7 : U8) :
    (readWord8 b0 b1 b2 b3 b4 b5 b6 b7).bv =
      ((((((b0.bv ++ b1.bv) ++ b2.bv) ++ b3.bv) ++ b4.bv) ++ b5.bv) ++ b6.bv) ++ b7.bv := by
  simp only [readWord8, append_byte, UScalar.cast, U64.bv, BitVec.zeroExtend, UScalarTy.numBits]
  simp only [narrow_append_byte]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_word_octets (value : U64) :
    readWord8 (octet value 56) (octet value 48) (octet value 40) (octet value 32)
      (octet value 24) (octet value 16) (octet value 8) (octet value 0) = value := by
  apply U64.bv_eq_imp_eq
  have joined := read_word_concat (octet value 56) (octet value 48) (octet value 40)
    (octet value 32) (octet value 24) (octet value 16) (octet value 8) (octet value 0)
  refine joined.trans ?_
  simp only [octet, U8.bv, BitVec.setWidth_ushiftRight_eq_extractLsb]
  repeat' rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

end BeaconcryptCore.Refinement.RegistrationHeaderWord

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.wrapping_add' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.wrapping_add
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.wrapping_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.wrapping_mul
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.divide_256' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.divide_256
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.shifted_octet' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.shifted_octet
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.append_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.append_byte
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.read_word_concat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.read_word_concat
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWord.read_word_octets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWord.read_word_octets
