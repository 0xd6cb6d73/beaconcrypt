-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightWordValues
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightByteWords

theorem bytes_word_inverse (bytes : List Byte) :
    (BitVec.fromLEBytes bytes).toLEBytes = bytes := by
  apply List.ext_getElem
  · rw [BitVec.toLEBytes_length]
    omega
  · intro i left right
    apply (Byte.eq_iff _ _).mpr
    intro j bound
    rw [List.Inhabited_getElem_eq_getElem! _ _ left,
      BitVec.toLEBytes_getElem!_testBit _ _ _ bound, BitVec.fromLEBytes_getElem!]
    have div : (8 * i + j) / 8 = i := by omega
    have mod : (8 * i + j) % 8 = j := by omega
    rw [div, mod, List.Inhabited_getElem_eq_getElem! _ _ right]

theorem le_bytes_cast {n m : Nat} (value : BitVec n) (same : n = m) :
    (value.cast same).toLEBytes = value.toLEBytes := by
  cases same
  rfl

theorem bytes_cast {n m : Nat} (value : BitVec n) (same : n = m) :
    (value.cast same).toBEBytes = value.toBEBytes := by
  cases same
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem to_from_word (bytes : Array U8 8#usize) :
    Aeneas.Std.core.num.U64.to_be_bytes (Aeneas.Std.core.num.U64.from_be_bytes bytes) = bytes := by
  apply Subtype.ext
  unfold Aeneas.Std.core.num.U64.to_be_bytes Aeneas.Std.core.num.U64.from_be_bytes
  have width : 8 * (bytes.val.map U8.bv).length = 64 := by
    rw [List.length_map, bytes.property]
    rfl
  change ((BitVec.fromBEBytes (bytes.val.map U8.bv)).cast width).toBEBytes.map (@UScalar.mk .U8) = bytes.val
  rw [bytes_cast]
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  rw [le_bytes_cast, bytes_word_inverse, List.reverse_reverse, List.map_map]
  have identity : (fun byte : U8 => (UScalar.mk byte.bv : U8)) = id := by
    funext byte
    cases byte
    rfl
  rw [show (@UScalar.mk .U8) ∘ U8.bv = (fun byte : U8 => (UScalar.mk byte.bv : U8)) from rfl, identity, List.map_id]

set_option backward.isDefEq.respectTransparency false in
theorem to_from_word16 (bytes : Array U8 2#usize) :
    Aeneas.Std.core.num.U16.to_be_bytes (Aeneas.Std.core.num.U16.from_be_bytes bytes) = bytes := by
  apply Subtype.ext
  unfold Aeneas.Std.core.num.U16.to_be_bytes Aeneas.Std.core.num.U16.from_be_bytes
  have width : 8 * (bytes.val.map U8.bv).length = 16 := by
    rw [List.length_map, bytes.property]
    rfl
  change ((BitVec.fromBEBytes (bytes.val.map U8.bv)).cast width).toBEBytes.map (@UScalar.mk .U8) = bytes.val
  rw [bytes_cast]
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  rw [le_bytes_cast, bytes_word_inverse, List.reverse_reverse, List.map_map]
  have identity : (fun byte : U8 => (UScalar.mk byte.bv : U8)) = id := by
    funext byte
    cases byte
    rfl
  rw [show (@UScalar.mk .U8) ∘ U8.bv = (fun byte : U8 => (UScalar.mk byte.bv : U8)) from rfl, identity, List.map_id]

set_option backward.isDefEq.respectTransparency false in
theorem to_from_word32 (bytes : Array U8 4#usize) :
    Aeneas.Std.core.num.U32.to_be_bytes (Aeneas.Std.core.num.U32.from_be_bytes bytes) = bytes := by
  apply Subtype.ext
  unfold Aeneas.Std.core.num.U32.to_be_bytes Aeneas.Std.core.num.U32.from_be_bytes
  have width : 8 * (bytes.val.map U8.bv).length = 32 := by
    rw [List.length_map, bytes.property]
    rfl
  change ((BitVec.fromBEBytes (bytes.val.map U8.bv)).cast width).toBEBytes.map (@UScalar.mk .U8) = bytes.val
  rw [bytes_cast]
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  rw [le_bytes_cast, bytes_word_inverse, List.reverse_reverse, List.map_map]
  have identity : (fun byte : U8 => (UScalar.mk byte.bv : U8)) = id := by
    funext byte
    cases byte
    rfl
  rw [show (@UScalar.mk .U8) ∘ U8.bv = (fun byte : U8 => (UScalar.mk byte.bv : U8)) from rfl, identity, List.map_id]

private theorem extract_extract {w a b c d : Nat} (value : BitVec w) (bound : b + c ≤ d) :
    (value.extractLsb' a d).extractLsb' b c = value.extractLsb' (a + b) c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_extractLsb']
  intro inside
  simp [inside, show b + i < d by omega, Nat.add_assoc]

theorem word16_bytes (value : U16) :
    (Aeneas.Std.core.num.U16.to_be_bytes value).val = [RegistrationHeaderNarrowWord.Word16.octet value 8, RegistrationHeaderNarrowWord.Word16.octet value 0] := by
  change value.bv.toBEBytes.map (@UScalar.mk .U8) = _
  simp only [BitVec.toBEBytes]
  iterate 3
    rw [BitVec.toLEBytes]
    norm_num only [Nat.reduceLT, Nat.reduceSub]
    simp only [ite_true, ite_false, Nat.reduceSub]
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, RegistrationHeaderNarrowWord.Word16.octet]
  simp only [List.cons.injEq, UScalar.mk.injEq]
  simp [BitVec.setWidth_ushiftRight_eq_extractLsb]

theorem word32_bytes (value : U32) :
    (Aeneas.Std.core.num.U32.to_be_bytes value).val = [RegistrationHeaderNarrowWord.Word32.octet value 24, RegistrationHeaderNarrowWord.Word32.octet value 16, RegistrationHeaderNarrowWord.Word32.octet value 8, RegistrationHeaderNarrowWord.Word32.octet value 0] := by
  change value.bv.toBEBytes.map (@UScalar.mk .U8) = _
  simp only [BitVec.toBEBytes]
  iterate 5
    rw [BitVec.toLEBytes]
    norm_num only [Nat.reduceLT, Nat.reduceSub]
    simp only [ite_true, ite_false, Nat.reduceSub]
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, RegistrationHeaderNarrowWord.Word32.octet]
  simp only [List.cons.injEq, UScalar.mk.injEq]
  simp [BitVec.setWidth_ushiftRight_eq_extractLsb, extract_extract,
    BitVec.setWidth_extractLsb'_of_le]

end BeaconcryptCore.Refinement.RegistrationPreflightByteWords

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.bytes_word_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.bytes_word_inverse

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.le_bytes_cast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.le_bytes_cast

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.bytes_cast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.bytes_cast

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word16

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.to_from_word32

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.word16_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.word16_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightByteWords.word32_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightByteWords.word32_bytes
