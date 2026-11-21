-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecWord

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecEndian

open FrameCodecWord

private theorem bitvec_roundtrip (value : BitVec 64) :
    (BitVec.fromBEBytes value.toBEBytes).toNat = value.toNat := by
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast]
  rw [BitVec.toBEBytes, List.reverse_reverse, BitVec.fromLEBytes_toLEBytes (by decide), BitVec.toNat_cast]

/-- All eight canonical big-endian octets reconstruct the original scalar. -/
theorem from_word (value : U64) :
    CoreModels.core.num.U64.from_be_bytes (word value) = ok value := by
  change ok (Aeneas.Std.core.num.U64.from_be_bytes (word value)) = ok value
  have encoded : Aeneas.Std.core.num.U64.to_be_bytes value = word value :=
    RustM.ok.inj (word_exact value)
  congr 1
  rw [← encoded]
  apply U64.bv_eq_imp_eq
  apply BitVec.eq_of_toNat_eq
  dsimp only [Aeneas.Std.core.num.U64.from_be_bytes]
  rw [BitVec.toNat_cast]
  change (BitVec.fromBEBytes ((value.bv.toBEBytes.map (@UScalar.mk .U8)).map U8.bv)).toNat = value.bv.toNat
  rw [List.map_map]
  change (BitVec.fromBEBytes (List.map id value.bv.toBEBytes)).toNat = value.bv.toNat
  rw [List.map_id]
  exact bitvec_roundtrip value.bv

/-- Octets above a scalar's admitted width are exactly zero. -/
theorem octet_zero (value : U64) (offset : Nat) (bound : value.val < 2 ^ offset) :
    octet value offset = 0#u8 := by
  apply U8.bv_eq_imp_eq
  apply BitVec.eq_of_toNat_eq
  change ((value.bv >>> offset).setWidth 8).toNat = 0
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change value.bv.toNat < 2 ^ offset at bound
  rw [Nat.div_eq_of_lt bound]

/-- A canonical two-octet argument reconstructs its admitted scalar with six leading zeros. -/
theorem from_padded_two (value : U64) (bound : value.val ≤ 65_535) :
    CoreModels.core.num.U64.from_be_bytes
      ⟨[0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, octet value 8, octet value 0], by simp⟩ = ok value := by
  simpa only [word, octet_zero value 56 (by omega), octet_zero value 48 (by omega),
    octet_zero value 40 (by omega), octet_zero value 32 (by omega),
    octet_zero value 24 (by omega), octet_zero value 16 (by omega)] using from_word value

/-- A canonical four-octet argument reconstructs its admitted scalar with four leading zeros. -/
theorem from_padded_four (value : U64) (bound : value.val ≤ 4_294_967_295) :
    CoreModels.core.num.U64.from_be_bytes
      ⟨[0#u8, 0#u8, 0#u8, 0#u8, octet value 24, octet value 16, octet value 8, octet value 0], by simp⟩ =
      ok value := by
  simpa only [word, octet_zero value 56 (by omega), octet_zero value 48 (by omega),
    octet_zero value 40 (by omega), octet_zero value 32 (by omega)] using from_word value

end BeaconcryptCore.Refinement.FrameCodecEndian

/-- info: 'BeaconcryptCore.Refinement.FrameCodecEndian.from_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecEndian.from_word

/-- info: 'BeaconcryptCore.Refinement.FrameCodecEndian.octet_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecEndian.octet_zero

/-- info: 'BeaconcryptCore.Refinement.FrameCodecEndian.from_padded_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecEndian.from_padded_two

/-- info: 'BeaconcryptCore.Refinement.FrameCodecEndian.from_padded_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecEndian.from_padded_four
