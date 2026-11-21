-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecArgument
import BeaconcryptCore.Computational.CborTransport
import BeaconcryptCore.Refinement.Transport

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse PqxdhRefinement
open BeaconcryptCore.Refinement.FrameCodecWord
open BeaconcryptCore.Refinement.FrameCodecArgument
open BeaconcryptCore.Computational

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecRepresentation

/-- The actual shifted word byte has the exact natural-number byte interpretation of the codec model. -/
theorem octet_abs (value : U64) (offset : Nat) :
    absByte (octet value (8 * offset)) = UInt8.ofNat (value.val / 256 ^ offset % 256) := by
  change UInt8.ofNat (((value.bv >>> (8 * offset)).setWidth 8).toNat) = _
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  rfl

/-- The canonical major and information bits denote exactly their CBOR byte value. -/
theorem header_abs (major information : U8) (majorBound : major.val ≤ 7)
    (informationBound : information.val ≤ 31) :
    absByte (header major information) = UInt8.ofNat (32 * major.val + information.val) := by
  change UInt8.ofNat ((major.bv <<< 5 ||| information.bv).toNat) = _
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  norm_num only [Nat.reducePow]
  have small : major.bv.toNat * 32 < 256 := by change major.val * 32 < 256; omega
  rw [Nat.mod_eq_of_lt small]
  apply congrArg UInt8.ofNat
  change major.val * 32 ||| information.val = 32 * major.val + information.val
  rw [Nat.mul_comm major.val 32]
  simpa only [Nat.reducePow] using
    (Nat.two_pow_add_eq_or_of_lt (i := 5) (b := information.val) (by omega) major.val).symm

theorem bigEndian_abs (value : U64) (width : Nat) :
    (List.range width).reverse.map (fun offset => absByte (octet value (8 * offset))) =
      CborTransport.bigEndian width value.val := by
  simp only [octet_abs, CborTransport.bigEndian]

/-- The exact emitted native argument bytes realize the existing mathematical CBOR argument. -/
theorem argument_abs (major : U8) (value : U64) (domain : major = 0#u8 ∨ major = 2#u8) :
    (argumentBytes major value).map absByte = CborTransport.argument major.val value.val := by
  have majorBound : major.val ≤ 7 := by rcases domain with rfl | rfl <;> decide
  unfold argumentBytes encoded CborTransport.argument
  simp only [UScalar.le_equiv, UScalar.ofNatCore_val_eq]
  split_ifs with inline octetWidth shortWidth wordWidth
  · let information : U8 := ⟨value.bv.setWidth 8⟩
    have informationValue : information.val = value.val := by
      change (value.bv.setWidth 8).toNat = value.val
      rw [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by change value.val < 256; omega)
    change [absByte (header major information)] = _
    rw [header_abs major information majorBound (by rw [informationValue]; omega), informationValue]
  · change absByte (header major 24#u8) ::
      (List.range 1).reverse.map (fun offset => absByte (octet value (8 * offset))) = _
    rw [header_abs major 24#u8 majorBound (by decide), bigEndian_abs]
    rfl
  · change absByte (header major 25#u8) ::
      (List.range 2).reverse.map (fun offset => absByte (octet value (8 * offset))) = _
    rw [header_abs major 25#u8 majorBound (by decide), bigEndian_abs]
    rfl
  · change absByte (header major 26#u8) ::
      (List.range 4).reverse.map (fun offset => absByte (octet value (8 * offset))) = _
    rw [header_abs major 26#u8 majorBound (by decide), bigEndian_abs]
    rfl
  · change absByte (header major 27#u8) ::
      (List.range 8).reverse.map (fun offset => absByte (octet value (8 * offset))) = _
    rw [header_abs major 27#u8 majorBound (by decide), bigEndian_abs]
    rfl

/-- The canonical bytes emitted by the native frame codec, before any external allocation. -/
def frameBytes (sequence sender : U64) (payload : Slice U8) : List U8 :=
  [133#u8, 1#u8, 2#u8] ++ argumentBytes 0#u8 sequence ++ argumentBytes 0#u8 sender ++
    argumentBytes 2#u8 (UScalar.cast .U64 payload.len) ++ payload.val

/-- Native canonical frame bytes represent exactly the frame rendering used by the existing computational codec. -/
theorem frame_abs (sequence sender : U64) (payload : Slice U8) :
    (frameBytes sequence sender payload).map absByte =
      CborTransport.render ⟨sequence, sender, payload.val.map absByte⟩ := by
  have representable : (payload.val.map absByte).length < 2 ^ 64 := by
    have bound := (UScalar.cast .U64 payload.len).bv.isLt
    change (UScalar.cast .U64 payload.len).val < 2 ^ 64 at bound
    rw [BeaconcryptCore.Refinement.Transport.usize_to_u64_value, Slice.len_val] at bound
    simpa only [List.length_map, Slice.length] using bound
  unfold frameBytes CborTransport.render
  rw [ite_eq_left representable]
  simp only [List.map_append,
    argument_abs 0#u8 sequence (Or.inl rfl), argument_abs 0#u8 sender (Or.inl rfl),
    argument_abs 2#u8 (UScalar.cast .U64 payload.len) (Or.inr rfl),
    BeaconcryptCore.Refinement.Transport.usize_to_u64_value, Slice.len_val, Slice.length, List.length_map]
  rfl

end BeaconcryptCore.Refinement.FrameCodecRepresentation

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRepresentation.octet_abs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRepresentation.octet_abs

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRepresentation.header_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRepresentation.header_abs

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRepresentation.bigEndian_abs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRepresentation.bigEndian_abs

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRepresentation.argument_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRepresentation.argument_abs

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRepresentation.frame_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRepresentation.frame_abs
