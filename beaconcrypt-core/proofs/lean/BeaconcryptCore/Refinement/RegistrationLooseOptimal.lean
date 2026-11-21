-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseOrderItems
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseOptimal
open beaconcrypt_parse.cbordetveraux RegistrationLooseArgument RegistrationLooseFlatHeader

def minimal : Form → Bool
  | .short _ _ => true
  | .byte n => decide (24 ≤ n.val)
  | .word16 n => decide (256 ≤ n.val)
  | .word32 n => decide (65536 ≤ n.val)
  | .word64 n => decide (4294967296 ≤ n.val)

set_option backward.isDefEq.respectTransparency false in
theorem widen_value {type : UScalarTy} (n : UScalar type) (width : type.numBits ≤ 64) :
    (UScalar.cast .U64 n).val = n.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have bound := n.hBounds
  have powers : 2 ^ type.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) width
  change n.val < 2 ^ 64
  omega

set_option backward.isDefEq.respectTransparency false in
theorem narrow_widen {type : UScalarTy} (n : UScalar type) (width : type.numBits ≤ 64) :
    UScalar.cast type (UScalar.cast .U64 n) = n := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq, widen_value n width]
  exact Nat.mod_eq_of_lt n.hBounds

set_option backward.isDefEq.respectTransparency false in
theorem optimal_form (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    cbor_raw_ints_optimal input = .ok (minimal form) := by
  obtain ⟨front, tail, split, _, _, read⟩ := header_parts input major form rest contents majorBound notSimple
  simp only [cbor_raw_ints_optimal, jump_form input major form rest contents majorBound,
    bind_tc_ok, split, uncurry, read, get_header_major_type, header_major, notSimple, ↓reduceIte]
  cases form with
  | short n bound =>
    simp [sourceHeader, additional, lift, impl_raw_uint64_optimal, max_simple_value_additional_info,
      minimal, bind_tc_ok, UScalar.le_equiv]
    omega
  | byte n =>
    simp [sourceHeader, additional, lift, impl_raw_uint64_optimal, max_simple_value_additional_info,
      minimal, bind_tc_ok, UScalar.le_equiv, widen_value n (by decide)]
    by_cases enough : 24 ≤ n.val
    · simp only [show 23 < n.val by omega, ↓reduceIte, enough, decide_true]
    · simp only [show ¬ 23 < n.val by omega, ↓reduceIte, enough, decide_false]
  | word16 n =>
    simp [sourceHeader, additional, lift, impl_raw_uint64_optimal, max_simple_value_additional_info,
      minimal, bind_tc_ok, UScalar.le_equiv, widen_value n (by decide)]
    omega
  | word32 n =>
    simp [sourceHeader, additional, lift, impl_raw_uint64_optimal, max_simple_value_additional_info,
      minimal, bind_tc_ok, UScalar.le_equiv, widen_value n (by decide)]
    omega
  | word64 n =>
    simp [sourceHeader, additional, lift, impl_raw_uint64_optimal, max_simple_value_additional_info,
      minimal, bind_tc_ok, UScalar.le_equiv]
    omega

set_option backward.isDefEq.respectTransparency false in
theorem canonical_bytes (major : U8) (form : Form) (accepted : minimal form = true) :
    bytes major form = RegistrationHeaderCanonical.encodedBytes major (value form) := by
  cases form with
  | short n bound =>
    simp only [bytes, additional, wordBytes, value, RegistrationHeaderCanonical.encodedBytes,
      widen_value n (by decide), bound, ↓reduceIte, narrow_widen n (by decide)]
  | byte n =>
    have lower : 24 ≤ n.val := by simpa only [minimal, decide_eq_true_eq] using accepted
    have upper : n.val < 256 := n.hBounds
    have notShort : ¬ n.val < 24 := by omega
    simp only [bytes, additional, wordBytes, value, RegistrationHeaderCanonical.encodedBytes,
      widen_value n (by decide), notShort, upper, ↓reduceIte, narrow_widen n (by decide)]
  | word16 n =>
    have lower : 256 ≤ n.val := by simpa only [minimal, decide_eq_true_eq] using accepted
    have upper : n.val < 65536 := n.hBounds
    have notShort : ¬ n.val < 24 := by omega
    have notByte : ¬ n.val < 256 := by omega
    simp only [bytes, additional, wordBytes, value, RegistrationHeaderCanonical.encodedBytes,
      widen_value n (by decide), notShort, notByte, upper, ↓reduceIte,
      narrow_widen n (by decide), RegistrationPreflightByteWords.word16_bytes]
  | word32 n =>
    have lower : 65536 ≤ n.val := by simpa only [minimal, decide_eq_true_eq] using accepted
    have upper : n.val < 4294967296 := n.hBounds
    have notShort : ¬ n.val < 24 := by omega
    have notByte : ¬ n.val < 256 := by omega
    have notWord16 : ¬ n.val < 65536 := by omega
    simp only [bytes, additional, wordBytes, value, RegistrationHeaderCanonical.encodedBytes,
      widen_value n (by decide), notShort, notByte, notWord16, upper, ↓reduceIte,
      narrow_widen n (by decide), RegistrationPreflightByteWords.word32_bytes]
  | word64 n =>
    have lower : 4294967296 ≤ n.val := by simpa only [minimal, decide_eq_true_eq] using accepted
    have notShort : ¬ n.val < 24 := by omega
    have notByte : ¬ n.val < 256 := by omega
    have notWord16 : ¬ n.val < 65536 := by omega
    have notWord32 : ¬ n.val < 4294967296 := by omega
    simp only [bytes, additional, wordBytes, value, RegistrationHeaderCanonical.encodedBytes,
      notShort, notByte, notWord16, notWord32, ↓reduceIte, FrameCodecWord.word]

end BeaconcryptCore.Refinement.RegistrationLooseOptimal

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOptimal.widen_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOptimal.widen_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOptimal.narrow_widen' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOptimal.narrow_widen

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOptimal.optimal_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOptimal.optimal_form

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOptimal.canonical_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOptimal.canonical_bytes
