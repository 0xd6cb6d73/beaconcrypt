-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationShallowExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderCanonical
import BeaconcryptCore.Refinement.RegistrationConstructorGuards
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual source ByteString factory admission, including all four quotient
checks and original raw-length construction. Every supported standard usize
length fits U64, so the original ByteString branch returns its original payload
and source-derived size. Public dispatcher equivalence remains separate. -/
namespace BeaconcryptCore.Refinement.RegistrationStringFactory
open beaconcrypt_parse cbordetveraux

def quotient (value : Usize) : Usize := ⟨UScalar.bv value / UScalar.bv (32768#usize)⟩

theorem divide (value : Usize) :
    _root_.core.num.Usize.wrapping_div value 32768#usize = .ok (quotient value) := by
  unfold _root_.core.num.Usize.wrapping_div UScalar.div
  have notZero : (32768#usize : Usize) ≠ 0#usize := by scalar_tac
  have notZeroBits : UScalar.bv (32768#usize) ≠ 0 := by
    intro zero
    apply notZero
    apply Usize.bv_eq_imp_eq
    exact zero
  have nonzero : (UScalar.bv (32768#usize) != 0) = true := bne_iff_ne.mpr notZeroBits
  rw [nonzero]
  simp only [ite_true]
  rfl

theorem quotient_value (value : Usize) : (quotient value).val = value.val / 32768 := by
  change (UScalar.bv value / UScalar.bv (32768#usize)).toNat = _
  rw [BitVec.toNat_udiv]
  change value.val / (32768#usize).val = _
  rw [show (32768#usize).val = 32768 by scalar_tac]

theorem fourth_bound (value : Usize) :
    quotient (quotient (quotient (quotient value))) < 16#usize := by
  simp only [UScalar.lt_equiv, quotient_value, show (16#usize).val = 16 by scalar_tac]
  have bound := value.hBounds
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [UScalarTy.numBits, bits] at bound <;> omega

set_option backward.isDefEq.respectTransparency false in
theorem length_cast (input : Slice U8) : (UScalar.cast .U64 input.len).val = input.length := by
  rw [UScalar.cast_val_eq, Slice.len_val]
  change input.length % (2 ^ 64) = input.length
  apply Nat.mod_eq_of_lt
  have bound := input.len.hBounds
  simp only [Slice.len_val] at bound
  change input.val.length < 2 ^ 64
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [UScalarTy.numBits, bits] at bound <;> omega

theorem factory_normal (input : Slice U8) :
    extraction_mk_byte_string input = (do
      let raw ← mk_raw_uint64 (UScalar.cast .U64 input.len)
      .ok (cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177.Some
        (.CBOR_Case_String (cbor_string.mk cbor_major_type_byte_string raw.size input)))) := by
  simp only [extraction_mk_byte_string, core.slice.Slice.len,
    rust_primitives.slice.slice_length, divide, bind_tc_ok, fourth_bound, ↓reduceIte, lift]

theorem factory_exists (input : Slice U8) :
    ∃ size, extraction_mk_byte_string input = .ok
      (cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177.Some
        (.CBOR_Case_String (cbor_string.mk cbor_major_type_byte_string size input))) ∧
      mk_raw_uint64 (UScalar.cast .U64 input.len) = .ok
        (raw_uint64.mk size (UScalar.cast .U64 input.len)) := by
  obtain ⟨size, raw⟩ := RegistrationConstructorGuards.mk_raw_exists (UScalar.cast .U64 input.len)
  refine ⟨size, ?_, raw⟩
  rw [factory_normal, raw]
  rfl

end BeaconcryptCore.Refinement.RegistrationStringFactory

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.divide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.divide

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.quotient_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.quotient_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.fourth_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.fourth_bound

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.length_cast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.length_cast

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.factory_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.factory_normal

/-- info: 'BeaconcryptCore.Refinement.RegistrationStringFactory.factory_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationStringFactory.factory_exists
