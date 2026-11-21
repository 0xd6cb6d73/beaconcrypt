-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightWordValues
import BeaconcryptCore.Refinement.RegistrationBytePrimitives
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual checked signed-count shift and direct low-bit mask used by handwritten preflight agree with the original generated header bitfield reader. Existing source header bit proofs therefore identify both major type and additional information without replacing the parser. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits
open beaconcrypt_parse cbordetveraux RegistrationHeaderBits

theorem shift_field (value : U8) :
    (value >>> 5#i32 : RustM U8) = get_bitfield_gen8 value 5#u32 8#u32 := by
  change UScalar.shiftRight_IScalar value 5#i32 = _
  simp [get_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.core.num.U32.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    UScalar.shiftRight_IScalar, UScalar.shiftRight, IScalar.toNat,
    Aeneas.Std.core.num.U8.wrapping_shl, Aeneas.Std.core.num.U8.wrapping_shr,
    UScalar.wrapping_shl, UScalar.wrapping_shr, U32.wrapping_sub, U32.wrapping_add,
    U32.size, U32.numBits, UScalarTy.numBits, bind_tc_ok]

theorem mask_field (value : U8) :
    .ok (value &&& 31#u8) = get_bitfield_gen8 value 0#u32 5#u32 := by
  simp only [get_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.core.num.U32.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    bind_tc_ok]
  congr 1
  apply U8.bv_eq_imp_eq
  norm_num [Aeneas.Std.core.num.U8.wrapping_shl, Aeneas.Std.core.num.U8.wrapping_shr,
    UScalar.wrapping_shl, UScalar.wrapping_shr, U32.wrapping_sub, U32.wrapping_add,
    U32.size, U32.numBits, UScalarTy.numBits]
  exact (by decide : ∀ x : BitVec 8, x &&& 31 = (x <<< 3) >>> 3) value.bv

theorem packed_shift (major additional : U8) (bound : major.val < 8) :
    (packed major additional >>> 5#i32 : RustM U8) = .ok major := by
  rw [shift_field, read_major major additional bound]

theorem packed_mask (major additional : U8) (bound : additional.val < 32) :
    packed major additional &&& 31#u8 = additional := by
  have source := read_additional major additional bound
  rw [← mask_field] at source
  exact RustM.ok.inj source
end BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.shift_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.shift_field

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.mask_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.mask_field

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.packed_shift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.packed_shift

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.packed_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits.packed_mask
