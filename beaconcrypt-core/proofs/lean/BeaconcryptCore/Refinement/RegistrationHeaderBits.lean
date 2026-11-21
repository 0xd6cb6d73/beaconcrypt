-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
/-! Actual generated bitfield packing and initial-byte readback. Argument payload
readback and complete public codec laws are separate obligations. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderBits
open beaconcrypt_parse.cbordetveraux

theorem set_additional (value : U8) :
    set_bitfield_gen8 0#u8 0#u32 5#u32 value = .ok value := by
  simp only [set_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    lift, bind_tc_ok]
  congr 1
  apply U8.bv_eq_imp_eq
  simp [Aeneas.Std.core.num.U8.wrapping_shl, Aeneas.Std.core.num.U8.wrapping_shr,
    UScalar.wrapping_shl, UScalar.wrapping_shr]

def packed (major additional : U8) : U8 :=
  (additional &&& 31#u8) ||| Aeneas.Std.core.num.U8.wrapping_shl major 5#u32

theorem set_major (major additional : U8) :
    set_bitfield_gen8 additional 5#u32 8#u32 major = .ok (packed major additional) := by
  simp only [set_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    lift, bind_tc_ok]
  rfl

theorem pack_header (major additional : U8) :
    (do let low ← set_bitfield_gen8 0#u8 0#u32 5#u32 additional
        set_bitfield_gen8 low 5#u32 8#u32 major) = .ok (packed major additional) := by
  rw [set_additional]
  simp only [bind_tc_ok, set_major]

private theorem bits_major (major additional : BitVec 8) (bound : major.toNat < 8) :
    (((additional &&& 31) ||| (major <<< 5)) >>> 5) = major := by
  exact (by decide : ∀ x y : BitVec 8, x.toNat < 8 →
    (((y &&& 31) ||| (x <<< 5)) >>> 5) = x) major additional bound

private theorem bits_additional (major additional : BitVec 8) (bound : additional.toNat < 32) :
    (((additional &&& 31) ||| (major <<< 5)) <<< 3 >>> 3) = additional := by
  exact (by decide : ∀ x y : BitVec 8, y.toNat < 32 →
    (((y &&& 31) ||| (x <<< 5)) <<< 3 >>> 3) = y) major additional bound

theorem read_major (major additional : U8) (bound : major.val < 8) :
    get_bitfield_gen8 (packed major additional) 5#u32 8#u32 = .ok major := by
  simp only [get_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.core.num.U32.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    bind_tc_ok]
  congr 1
  apply U8.bv_eq_imp_eq
  norm_num [packed, Aeneas.Std.core.num.U8.wrapping_shl,
    Aeneas.Std.core.num.U8.wrapping_shr, UScalar.wrapping_shl, UScalar.wrapping_shr,
    U32.wrapping_sub, U32.wrapping_add, U32.size, U32.numBits, UScalarTy.numBits]
  change major.bv.toNat < 8 at bound
  change (((additional.bv &&& (31 : BitVec 8)) ||| (major.bv <<< 5)) >>> 5) = major.bv
  exact bits_major major.bv additional.bv bound

theorem read_additional (major additional : U8) (bound : additional.val < 32) :
    get_bitfield_gen8 (packed major additional) 0#u32 5#u32 = .ok additional := by
  simp only [get_bitfield_gen8, CoreModels.core.num.U32.wrapping_sub,
    CoreModels.core.num.U32.wrapping_add,
    CoreModels.rust_primitives.arithmetic.wrapping_sub_u32,
    CoreModels.rust_primitives.arithmetic.wrapping_add_u32,
    _root_.core.num.U8.wrapping_shr, _root_.core.num.U8.wrapping_shl,
    bind_tc_ok]
  congr 1
  apply U8.bv_eq_imp_eq
  norm_num [packed, Aeneas.Std.core.num.U8.wrapping_shl,
    Aeneas.Std.core.num.U8.wrapping_shr, UScalar.wrapping_shl, UScalar.wrapping_shr,
    U32.wrapping_sub, U32.wrapping_add, U32.size, U32.numBits, UScalarTy.numBits]
  change additional.bv.toNat < 32 at bound
  change (((additional.bv &&& (31 : BitVec 8)) ||| (major.bv <<< 5)) <<< 3 >>> 3) = additional.bv
  exact bits_additional major.bv additional.bv bound

end BeaconcryptCore.Refinement.RegistrationHeaderBits

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderBits.set_additional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderBits.set_additional

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderBits.set_major' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderBits.set_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderBits.pack_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderBits.pack_header

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderBits.read_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderBits.read_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderBits.read_additional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderBits.read_additional
