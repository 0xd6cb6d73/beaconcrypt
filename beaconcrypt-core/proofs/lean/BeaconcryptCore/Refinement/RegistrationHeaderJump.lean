-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact source jump_header width from the packed initial byte, together
with adjacent splitting of actual standard slices. Jumping alone validates
neither payload availability nor canonical argument width. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderJump
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits RegistrationHeaderReadback

private theorem add01 : core.num.Usize.wrapping_add 0#usize 1#usize = .ok 1#usize := by
  change RustM.ok (Usize.wrapping_add 0#usize 1#usize) = RustM.ok 1#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem add11 : core.num.Usize.wrapping_add 1#usize 1#usize = .ok 2#usize := by
  change RustM.ok (Usize.wrapping_add 1#usize 1#usize) = RustM.ok 2#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem add12 : core.num.Usize.wrapping_add 1#usize 2#usize = .ok 3#usize := by
  change RustM.ok (Usize.wrapping_add 1#usize 2#usize) = RustM.ok 3#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem add14 : core.num.Usize.wrapping_add 1#usize 4#usize = .ok 5#usize := by
  change RustM.ok (Usize.wrapping_add 1#usize 4#usize) = RustM.ok 5#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem add18 : core.num.Usize.wrapping_add 1#usize 8#usize = .ok 9#usize := by
  change RustM.ok (Usize.wrapping_add 1#usize 8#usize) = RustM.ok 9#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem sub10 : core.num.Usize.wrapping_sub 1#usize 0#usize = .ok 1#usize := by
  change RustM.ok (Usize.wrapping_sub 1#usize 0#usize) = RustM.ok 1#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_sub_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

def count (additional : U8) : Usize :=
  if additional = 24#u8 then 2#usize else if additional = 25#u8 then 3#usize
  else if additional = 26#u8 then 5#usize else if additional = 27#u8 then 9#usize
  else 1#usize

set_option backward.isDefEq.respectTransparency false in
theorem jump_prefix (input : Slice U8) (major additional : U8) (rest : List U8)
    (contents : input.val = packed major additional :: rest)
    (majorBound : major.val < 8) (additionalBound : additional.val < 32) :
    jump_header input 0#usize = .ok (count additional) := by
  let empty : Slice U8 := ⟨[], by simp⟩
  have splitZero : core.slice.Slice.split_at input 0#usize = .ok (empty, input) := by
    simp [CoreModels.core.slice.Slice.split_at, CoreModels.rust_primitives.slice.slice_split_at,
      Aeneas.Std.core.slice.Slice.split_at, List.splitAt_eq, Slice.length, empty]
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := split_first input _ rest contents
  unfold jump_header
  rw [add01, splitZero]
  simp only [bind_tc_ok, uncurry, sub10]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major additional [] frontBytes majorBound additionalBound]
  simp only [bind_tc_ok, additional_info_long_argument_8_bits,
    additional_info_long_argument_16_bits, additional_info_long_argument_32_bits,
    additional_info_long_argument_64_bits, add11, add12, add14, add18]
  unfold count
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem split_prefix {A : Type} (input : Slice A) (mid : Usize) (left right : List A)
    (contents : input.val = left ++ right) (position : mid.val = left.length) :
    ∃ front tail, core.slice.Slice.split_at input mid = .ok (front, tail) ∧
      front.val = left ∧ tail.val = right := by
  have bound := input.property
  rw [contents] at bound
  simp only [List.length_append] at bound
  let front : Slice A := ⟨left, by omega⟩
  let tail : Slice A := ⟨right, by omega⟩
  refine ⟨front, tail, ?_, rfl, rfl⟩
  simp [CoreModels.core.slice.Slice.split_at, CoreModels.rust_primitives.slice.slice_split_at,
    Aeneas.Std.core.slice.Slice.split_at, contents, position, List.splitAt_eq,
    front, tail, Slice.length]

end BeaconcryptCore.Refinement.RegistrationHeaderJump

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderJump.jump_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderJump.jump_prefix
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderJump.split_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderJump.split_prefix
