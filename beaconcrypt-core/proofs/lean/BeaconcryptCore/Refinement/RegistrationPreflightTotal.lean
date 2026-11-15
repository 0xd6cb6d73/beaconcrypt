-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightSix
import BeaconcryptCore.Refinement.RegistrationPreflightFour
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightTotal
open beaconcrypt_parse RegistrationHeaderBits

def major (byte : U8) : U8 := ⟨byte.bv >>> 5⟩
def additional (byte : U8) : U8 := byte &&& 31#u8

set_option backward.isDefEq.respectTransparency false in
theorem unpack (byte : U8) : packed (major byte) (additional byte) = byte := by
  apply U8.bv_eq_imp_eq
  change (((byte.bv &&& (31 : BitVec 8)) &&& 31) ||| ((byte.bv >>> 5) <<< 5)) = byte.bv
  exact (by decide : ∀ value : BitVec 8, (((value &&& 31) &&& 31) ||| ((value >>> 5) <<< 5)) = value) byte.bv

theorem major_bound (byte : U8) : (major byte).val < 8 := by
  change (byte.bv >>> 5).toNat < 8
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have bound := byte.hBounds
  change byte.val < 256 at bound
  change byte.val / 32 < 8
  omega

theorem additional_bound (byte : U8) : (additional byte).val < 32 := by
  change (byte.bv &&& (31 : BitVec 8)).toNat < 32
  exact (by decide : ∀ value : BitVec 8, (value &&& 31).toNat < 32) byte.bv

set_option backward.isDefEq.respectTransparency false in
theorem argument_total (input : Slice U8) (declared : U8) :
    ∃ result, primitive_argument input declared = .ok result := by
  cases contents : input.val with
  | nil => exact ⟨.None, RegistrationPreflightArgument.empty input declared contents⟩
  | cons byte rest =>
    have sourceBytes : input.val = packed (major byte) (additional byte) :: rest := by rw [unpack]; exact contents
    by_cases same : major byte = declared
    · obtain ⟨tail, _, source⟩ := RegistrationPreflightArgument.prefix_step input (major byte) (additional byte) rest
        sourceBytes (major_bound byte) (additional_bound byte)
      obtain ⟨result, normal⟩ := RegistrationPreflightArgument.after_total (additional byte) tail (additional_bound byte)
      refine ⟨result, ?_⟩
      rw [← same, source, normal]
    · exact ⟨.None, RegistrationPreflightArgument.mismatch input (major byte) declared (additional byte) rest
        sourceBytes (major_bound byte) same⟩

set_option backward.isDefEq.respectTransparency false in
theorem try_usize_total (value : U64) :
    ∃ result, core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from value = .ok result := by
  simp only [core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, lift, bind_tc_ok]
  split_ifs <;> exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem suffix_total (input : Slice U8) (start : Usize) :
    ∃ result, core.slice.Slice.get (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      input { start := start } = .ok result := by
  by_cases bound : start.val ≤ input.length
  · exact ⟨_, RegistrationPreflightFields.get_suffix input start bound⟩
  · have outside : ¬ start ≤ input.len := by simpa only [UScalar.le_equiv, Slice.len_val] using bound
    exact ⟨.None, by simp only [core.slice.Slice.get,
      core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
      rust_primitives.slice.slice_length, bind_tc_ok, outside, ↓reduceIte]⟩

set_option backward.isDefEq.respectTransparency false in
theorem field_total (input : Slice U8) (declared : U8) :
    ∃ result, extraction_preflight_field input declared = .ok result := by
  obtain ⟨argument, run⟩ := argument_total input declared
  cases argument with
  | none => exact ⟨.None, by simp only [extraction_preflight_field, run, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
  | some pair =>
    rcases pair with ⟨value, rest⟩
    by_cases string : declared = 2#u8
    · subst declared
      obtain ⟨converted, convertRun⟩ := try_usize_total value
      cases converted with
      | Err error => exact ⟨.None, by simp only [extraction_preflight_field, run, bind_tc_ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          uncurry, ↓reduceIte, convertRun, core.result.Result.ok,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
      | Ok count =>
        obtain ⟨result, getRun⟩ := suffix_total rest count
        refine ⟨result, ?_⟩
        cases result <;> simp only [extraction_preflight_field, run, bind_tc_ok,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          uncurry, ↓reduceIte, convertRun, core.result.Result.ok, getRun,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
    · exact ⟨.Some rest, by simp only [extraction_preflight_field, run, bind_tc_ok,
        core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        uncurry, string, ↓reduceIte]⟩

set_option backward.isDefEq.respectTransparency false in
theorem strip_total (input start : Slice U8) :
    ∃ result, extraction_strip_prefix input start = .ok result := by
  by_cases bound : start.len ≤ input.len
  · have inside : start.length ≤ input.length := by simpa only [UScalar.le_equiv, Slice.len_val] using bound
    obtain ⟨front, tail, split, _, _⟩ := RegistrationHeaderJump.split_prefix input start.len
      (input.val.take start.length) (input.val.drop start.length) (List.take_append_drop _ _).symm
      (by rw [List.length_take, Nat.min_eq_left inside, Slice.len_val])
    simp only [extraction_strip_prefix, core.slice.Slice.len, rust_primitives.slice.slice_length,
      bind_tc_ok, bound, ↓reduceIte, split, uncurry, RegistrationBytePrimitives.slice_eq_exact]
    split_ifs <;> exact ⟨_, rfl⟩
  · exact ⟨.None, by simp only [extraction_strip_prefix, core.slice.Slice.len,
      rust_primitives.slice.slice_length, bind_tc_ok, bound, ↓reduceIte]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem complete_total (input start : Slice U8) (a0 a1 a2 a3 a4 a5 : U8) :
    ∃ result, preflight input start (RegistrationPreflightSix.kinds a0 a1 a2 a3 a4 a5) = .ok result := by
  by_cases admitted : input.length ≤ 33554432
  · have cap : beaconcrypt_core.transport.complete_message_size_admitted input.len = .ok true := by
      rw [BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact]
      simp only [Slice.len_val, admitted, decide_true]
    obtain ⟨r0, run0⟩ := strip_total input start
    cases r0 with
    | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
    | some tail0 =>
      obtain ⟨r1, run1⟩ := field_total tail0 a0
      cases r1 with
      | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
      | some tail1 =>
        obtain ⟨r2, run2⟩ := field_total tail1 a1
        cases r2 with
        | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
        | some tail2 =>
          obtain ⟨r3, run3⟩ := field_total tail2 a2
          cases r3 with
          | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
          | some tail3 =>
            obtain ⟨r4, run4⟩ := field_total tail3 a3
            cases r4 with
            | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
            | some tail4 =>
              obtain ⟨r5, run5⟩ := field_total tail4 a4
              cases r5 with
              | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
              | some tail5 =>
                obtain ⟨r6, run6⟩ := field_total tail5 a5
                cases r6 with
                | none => exact ⟨.None, by simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, run6, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
                | some tail6 =>
                  refine ⟨if tail6.len = 0#usize then .Some () else .None, ?_⟩
                  simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, run6, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.slice.Slice.is_empty, RegistrationCodecStandardSlices.thenSomeUnit]
                  split_ifs <;> rfl
  · refine ⟨.None, ?_⟩
    simp only [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length,
      BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact,
      bind_tc_ok, Slice.len_val, admitted, decide_false, Bool.false_eq_true, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem complete_total_four (input start : Slice U8) (a0 a1 a2 a3 : U8) :
    ∃ result, extraction_preflight_four input start (RegistrationPreflightFour.kinds a0 a1 a2 a3) = .ok result := by
  by_cases admitted : input.length ≤ 33554432
  · have cap : beaconcrypt_core.transport.complete_message_size_admitted input.len = .ok true := by
      rw [BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact]
      simp only [Slice.len_val, admitted, decide_true]
    obtain ⟨r0, run0⟩ := strip_total input start
    cases r0 with
    | none => exact ⟨.None, by simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
    | some tail0 =>
      obtain ⟨r1, run1⟩ := field_total tail0 a0
      cases r1 with
      | none => exact ⟨.None, by simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
      | some tail1 =>
        obtain ⟨r2, run2⟩ := field_total tail1 a1
        cases r2 with
        | none => exact ⟨.None, by simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
        | some tail2 =>
          obtain ⟨r3, run3⟩ := field_total tail2 a2
          cases r3 with
          | none => exact ⟨.None, by simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
          | some tail3 =>
            obtain ⟨r4, run4⟩ := field_total tail3 a3
            cases r4 with
            | none => exact ⟨.None, by simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]⟩
            | some tail4 =>
              refine ⟨if tail4.len = 0#usize then .Some () else .None, ?_⟩
              simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.slice.Slice.is_empty, RegistrationCodecStandardSlices.thenSomeUnit]
              split_ifs <;> rfl
  · refine ⟨.None, ?_⟩
    simp only [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length,
      BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact,
      bind_tc_ok, Slice.len_val, admitted, decide_false, Bool.false_eq_true, ↓reduceIte]

end BeaconcryptCore.Refinement.RegistrationPreflightTotal

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.unpack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.unpack

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.major_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.major_bound

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.additional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.additional_bound

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.argument_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.argument_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.try_usize_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.try_usize_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.suffix_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.suffix_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.field_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.field_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.strip_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.strip_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.complete_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.complete_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightTotal.complete_total_four' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightTotal.complete_total_four
