-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightArgument
import BeaconcryptCore.Refinement.RegistrationSerializerFields
import BeaconcryptCore.Refinement.RegistrationFlatSkip
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Original primitive field preflight consumes complete canonical unsigned integers and byte strings, retaining the exact remaining borrowed slice. Source usize conversion is checked on both modeled pointer widths, and the original checked suffix projection returns precisely the payload suffix. Prefix stripping executes actual total U8 slice comparison. Complete public preflight is composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightFields
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderJump RegistrationPreflightArgument

set_option backward.isDefEq.respectTransparency false in
theorem try_length (payload : Slice U8) :
    core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from (UScalar.cast .U64 payload.len) =
      .ok (.Ok payload.len) := by
  have upper : ¬ UScalar.cast .U64 payload.len > UScalar.cast .U64 core.num.Usize.MAX := by
    simp only [UScalar.lt_equiv, RegistrationSerializerFields.usize_cast]
    have bound := payload.len.hBounds
    simp only [core.num.Usize.MAX, UScalar.ofNatCore_val_eq, Usize.max, Usize.numBits]
    omega
  have lower : ¬ UScalar.cast .U64 payload.len < UScalar.cast .U64 core.num.Usize.MIN := by
    simp only [UScalar.lt_equiv, RegistrationSerializerFields.usize_cast]
    simp [core.num.Usize.MIN]
  simp only [core.Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from, lift, bind_tc_ok,
    upper, lower, ↓reduceIte, RegistrationFlatSkip.cast_length]

set_option backward.isDefEq.respectTransparency false in
theorem get_suffix (input : Slice U8) (start : Usize) (bound : start.val ≤ input.length) :
    core.slice.Slice.get (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      input { start := start } = .ok (.Some (input.drop start)) := by
  have allowed : start ≤ input.len := by simpa only [UScalar.le_equiv, Slice.len_val] using bound
  simp only [core.slice.Slice.get,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, bind_tc_ok, allowed, ↓reduceIte,
    rust_primitives.slice.slice_slice, Slice.subslice, Slice.len_val, bound, le_refl, and_self]
  congr 1
  congr 1
  apply Subtype.ext
  change input.val.slice start.val input.val.length = input.val.drop start.val
  rw [List.slice, ← List.length_drop, List.take_length]

set_option backward.isDefEq.respectTransparency false in
theorem field_uint (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ tail, tail.val = rest ∧ extraction_preflight_field input 0#u8 = .ok (.Some tail) := by
  obtain ⟨tail, tailBytes, source⟩ := RegistrationPreflightArgument.encoded input cbor_major_type_uint64 value rest contents (by simp [cbor_major_type_uint64])
  simp only [cbor_major_type_uint64] at source
  refine ⟨tail, tailBytes, ?_⟩
  simp only [extraction_preflight_field, source, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, uncurry]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem field_bytes (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    ∃ tail, tail.val = rest ∧ extraction_preflight_field input 2#u8 = .ok (.Some tail) := by
  obtain ⟨afterHeader, afterHeaderBytes, argument⟩ := RegistrationPreflightArgument.encoded input cbor_major_type_byte_string
    (UScalar.cast .U64 payload.len) (payload.val ++ rest) (by simpa only [List.append_assoc] using contents) (by simp [cbor_major_type_byte_string])
  simp only [cbor_major_type_byte_string] at argument
  have bound : payload.len.val ≤ afterHeader.length := by
    simp only [Slice.len_val, Slice.length]
    rw [afterHeaderBytes, List.length_append]
    omega
  let tail := afterHeader.drop payload.len
  have tailBytes : tail.val = rest := by
    change afterHeader.val.drop payload.len.val = rest
    rw [afterHeaderBytes, Slice.len_val]
    change (payload.val ++ rest).drop payload.val.length = rest
    simp
  refine ⟨tail, tailBytes, ?_⟩
  simp only [extraction_preflight_field, argument, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, uncurry, ↓reduceIte,
    try_length, core.result.Result.ok, get_suffix afterHeader payload.len bound]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem strip (input head : Slice U8) (rest : List U8) (contents : input.val = head.val ++ rest) :
    ∃ tail, tail.val = rest ∧ extraction_strip_prefix input head = .ok (.Some tail) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input head.len head.val rest contents (Slice.len_val head)
  have enough : head.len ≤ input.len := by
    simp only [UScalar.le_equiv, Slice.len_val]
    have sizes := congrArg List.length contents
    simp only [List.length_append] at sizes
    change input.length = head.length + rest.length at sizes
    omega
  have equal : front.val = head.val := frontBytes
  refine ⟨tail, tailBytes, ?_⟩
  simp only [extraction_strip_prefix, core.slice.Slice.len, rust_primitives.slice.slice_length,
    bind_tc_ok, enough, ↓reduceIte, splitInput, uncurry,
    RegistrationBytePrimitives.slice_eq_exact, equal, decide_true]
end BeaconcryptCore.Refinement.RegistrationPreflightFields

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFields.try_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFields.try_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFields.get_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFields.get_suffix

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFields.field_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFields.field_uint

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFields.field_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFields.field_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFields.strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFields.strip
