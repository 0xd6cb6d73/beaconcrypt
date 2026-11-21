-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightArgumentBits
import BeaconcryptCore.Refinement.RegistrationHeaderJump
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual handwritten primitive reader follows the generated header bit representation, then the original bounded word conversion. Canonical prefixes read every U64 width with the exact remaining borrowed slice. Empty input, wrong major type, reserved information and truncated long arguments reject through their original paths. Every bounded long-argument width and additional-info continuation terminates on all typed inputs. Complete six-field preflight is composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightArgument
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderBits RegistrationHeaderJump
open RegistrationPreflightArgumentBits RegistrationPreflightWordValues

abbrev Argument := core.option.Option (U64 × Slice U8)

def afterHeader (additional : U8) (tail : Slice U8) : RustM Argument :=
  if additional ≤ 23#u8 then .ok (.Some (UScalar.cast .U64 additional, tail))
  else match additional with
  | 24#uscalar => extraction_argument_long tail 1#usize
  | 25#uscalar => extraction_argument_long tail 2#usize
  | 26#uscalar => extraction_argument_long tail 4#usize
  | 27#uscalar => extraction_argument_long tail 8#usize
  | _ => .ok .None

set_option backward.isDefEq.respectTransparency false in
theorem prefix_step (input : Slice U8) (major additional : U8) (rest : List U8)
    (contents : input.val = packed major additional :: rest)
    (majorBound : major.val < 8) (additionalBound : additional.val < 32) :
    ∃ tail, tail.val = rest ∧ primitive_argument input major = afterHeader additional tail := by
  obtain ⟨front, tail, splitInput, _, tailBytes⟩ := RegistrationHeaderReadback.split_first input _ rest contents
  have positive : 0 < input.length := by rw [Slice.length, contents]; simp
  have nonzero : input.len ≠ 0#usize := by scalar_tac
  have nonnegative : 0#u8 ≤ additional := by scalar_tac
  refine ⟨tail, tailBytes, ?_⟩
  simp only [primitive_argument, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, bind_tc_ok, nonzero, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [RegistrationHeaderReadback.first_index input _ rest contents, splitInput]
  simp only [bind_tc_ok, uncurry, packed_shift major additional majorBound,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    packed_mask major additional additionalBound, lift, nonnegative,
    core.U64.Insts.CoreConvertFromU8.from]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem long_prefix (input : Slice U8) (width : Usize) (value : U64) (encoded rest : List U8)
    (contents : input.val = encoded ++ rest) (length : encoded.length = width.val)
    (word : ∀ front : Slice U8, front.val = encoded → extraction_argument_word front width = .ok value) :
    ∃ tail, tail.val = rest ∧ extraction_argument_long input width = .ok (.Some (value, tail)) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input width encoded rest contents length.symm
  have enough : ¬ width > input.len := by
    simp only [UScalar.lt_equiv, Slice.len_val]
    have sizes := congrArg List.length contents
    simp only [List.length_append] at sizes
    change input.length = _ at sizes
    omega
  refine ⟨tail, tailBytes, ?_⟩
  simp only [extraction_argument_long, core.slice.Slice.len, rust_primitives.slice.slice_length,
    bind_tc_ok, enough, ↓reduceIte, splitInput, uncurry, word front frontBytes]

set_option backward.isDefEq.respectTransparency false in
theorem long_rejected (input : Slice U8) (width : Usize) (outside : input.length < width.val) :
    extraction_argument_long input width = .ok .None := by
  have tooWide : width > input.len := by simpa only [UScalar.lt_equiv, Slice.len_val] using outside
  simp only [extraction_argument_long, core.slice.Slice.len, rust_primitives.slice.slice_length,
    bind_tc_ok, tooWide, ↓reduceIte]
theorem after_byte (tail : Slice U8) : afterHeader 24#u8 tail = extraction_argument_long tail 1#usize := by
  simp [afterHeader]
  rfl

theorem after_word16 (tail : Slice U8) : afterHeader 25#u8 tail = extraction_argument_long tail 2#usize := by
  simp [afterHeader]
  rfl

theorem after_word32 (tail : Slice U8) : afterHeader 26#u8 tail = extraction_argument_long tail 4#usize := by
  simp [afterHeader]
  rfl

theorem after_word64 (tail : Slice U8) : afterHeader 27#u8 tail = extraction_argument_long tail 8#usize := by
  simp [afterHeader]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem encoded (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest) (majorBound : major.val < 8) :
    ∃ tail, tail.val = rest ∧ primitive_argument input major = .ok (.Some (value, tail)) := by
  unfold encodedBytes at contents
  split_ifs at contents with small byte word16 word32
  · have additionalBound : (UScalar.cast .U8 value).val < 24 := by
      rw [cast_value .U8 value (by scalar_tac)]
      exact small
    obtain ⟨tail, tailBytes, source⟩ := prefix_step input major (UScalar.cast .U8 value) rest
      (by simpa using contents) majorBound (by omega)
    refine ⟨tail, tailBytes, ?_⟩
    rw [source]
    have short : UScalar.cast .U8 value ≤ 23#u8 := by scalar_tac
    simp only [afterHeader, short, ↓reduceIte, cast_roundtrip .U8 value (by scalar_tac)]
  · obtain ⟨start, startBytes, source⟩ := prefix_step input major 24#u8
      ([ (UScalar.cast .U8 value) ] ++ rest) (by simpa [FrameCodecWord.word] using contents) majorBound (by decide)
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 1#usize (UScalar.cast .U64 (UScalar.cast .U8 value))
      [ (UScalar.cast .U8 value) ] rest startBytes (by rfl)
      (fun front bytes => argument_byte front (UScalar.cast .U8 value) bytes)
    refine ⟨tail, tailBytes, ?_⟩
    rw [source, after_byte, decoded, cast_roundtrip .U8 value (by scalar_tac)]
  · obtain ⟨start, startBytes, source⟩ := prefix_step input major 25#u8
      ([ RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 8, RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 0 ] ++ rest) (by simpa [FrameCodecWord.word] using contents) majorBound (by decide)
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 2#usize (UScalar.cast .U64 (UScalar.cast .U16 value))
      [ RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 8, RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 0 ] rest startBytes (by rfl)
      (fun front bytes => argument_word16 front (UScalar.cast .U16 value) bytes)
    refine ⟨tail, tailBytes, ?_⟩
    rw [source, after_word16, decoded, cast_roundtrip .U16 value (by scalar_tac)]
  · obtain ⟨start, startBytes, source⟩ := prefix_step input major 26#u8
      ([ RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 24, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 16, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 8, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 0 ] ++ rest) (by simpa [FrameCodecWord.word] using contents) majorBound (by decide)
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 4#usize (UScalar.cast .U64 (UScalar.cast .U32 value))
      [ RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 24, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 16, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 8, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 0 ] rest startBytes (by rfl)
      (fun front bytes => argument_word32 front (UScalar.cast .U32 value) bytes)
    refine ⟨tail, tailBytes, ?_⟩
    rw [source, after_word32, decoded, cast_roundtrip .U32 value (by scalar_tac)]
  · obtain ⟨start, startBytes, source⟩ := prefix_step input major 27#u8
      ((FrameCodecWord.word value).val ++ rest) (by simpa [FrameCodecWord.word] using contents) majorBound (by decide)
    obtain ⟨tail, tailBytes, decoded⟩ := long_prefix start 8#usize value
      (FrameCodecWord.word value).val rest startBytes (by rfl)
      (fun front bytes => argument_word64 front value bytes)
    refine ⟨tail, tailBytes, ?_⟩
    rw [source, after_word64, decoded]

set_option backward.isDefEq.respectTransparency false in
theorem empty (input : Slice U8) (major : U8) (contents : input.val = []) :
    primitive_argument input major = .ok .None := by
  have zero : input.len = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, Slice.length, contents]
    rfl
  simp only [primitive_argument, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, bind_tc_ok, zero, decide_true, ↓reduceIte]

theorem after_reserved (additional : U8) (tail : Slice U8)
    (lower : 28 ≤ additional.val) (upper : additional.val < 32) : afterHeader additional tail = .ok .None := by
  have cases : additional = 28#u8 ∨ additional = 29#u8 ∨ additional = 30#u8 ∨ additional = 31#u8 := by scalar_tac
  rcases cases with same | same | same | same <;> subst additional <;> simp [afterHeader] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem reserved (input : Slice U8) (major additional : U8) (rest : List U8)
    (contents : input.val = packed major additional :: rest)
    (majorBound : major.val < 8) (lower : 28 ≤ additional.val) (upper : additional.val < 32) :
    primitive_argument input major = .ok .None := by
  obtain ⟨tail, _, source⟩ := prefix_step input major additional rest contents majorBound upper
  rw [source, after_reserved additional tail lower upper]

set_option backward.isDefEq.respectTransparency false in
theorem mismatch (input : Slice U8) (actual declared additional : U8) (rest : List U8)
    (contents : input.val = packed actual additional :: rest)
    (majorBound : actual.val < 8) (different : actual ≠ declared) :
    primitive_argument input declared = .ok .None := by
  obtain ⟨front, tail, splitInput, _, _⟩ := RegistrationHeaderReadback.split_first input _ rest contents
  have positive : 0 < input.length := by rw [Slice.length, contents]; simp
  have nonzero : input.len ≠ 0#usize := by scalar_tac
  have unequal : (actual != declared) = true := bne_iff_ne.mpr different
  simp only [primitive_argument, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, bind_tc_ok, nonzero, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [RegistrationHeaderReadback.first_index input _ rest contents, splitInput]
  simp only [bind_tc_ok, uncurry, packed_shift actual additional majorBound, unequal, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem long_total (input : Slice U8) (width : Usize) (bounded : width.val ≤ 8) :
    ∃ result, extraction_argument_long input width = .ok result := by
  by_cases short : input.length < width.val
  · exact ⟨.None, long_rejected input width short⟩
  · have bound : width.val ≤ input.length := by omega
    obtain ⟨front, tail, splitInput, frontBytes, _⟩ := split_prefix input width
      (input.val.take width.val) (input.val.drop width.val)
      (List.take_append_drop width.val input.val).symm
      (by rw [List.length_take, Nat.min_eq_left bound])
    have length : front.length = width.val := by
      rw [Slice.length, frontBytes, List.length_take, Nat.min_eq_left bound]
    let value := Aeneas.Std.core.num.U64.from_be_bytes (RegistrationPreflightWord.padded front width length bounded)
    have word : extraction_argument_word front width = .ok value := by
      rw [RegistrationPreflightWord.argument_word front width length bounded]
      rfl
    have enough : ¬ width > input.len := by simpa only [UScalar.lt_equiv, Slice.len_val] using Nat.not_lt.mpr bound
    refine ⟨.Some (value, tail), ?_⟩
    simp only [extraction_argument_long, core.slice.Slice.len, rust_primitives.slice.slice_length,
      bind_tc_ok, enough, ↓reduceIte, splitInput, uncurry, word]

set_option backward.isDefEq.respectTransparency false in
theorem after_total (additional : U8) (tail : Slice U8) (upper : additional.val < 32) :
    ∃ result, afterHeader additional tail = .ok result := by
  by_cases short : additional ≤ 23#u8
  · exact ⟨.Some (UScalar.cast .U64 additional, tail), by simp only [afterHeader, short, ↓reduceIte]⟩
  · have alternatives : additional = 24#u8 ∨ additional = 25#u8 ∨ additional = 26#u8 ∨ additional = 27#u8 ∨ 28 ≤ additional.val := by scalar_tac
    rcases alternatives with same | same | same | same | lower
    · subst additional
      rw [after_byte]
      exact long_total tail 1#usize (by decide)
    · subst additional
      rw [after_word16]
      exact long_total tail 2#usize (by decide)
    · subst additional
      rw [after_word32]
      exact long_total tail 4#usize (by decide)
    · subst additional
      rw [after_word64]
      exact long_total tail 8#usize (by decide)
    · exact ⟨.None, after_reserved additional tail lower upper⟩

end BeaconcryptCore.Refinement.RegistrationPreflightArgument

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.prefix_step

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_prefix

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word16

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word32

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_word64

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.encoded

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.empty

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_reserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.reserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.mismatch

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.long_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightArgument.after_total
