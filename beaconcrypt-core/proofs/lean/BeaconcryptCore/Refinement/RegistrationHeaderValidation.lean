-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSerializerStages
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual source header validator accepts available non-simple headers at arbitrary original-slice offsets and returns the exact updated counter. Every canonical U64 width is covered. Exhausted input and reserved additional-info rejection retain their actual counter poststates. These are local source validation facts; full codec readback is composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderValidation
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits RegistrationHeaderJump RegistrationHeaderSize
open RegistrationSerializerStages

theorem add_value (left right : Usize) (bound : left.val + right.val < UScalar.size .Usize) :
    (Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt bound]

theorem sub_source (left right : Usize) :
    core.num.Usize.wrapping_sub left right = .ok (Usize.wrapping_sub left right) := rfl

theorem sub_exact (left right result : Usize) (value : left.val = right.val + result.val) :
    core.num.Usize.wrapping_sub left right = .ok result := by
  rw [sub_source]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [sub_value left right (by omega)]
  omega

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem header_prefix (input : Slice U8) (offset finish : Usize) (major additional : U8)
    (headBytes rest : List U8)
    (contents : input.val = headBytes ++ packed major additional :: rest)
    (position : offset.val = headBytes.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (additionalBound : additional.val < 28)
    (available : offset.val + (count additional).val ≤ input.length)
    (finishValue : finish.val = offset.val + (count additional).val) :
    validate_header input (cell offset) = .ok (true, cell finish) := by
  obtain ⟨ignored, tail, splitInput, _, tailBytes⟩ := split_prefix input offset headBytes
    (packed major additional :: rest) contents position
  obtain ⟨first, restSlice, splitFirst, firstBytes, _⟩ :=
    RegistrationHeaderReadback.split_first tail _ rest tailBytes
  have readFirst := RegistrationHeaderReadback.read_initial first major additional [] firstBytes majorBound (by omega)
  have positive : 1 ≤ (count additional).val := by
    unfold count
    split_ifs <;> scalar_tac
  have beforeLimit : offset.val + 1 < UScalar.size .Usize := by
    have := input.len.hBounds
    rw [Slice.len_val] at this
    rw [← UScalar.size_def] at this
    omega
  let next := Usize.wrapping_add offset 1#usize
  have nextValue : next.val = offset.val + 1 := add_value offset 1#usize (by simpa using beforeLimit)
  have advance : core.num.Usize.wrapping_add offset 1#usize = .ok next := rfl
  have consumed : core.num.Usize.wrapping_sub next offset = .ok 1#usize :=
    sub_exact next offset 1#usize (by simpa using nextValue)
  have consumedScalar : Usize.wrapping_sub next offset = 1#usize := by
    simpa only [sub_source, ok.injEq] using consumed
  have remainingValue : (Usize.wrapping_sub input.len offset).val = input.length - offset.val := by
    rw [sub_value input.len offset (by rw [Slice.len_val]; omega), Slice.len_val]
  have hasFirst : ¬ Usize.wrapping_sub input.len offset < 1#usize := by
    simp only [UScalar.lt_equiv, remainingValue]
    change ¬ input.length - offset.val < 1
    omega
  have remainingNext : (Usize.wrapping_sub input.len next).val = input.length - (offset.val + 1) := by
    rw [sub_value input.len next (by rw [Slice.len_val]; omega), Slice.len_val, nextValue]
  have notSimpleBool : (major != cbor_major_type_simple_value) = true := bne_iff_ne.mpr notSimple
  have allowed : additional < additional_info_unassigned_min := by
    simp only [additional_info_unassigned_min, UScalar.lt_equiv]
    exact additionalBound
  simp only [validate_header, index_cell, core.slice.Slice.len, rust_primitives.slice.slice_length,
    sub_source, bind_tc_ok, hasFirst, ↓reduceIte, advance, update_cell]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry, consumedScalar]
  rw [splitFirst]
  simp only [bind_tc_ok, uncurry, readFirst, notSimpleBool, allowed, decide_true, ↓reduceIte]
  simp only [notSimple, ↓reduceIte,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits]
  by_cases short8 : additional = 24#u8
  · have enough : ¬ Usize.wrapping_sub input.len next < 1#usize := by
      simp only [UScalar.lt_equiv, remainingNext]
      simp only [count, short8, ↓reduceIte] at available
      change ¬ input.length - (offset.val + 1) < 1
      change offset.val + 2 ≤ input.length at available
      omega
    simp only [short8, ↓reduceIte]
    simp only [↓reduceIte, enough]
    rw [add_usize next 1#usize finish (by rw [nextValue, finishValue]; simp [count, short8])]
    simp only [bind_tc_ok]
  · simp only [short8, ↓reduceIte]
    by_cases short16 : additional = 25#u8
    · have enough : ¬ Usize.wrapping_sub input.len next < 2#usize := by
        simp only [UScalar.lt_equiv, remainingNext]
        simp [count, short16] at available
        change ¬ input.length - (offset.val + 1) < 2
        change offset.val + 3 ≤ input.length at available
        omega
      simp only [short16, ↓reduceIte, enough]
      rw [add_usize next 2#usize finish (by rw [nextValue, finishValue]; simp [count, short16])]
      simp only [bind_tc_ok]
    · simp only [short16, ↓reduceIte]
      by_cases short32 : additional = 26#u8
      · have enough : ¬ Usize.wrapping_sub input.len next < 4#usize := by
          simp only [UScalar.lt_equiv, remainingNext]
          simp [count, short32] at available
          change ¬ input.length - (offset.val + 1) < 4
          change offset.val + 5 ≤ input.length at available
          omega
        simp only [short32, ↓reduceIte, enough]
        rw [add_usize next 4#usize finish (by rw [nextValue, finishValue]; simp [count, short32])]
        simp only [bind_tc_ok]
      · simp only [short32, ↓reduceIte]
        by_cases short64 : additional = 27#u8
        · have enough : ¬ Usize.wrapping_sub input.len next < 8#usize := by
            simp only [UScalar.lt_equiv, remainingNext]
            simp [count, short64] at available
            change ¬ input.length - (offset.val + 1) < 8
            change offset.val + 9 ≤ input.length at available
            omega
          simp only [short64, ↓reduceIte, enough]
          rw [add_usize next 8#usize finish (by rw [nextValue, finishValue]; simp [count, short64])]
          simp only [bind_tc_ok]
        · simp only [short64, ↓reduceIte]
          have equal : next = finish := by
            apply UScalar.eq_of_val_eq
            rw [nextValue, finishValue]
            simp [count, short8, short16, short32, short64]
          rw [equal]

theorem count_short (additional : U8) (bound : additional.val < 24) : count additional = 1#usize := by
  have n24 : additional ≠ 24#u8 := by scalar_tac
  have n25 : additional ≠ 25#u8 := by scalar_tac
  have n26 : additional ≠ 26#u8 := by scalar_tac
  have n27 : additional ≠ 27#u8 := by scalar_tac
  simp only [count, n24, n25, n26, n27, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem encoded (input : Slice U8) (offset finish : Usize) (major : U8) (value : U64)
    (headBytes rest : List U8)
    (contents : input.val = headBytes ++ RegistrationHeaderCanonical.encodedBytes major value ++ rest)
    (position : offset.val = headBytes.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (finishValue : finish.val = offset.val + (RegistrationHeaderCanonical.writtenCount value).val) :
    validate_header input (cell offset) = .ok (true, cell finish) := by
  have room : offset.val + (RegistrationHeaderCanonical.writtenCount value).val ≤ input.length := by
    have lengths := congrArg List.length contents
    simp only [List.length_append, RegistrationHeaderCanonical.encoded_length] at lengths
    change input.length = _ at lengths
    omega
  unfold RegistrationHeaderCanonical.encodedBytes at contents
  unfold RegistrationHeaderCanonical.writtenCount at room finishValue
  split_ifs at contents room finishValue with small byte word16 word32
  · simp only [List.append_assoc, List.cons_append, List.nil_append] at contents
    have bound : (UScalar.cast .U8 value).val < 24 := by
      rw [RegistrationHeaderCanonical.cast_value .U8 value (by scalar_tac)]
      exact small
    apply header_prefix input offset finish major (UScalar.cast .U8 value) headBytes rest contents position majorBound notSimple (by omega)
    · simpa only [count_short _ bound] using room
    · simpa only [count_short _ bound] using finishValue
  · simp only [List.append_assoc, List.cons_append, List.nil_append] at contents
    exact header_prefix input offset finish major 24#u8 headBytes _ contents position majorBound notSimple (by scalar_tac) (by simpa [count] using room) (by simpa [count] using finishValue)
  · simp only [List.append_assoc, List.cons_append, List.nil_append] at contents
    exact header_prefix input offset finish major 25#u8 headBytes _ contents position majorBound notSimple (by scalar_tac) (by simpa [count] using room) (by simpa [count] using finishValue)
  · simp only [List.append_assoc, List.cons_append, List.nil_append] at contents
    exact header_prefix input offset finish major 26#u8 headBytes _ contents position majorBound notSimple (by scalar_tac) (by simpa [count] using room) (by simpa [count] using finishValue)
  · simp only [List.append_assoc, List.cons_append, List.nil_append] at contents
    exact header_prefix input offset finish major 27#u8 headBytes _ contents position majorBound notSimple (by scalar_tac) (by simpa [count] using room) (by simpa [count] using finishValue)


theorem exhausted (input : Slice U8) :
    validate_header input (cell input.len) = .ok (false, cell input.len) := by
  have same : core.num.Usize.wrapping_sub input.len input.len = .ok 0#usize :=
    sub_exact input.len input.len 0#usize (by simp)
  simp only [validate_header, index_cell, core.slice.Slice.len,
    rust_primitives.slice.slice_length, bind_tc_ok, same]
  rw [ite_eq_left (by scalar_tac)]

set_option backward.isDefEq.respectTransparency false in
theorem reserved (input : Slice U8) (offset next : Usize) (major additional : U8)
    (headBytes rest : List U8)
    (contents : input.val = headBytes ++ packed major additional :: rest)
    (position : offset.val = headBytes.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (additionalBound : additional.val < 32) (unassigned : 28 ≤ additional.val)
    (nextValue : next.val = offset.val + 1) :
    validate_header input (cell offset) = .ok (false, cell next) := by
  obtain ⟨ignored, tail, splitInput, _, tailBytes⟩ := split_prefix input offset headBytes
    (packed major additional :: rest) contents position
  obtain ⟨first, restSlice, splitFirst, firstBytes, _⟩ :=
    RegistrationHeaderReadback.split_first tail _ rest tailBytes
  have readFirst := RegistrationHeaderReadback.read_initial first major additional [] firstBytes majorBound additionalBound
  have inputLength : offset.val + 1 ≤ input.length := by
    have sizes := congrArg List.length contents
    simp only [List.length_append, List.length_cons] at sizes
    change input.length = _ at sizes
    omega
  have consumed : Usize.wrapping_sub next offset = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [sub_value next offset (by omega)]
    change next.val - offset.val = 1
    omega
  have remainingValue : (Usize.wrapping_sub input.len offset).val = input.length - offset.val := by
    rw [sub_value input.len offset (by rw [Slice.len_val]; omega), Slice.len_val]
  have hasFirst : ¬ Usize.wrapping_sub input.len offset < 1#usize := by
    simp only [UScalar.lt_equiv, remainingValue]
    change ¬ input.length - offset.val < 1
    omega
  have notSimpleBool : (major != cbor_major_type_simple_value) = true := bne_iff_ne.mpr notSimple
  have disallowed : ¬ additional < additional_info_unassigned_min := by
    simp only [additional_info_unassigned_min, UScalar.lt_equiv]
    exact Nat.not_lt.mpr unassigned
  simp only [validate_header, index_cell, core.slice.Slice.len, rust_primitives.slice.slice_length,
    sub_source, bind_tc_ok, hasFirst, ↓reduceIte, add_usize offset 1#usize next (by simpa using nextValue.symm), update_cell]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry, consumed]
  rw [splitFirst]
  simp only [bind_tc_ok, uncurry, readFirst, notSimpleBool, disallowed, decide_false, Bool.false_eq_true, ↓reduceIte]

end BeaconcryptCore.Refinement.RegistrationHeaderValidation

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.add_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.add_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.sub_source' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.sub_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.sub_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.sub_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.header_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.header_prefix

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.count_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.count_short

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.encoded

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.exhausted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.exhausted

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderValidation.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderValidation.reserved
