-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCanonicalTrace
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Actual structural-validation loop steps retain original input offsets, bounded header and payload slices, quotient admission, child-count validation and mutable-array copyback. Source-byte constructors establish UInt64, bounded array-header and byte-string steps. Byte-string steps never execute the text operation, and all returned offset/counter poststates are exact. Complete finite validation traces are composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationRawItems
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump RegistrationFlatHeader
open RegistrationCodecArraySingleton RegistrationFlatSkip RegistrationHeaderSize RegistrationCanonicalItems

structure HeaderAt (input : Slice U8) (offset : Usize) (major : U8) (value : U64) where
  finish : Usize
  before : Slice U8
  tail : Slice U8
  headerFront : Slice U8
  headerTail : Slice U8
  finishValue : finish.val = offset.val + (writtenCount value).val
  validate : validate_header input (cell offset) = .ok (true, cell finish)
  splitOffset : core.slice.Slice.split_at input offset = .ok (before, tail)
  splitHeader : core.slice.Slice.split_at tail (writtenCount value) = .ok (headerFront, headerTail)
  consumed : core.num.Usize.wrapping_sub finish offset = .ok (writtenCount value)
  readHeader : read_header headerFront = .ok (normalHeader major value)
  headerBytes : headerFront.val = encodedBytes major value

set_option backward.isDefEq.respectTransparency false in
theorem header_at (input : Slice U8) (offset : Usize) (major : U8) (value : U64)
    (headBytes rest : List U8)
    (contents : input.val = headBytes ++ encodedBytes major value ++ rest)
    (position : offset.val = headBytes.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    ∃ h : HeaderAt input offset major value, h.tail.val = encodedBytes major value ++ rest := by
  have room : offset.val + (writtenCount value).val ≤ input.length := by
    have sizes := congrArg List.length contents
    simp only [List.length_append, encoded_length] at sizes
    change input.length = _ at sizes
    omega
  let finish := Usize.wrapping_add offset (writtenCount value)
  have finishValue : finish.val = offset.val + (writtenCount value).val := by
    apply RegistrationHeaderValidation.add_value
    have bound := input.len.hBounds
    rw [Slice.len_val, ← UScalar.size_def] at bound
    omega
  obtain ⟨before, tail, splitOffset, _, tailBytes⟩ := split_prefix input offset headBytes
    (encodedBytes major value ++ rest) (by simpa only [List.append_assoc] using contents) position
  obtain ⟨front, suffix, splitHeader, headerBytes, _, readHeader⟩ := header_parts tail major value rest tailBytes majorBound notSimple
  exact ⟨{
    finish := finish, before := before, tail := tail, headerFront := front, headerTail := suffix,
    finishValue := finishValue,
    validate := RegistrationHeaderValidation.encoded input offset finish major value headBytes rest contents position majorBound notSimple finishValue,
    splitOffset := splitOffset, splitHeader := splitHeader,
    consumed := RegistrationHeaderValidation.sub_exact finish offset (writtenCount value) finishValue,
    readHeader := readHeader, headerBytes := headerBytes }, tailBytes⟩

set_option backward.isDefEq.respectTransparency false in
theorem argument_fits (major : U8) (value : U64) (remaining : Usize)
    (fits : value.val ≤ remaining.val) :
    validate_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleBool.call
      (RegistrationStringFactory.quotient (RegistrationStringFactory.quotient
        (RegistrationStringFactory.quotient (RegistrationStringFactory.quotient remaining))),
        remaining, (normalHeader major value).fst, (normalHeader major value).snd) () = .ok true := by
  have small : ¬ RegistrationStringFactory.quotient (RegistrationStringFactory.quotient
      (RegistrationStringFactory.quotient (RegistrationStringFactory.quotient remaining))) ≥ 16#usize := by
    have bound := RegistrationStringFactory.fourth_bound remaining
    scalar_tac
  have fitsCast : value ≤ UScalar.cast .U64 remaining := by
    simp only [UScalar.le_equiv, RegistrationSerializerFields.usize_cast]
    exact fits
  simp only [validate_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleBool.call,
    uncurry, small, ↓reduceIte, lift, bind_tc_ok, argument_normal, fitsCast, decide_true]

variable [RegistrationValidatorPrimitive.Operations]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uint_body (input : Slice U8) (offset count : Usize) (value : U64) (headBytes rest : List U8)
    (contents : input.val = headBytes ++ encodedBytes cbor_major_type_uint64 value ++ rest)
    (position : offset.val = headBytes.length)
    (countFit : count.val ≤ input.length - offset.val) :
    ∃ finish, validate_raw_data_item_loop.body input (cell offset) (pack count) (pack true) true =
      .ok (ControlFlow.cont (cell finish, pack (nextCount count 0#usize), pack true,
        decide (nextCount count 0#usize > 0#usize))) ∧
      finish.val = offset.val + (writtenCount value).val := by
  have majorBound : cbor_major_type_uint64.val < 8 := by simp [cbor_major_type_uint64]
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  have notString : cbor_major_type_uint64 ≠ cbor_major_type_byte_string := by simp [cbor_major_type_uint64, cbor_major_type_byte_string]
  have notText : cbor_major_type_uint64 ≠ cbor_major_type_text_string := by simp [cbor_major_type_uint64, cbor_major_type_text_string]
  have notArray : cbor_major_type_uint64 ≠ cbor_major_type_array := by simp [cbor_major_type_uint64, cbor_major_type_array]
  have notMap : cbor_major_type_uint64 ≠ cbor_major_type_map := by simp [cbor_major_type_uint64, cbor_major_type_map]
  have notTagged : cbor_major_type_uint64 ≠ cbor_major_type_tagged := by simp [cbor_major_type_uint64, cbor_major_type_tagged]
  obtain ⟨h, _⟩ := header_at input offset _ value headBytes rest contents position majorBound notSimple
  have beforeBound : offset.val ≤ input.length := by
    have bound := h.finish.hBounds
    have sizes := congrArg List.length contents
    simp only [List.length_append] at sizes
    change input.length = _ at sizes
    omega
  have remainingValue : (Usize.wrapping_sub input.len offset).val = input.length - offset.val := by
    rw [sub_value _ _ (by simpa only [Slice.len_val] using beforeBound), Slice.len_val]
  have allowed : ¬ count > Usize.wrapping_sub input.len offset := by
    simp only [UScalar.lt_equiv, remainingValue]
    omega
  have leafCount := validate_leaf h.headerFront _ value [] (by simpa using h.headerBytes)
    majorBound notSimple notArray notMap notTagged
    (Usize.wrapping_sub (Usize.wrapping_sub input.len offset) count) count
  have consumedScalar : Usize.wrapping_sub h.finish offset = writtenCount value := by
    simpa only [RegistrationHeaderValidation.sub_source, ok.injEq] using h.consumed
  have zeroBound : ¬ (0#usize : Usize) > Usize.wrapping_sub (Usize.wrapping_sub input.len offset) count := by scalar_tac
  refine ⟨h.finish, ?_, h.finishValue⟩
  simp only [validate_raw_data_item_loop.body, ↓reduceIte, index_cell, index_pack,
    core.slice.Slice.len, rust_primitives.slice.slice_length,
    RegistrationHeaderValidation.sub_source, bind_tc_ok, allowed, h.validate,
    h.splitOffset, uncurry]
  rw [consumedScalar]
  simp only [bind_tc_ok, h.splitHeader, uncurry, h.readHeader, normal_major,
    notString, notText, ↓reduceIte]
  simp only [index_cell, bind_tc_ok, consumedScalar, h.splitHeader, uncurry]
  simp only [Array.to_slice_mut, lift, bind_tc_ok, uncurry]
  have toSlice : Array.to_slice (pack count) = cell count := rfl
  have copyBack : Array.from_slice (pack count) (cell 0#usize) = pack 0#usize := rfl
  rw [toSlice, leafCount]
  simp only [bind_tc_ok, uncurry, copyBack, index_pack, Bool.false_eq_true, ↓reduceIte, zeroBound, add_source, update_pack, nextCount]
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem array_body (input : Slice U8) (offset count : Usize) (value : U64) (headBytes rest : List U8)
    (contents : input.val = headBytes ++ encodedBytes cbor_major_type_array value ++ rest)
    (position : offset.val = headBytes.length)
    (countFit : count.val ≤ input.length - offset.val)
    (childrenFit : value.val ≤ input.length - offset.val - count.val) :
    ∃ finish, validate_raw_data_item_loop.body input (cell offset) (pack count) (pack true) true =
      .ok (ControlFlow.cont (cell finish, pack (nextCount count (UScalar.cast .Usize value)), pack true,
        decide (nextCount count (UScalar.cast .Usize value) > 0#usize))) ∧
      finish.val = offset.val + (writtenCount value).val := by
  have majorBound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  have notString : cbor_major_type_array ≠ cbor_major_type_byte_string := by simp [cbor_major_type_array, cbor_major_type_byte_string]
  have notText : cbor_major_type_array ≠ cbor_major_type_text_string := by simp [cbor_major_type_array, cbor_major_type_text_string]
  obtain ⟨h, _⟩ := header_at input offset _ value headBytes rest contents position majorBound notSimple
  have beforeBound : offset.val ≤ input.length := by
    have bound := h.finish.hBounds
    have sizes := congrArg List.length contents
    simp only [List.length_append] at sizes
    change input.length = _ at sizes
    omega
  have remainingValue : (Usize.wrapping_sub input.len offset).val = input.length - offset.val := by
    rw [sub_value _ _ (by simpa only [Slice.len_val] using beforeBound), Slice.len_val]
  have allowed : ¬ count > Usize.wrapping_sub input.len offset := by
    simp only [UScalar.lt_equiv, remainingValue]
    omega
  let bound := Usize.wrapping_sub (Usize.wrapping_sub input.len offset) count
  have boundValue : bound.val = input.length - offset.val - count.val := by
    rw [sub_value _ _ (by rw [remainingValue]; exact countFit), remainingValue]
  have leafCount := validate_array h.headerFront value [] (by simpa using h.headerBytes)
    bound count (by rw [boundValue]; exact childrenFit)
  have childValue : (UScalar.cast .Usize value).val = value.val := by
    apply RegistrationHeaderCanonical.cast_value
    have limit := bound.hBounds
    rw [boundValue] at limit
    omega
  have consumedScalar : Usize.wrapping_sub h.finish offset = writtenCount value := by
    simpa only [RegistrationHeaderValidation.sub_source, ok.injEq] using h.consumed
  have zeroBound : ¬ (UScalar.cast .Usize value) > bound := by
    simp only [UScalar.lt_equiv, childValue, boundValue]
    omega
  dsimp only [bound] at leafCount zeroBound
  refine ⟨h.finish, ?_, h.finishValue⟩
  simp only [validate_raw_data_item_loop.body, ↓reduceIte, index_cell, index_pack,
    core.slice.Slice.len, rust_primitives.slice.slice_length,
    RegistrationHeaderValidation.sub_source, bind_tc_ok, allowed, h.validate,
    h.splitOffset, uncurry]
  rw [consumedScalar]
  simp only [bind_tc_ok, h.splitHeader, uncurry, h.readHeader, normal_major,
    notString, notText, ↓reduceIte]
  simp only [index_cell, bind_tc_ok, consumedScalar, h.splitHeader, uncurry]
  simp only [Array.to_slice_mut, lift, bind_tc_ok, uncurry]
  have toSlice : Array.to_slice (pack count) = cell count := rfl
  have copyBack : Array.from_slice (pack count) (cell (UScalar.cast .Usize value)) = pack (UScalar.cast .Usize value) := rfl
  rw [toSlice, leafCount]
  simp only [bind_tc_ok, uncurry, copyBack, index_pack, Bool.false_eq_true, ↓reduceIte, zeroBound, add_source, update_pack, nextCount]
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem bytes_body (input payload : Slice U8) (offset count : Usize) (headBytes rest : List U8)
    (contents : input.val = headBytes ++ (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest)
    (position : offset.val = headBytes.length)
    (countFit : count.val ≤ input.length - offset.val) :
    ∃ finish, validate_raw_data_item_loop.body input (cell offset) (pack count) (pack true) true =
      .ok (ControlFlow.cont (cell finish, pack (nextCount count 0#usize), pack true,
        decide (nextCount count 0#usize > 0#usize))) ∧
      finish.val = offset.val + (RegistrationSerializerFields.byteCount payload).val := by
  have majorBound : cbor_major_type_byte_string.val < 8 := by simp [cbor_major_type_byte_string]
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  have notArray : cbor_major_type_byte_string ≠ cbor_major_type_array := by simp [cbor_major_type_byte_string, cbor_major_type_array]
  have notMap : cbor_major_type_byte_string ≠ cbor_major_type_map := by simp [cbor_major_type_byte_string, cbor_major_type_map]
  have notTagged : cbor_major_type_byte_string ≠ cbor_major_type_tagged := by simp [cbor_major_type_byte_string, cbor_major_type_tagged]
  have sourceContents : input.val = headBytes ++ encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ (payload.val ++ rest) := by
    simpa only [List.append_assoc] using contents
  obtain ⟨h, tailBytes⟩ := header_at input offset _ _ headBytes (payload.val ++ rest) sourceContents position majorBound notSimple
  have sizes := congrArg List.length contents
  simp only [List.length_append, encoded_length] at sizes
  change input.length = headBytes.length + ((writtenCount (UScalar.cast .U64 payload.len)).val + payload.length) + rest.length at sizes
  have beforeBound : offset.val ≤ input.length := by omega
  have headerBound : h.finish.val + payload.length ≤ input.length := by rw [h.finishValue]; omega
  have remainingValue : (Usize.wrapping_sub input.len offset).val = input.length - offset.val := by
    rw [sub_value _ _ (by simpa only [Slice.len_val] using beforeBound), Slice.len_val]
  have remainingPayload : (Usize.wrapping_sub input.len h.finish).val = input.length - h.finish.val := by
    rw [sub_value _ _ (by rw [Slice.len_val]; omega), Slice.len_val]
  have allowed : ¬ count > Usize.wrapping_sub input.len offset := by
    simp only [UScalar.lt_equiv, remainingValue]
    omega
  have fitsArgument := argument_fits cbor_major_type_byte_string (UScalar.cast .U64 payload.len)
    (Usize.wrapping_sub input.len h.finish) (by rw [RegistrationStringFactory.length_cast, remainingPayload]; omega)
  let finish := Usize.wrapping_add h.finish payload.len
  have finishValue : finish.val = h.finish.val + payload.length := by
    rw [RegistrationHeaderValidation.add_value _ _ (by
      have limit := input.len.hBounds
      rw [Slice.len_val, ← UScalar.size_def] at limit
      rw [Slice.len_val]
      omega), Slice.len_val]
  have byteValue := RegistrationSerializerFields.byte_count_value input payload (by rw [h.finishValue] at headerBound; omega)
  have consumedHeader : Usize.wrapping_sub h.finish offset = writtenCount (UScalar.cast .U64 payload.len) := by
    simpa only [RegistrationHeaderValidation.sub_source, ok.injEq] using h.consumed
  have consumedPayload : Usize.wrapping_sub finish h.finish = payload.len := by
    apply UScalar.eq_of_val_eq
    rw [sub_value _ _ (by omega), finishValue, Slice.len_val]
    omega
  have consumedItem : Usize.wrapping_sub finish offset = RegistrationSerializerFields.byteCount payload := by
    apply UScalar.eq_of_val_eq
    rw [sub_value _ _ (by rw [finishValue, h.finishValue]; omega), finishValue, h.finishValue, byteValue]
    omega
  obtain ⟨beforePayload, payloadTail, splitPayloadOffset, _, payloadTailBytes⟩ := split_prefix input h.finish
    (headBytes ++ encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len))
    (payload.val ++ rest) (by simpa only [List.append_assoc] using contents)
    (by rw [h.finishValue, List.length_append, encoded_length, position])
  obtain ⟨payloadPart, suffix, splitPayload, _, _⟩ := split_prefix payloadTail payload.len payload.val rest
    payloadTailBytes (Slice.len_val payload)
  obtain ⟨itemPart, itemSuffix, splitItem, itemBytes, _⟩ := split_prefix h.tail (RegistrationSerializerFields.byteCount payload)
    (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val)
    rest (by simpa only [List.append_assoc] using tailBytes)
    (by rw [byteValue, List.length_append, encoded_length])
  have leafCount := validate_leaf itemPart _ _ payload.val itemBytes
    majorBound notSimple notArray notMap notTagged
    (Usize.wrapping_sub (Usize.wrapping_sub input.len offset) count) count
  have zeroBound : ¬ (0#usize : Usize) > Usize.wrapping_sub (Usize.wrapping_sub input.len offset) count := by scalar_tac
  refine ⟨finish, ?_, ?_⟩
  · simp only [validate_raw_data_item_loop.body, ↓reduceIte, index_cell, index_pack,
      core.slice.Slice.len, rust_primitives.slice.slice_length,
      RegistrationHeaderValidation.sub_source, bind_tc_ok, allowed, h.validate,
      h.splitOffset, uncurry]
    rw [consumedHeader]
    simp only [bind_tc_ok, h.splitHeader, uncurry, h.readHeader, normal_major, ↓reduceIte,
      RegistrationStringFactory.divide, fitsArgument, argument_normal, lift, cast_length, add_source,
      update_cell, index_cell]
    simp only [show Usize.wrapping_add h.finish payload.len = finish from rfl,
      splitPayloadOffset, bind_tc_ok, uncurry, consumedPayload, splitPayload, get_header_major_type, normal_major,
      ↓reduceIte, index_cell, consumedItem, splitItem]
    simp only [Array.to_slice_mut]
    have toSlice : Array.to_slice (pack count) = cell count := rfl
    have copyBack : Array.from_slice (pack count) (cell 0#usize) = pack 0#usize := rfl
    rw [toSlice, leafCount]
    simp only [bind_tc_ok, uncurry, copyBack, index_pack, Bool.false_eq_true, ↓reduceIte, zeroBound, update_pack, nextCount]
  · rw [finishValue, h.finishValue, byteValue]
    omega

end BeaconcryptCore.Refinement.RegistrationRawItems

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawItems.header_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawItems.header_at

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawItems.argument_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawItems.argument_fits

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawItems.uint_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawItems.uint_body

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawItems.array_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawItems.array_body

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawItems.bytes_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawItems.bytes_body
