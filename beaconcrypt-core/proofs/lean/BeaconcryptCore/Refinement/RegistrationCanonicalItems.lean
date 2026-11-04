-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationFlatSkip
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Each item certificate contains only equations for actual source calls on canonical source bytes. Constructors derive these equations for unsigned integers, byte strings and array headers, including the actual map-order and width checks. The two original canonical-loop bodies retain complete effects and advance exactly through those certified source calls. -/
namespace BeaconcryptCore.Refinement.RegistrationCanonicalItems
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump RegistrationFlatHeader
open RegistrationCodecArraySingleton RegistrationFlatSkip
variable [RegistrationValidatorPrimitive.Operations]

abbrev skip := jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call

structure Item (input : Slice U8) where
  major : U8
  argument : U64
  headerFront : Slice U8
  headerTail : Slice U8
  itemFront : Slice U8
  tail : Slice U8
  stop : Usize
  children : Usize
  headerJump : jump_header input 0#usize = .ok (writtenCount argument)
  headerSplit : core.slice.Slice.split_at input (writtenCount argument) = .ok (headerFront, headerTail)
  headerRead : read_header headerFront = .ok (normalHeader major argument)
  skipSource : skip ((normalHeader major argument).fst.major_type,
    (normalHeader major argument).fst, (normalHeader major argument).snd, writtenCount argument) () = .ok stop
  itemSplit : core.slice.Slice.split_at input stop = .ok (itemFront, tail)
  itemCount : jump_recursive_step_count_leaf itemFront = .ok children
  optimal : cbor_raw_ints_optimal input = .ok true
  sorted : cbor_raw_sorted input = .ok true

def nextCount (count children : Usize) : Usize := Usize.wrapping_add (Usize.wrapping_sub count 1#usize) children

omit [RegistrationValidatorPrimitive.Operations] in
theorem skip_zero_function :
    extraction_canonical_scan_0.closure.Insts.CoreOpsFunctionFnTupleUsize.call = skip := rfl

omit [RegistrationValidatorPrimitive.Operations] in
theorem skip_one_function :
    extraction_canonical_scan_1.closure.Insts.CoreOpsFunctionFnTupleUsize.call = skip := rfl

set_option backward.isDefEq.respectTransparency false in
theorem body_zero (input : Slice U8) (item : Item input) (count : Usize) :
    extraction_canonical_scan_0_loop.body (pack count) (pack true) input true =
      .ok (.cont (pack (nextCount count item.children), pack true, item.tail,
        decide (nextCount count item.children > 0#usize))) := by
  simp only [extraction_canonical_scan_0_loop.body, ↓reduceIte, index_pack,
    item.optimal, bind_tc_ok, item.headerJump, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero,
    item.headerSplit, item.headerRead, skip_zero_function, item.skipSource,
    item.itemSplit, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, item.itemCount,
    add_source, update_pack, nextCount]

set_option backward.isDefEq.respectTransparency false in
theorem body_one (input : Slice U8) (item : Item input) (count : Usize) :
    extraction_canonical_scan_1_loop.body (pack count) (pack true) input true =
      .ok (.cont (pack (nextCount count item.children), pack true, item.tail,
        decide (nextCount count item.children > 0#usize))) := by
  simp only [extraction_canonical_scan_1_loop.body, ↓reduceIte, index_pack,
    item.sorted, bind_tc_ok, item.headerJump, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero,
    item.headerSplit, item.headerRead, skip_one_function, item.skipSource,
    item.itemSplit, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, item.itemCount,
    add_source, update_pack, nextCount]

set_option backward.isDefEq.respectTransparency false in
theorem uint_item (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ item : Item input, item.tail.val = rest ∧ item.stop = writtenCount value ∧ item.children = 0#usize := by
  have majorBound : cbor_major_type_uint64.val < 8 := by simp [cbor_major_type_uint64]
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  have notString : cbor_major_type_uint64 ≠ cbor_major_type_byte_string := by simp [cbor_major_type_uint64, cbor_major_type_byte_string]
  have notText : cbor_major_type_uint64 ≠ cbor_major_type_text_string := by simp [cbor_major_type_uint64, cbor_major_type_text_string]
  have notArray : cbor_major_type_uint64 ≠ cbor_major_type_array := by simp [cbor_major_type_uint64, cbor_major_type_array]
  have notMap : cbor_major_type_uint64 ≠ cbor_major_type_map := by simp [cbor_major_type_uint64, cbor_major_type_map]
  have notTagged : cbor_major_type_uint64 ≠ cbor_major_type_tagged := by simp [cbor_major_type_uint64, cbor_major_type_tagged]
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes, readFront⟩ := header_parts input _ value rest contents majorBound notSimple
  have countFront := count_leaf front _ value [] (by simpa using frontBytes) majorBound notSimple notArray notMap notTagged
  let item : Item input := {
    major := cbor_major_type_uint64, argument := value,
    headerFront := front, headerTail := tail, itemFront := front, tail := tail,
    stop := writtenCount value, children := 0#usize,
    headerJump := jump_encoded input _ value rest contents majorBound,
    headerSplit := splitInput, headerRead := readFront,
    skipSource := by
      dsimp only [skip, jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call, jump_raw_data_item.closure]
      simp only [uncurry, normal_major, notString, notText, ↓reduceIte],
    itemSplit := splitInput, itemCount := countFront,
    optimal := optimal_encoded input _ value rest contents majorBound notSimple,
    sorted := RegistrationFlatHeader.sorted input _ value rest contents majorBound notSimple notMap }
  exact ⟨item, tailBytes, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem bytes_item (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    ∃ item : Item input, item.tail.val = rest ∧ item.stop = RegistrationSerializerFields.byteCount payload ∧ item.children = 0#usize := by
  have majorBound : cbor_major_type_byte_string.val < 8 := by simp [cbor_major_type_byte_string]
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  have notArray : cbor_major_type_byte_string ≠ cbor_major_type_array := by simp [cbor_major_type_byte_string, cbor_major_type_array]
  have notMap : cbor_major_type_byte_string ≠ cbor_major_type_map := by simp [cbor_major_type_byte_string, cbor_major_type_map]
  have notTagged : cbor_major_type_byte_string ≠ cbor_major_type_tagged := by simp [cbor_major_type_byte_string, cbor_major_type_tagged]
  have headerBytes : input.val = encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ (payload.val ++ rest) := by
    simpa only [List.append_assoc] using contents
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input _ _ (payload.val ++ rest) headerBytes majorBound notSimple
  have fit : (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length ≤ input.length := by
    have lengths := congrArg List.length contents
    simp only [List.length_append, encoded_length] at lengths
    change input.length = (writtenCount (UScalar.cast .U64 payload.len)).val + payload.length + rest.length at lengths
    omega
  have sizeValue := RegistrationSerializerFields.byte_count_value input payload fit
  obtain ⟨itemFront, suffix, splitItem, itemBytes, suffixBytes⟩ := split_prefix input
    (RegistrationSerializerFields.byteCount payload)
    (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val)
    rest contents (by rw [sizeValue, List.length_append, encoded_length])
  have countFront := count_leaf itemFront _ _ payload.val itemBytes majorBound notSimple notArray notMap notTagged
  let item : Item input := {
    major := cbor_major_type_byte_string, argument := UScalar.cast .U64 payload.len,
    headerFront := front, headerTail := tail, itemFront := itemFront, tail := suffix,
    stop := RegistrationSerializerFields.byteCount payload, children := 0#usize,
    headerJump := jump_encoded input _ _ (payload.val ++ rest) headerBytes majorBound,
    headerSplit := splitInput, headerRead := readFront,
    skipSource := by
      dsimp only [skip, jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call, jump_raw_data_item.closure]
      simp only [uncurry, normal_major, ↓reduceIte, argument_normal, lift, bind_tc_ok, cast_length, add_source,
      RegistrationSerializerFields.byteCount],
    itemSplit := splitItem, itemCount := countFront,
    optimal := optimal_encoded input _ _ (payload.val ++ rest) headerBytes majorBound notSimple,
    sorted := RegistrationFlatHeader.sorted input _ _ (payload.val ++ rest) headerBytes majorBound notSimple notMap }
  exact ⟨item, suffixBytes, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem array_item (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_array value ++ rest) :
    ∃ item : Item input, item.tail.val = rest ∧ item.stop = writtenCount value ∧
      item.children = UScalar.cast .Usize value := by
  have majorBound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  have notString : cbor_major_type_array ≠ cbor_major_type_byte_string := by simp [cbor_major_type_array, cbor_major_type_byte_string]
  have notText : cbor_major_type_array ≠ cbor_major_type_text_string := by simp [cbor_major_type_array, cbor_major_type_text_string]
  have notMap : cbor_major_type_array ≠ cbor_major_type_map := by simp [cbor_major_type_array, cbor_major_type_map]
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes, readFront⟩ := header_parts input _ value rest contents majorBound notSimple
  have countFront := count_array front value [] (by simpa using frontBytes)
  let item : Item input := {
    major := cbor_major_type_array, argument := value,
    headerFront := front, headerTail := tail, itemFront := front, tail := tail,
    stop := writtenCount value, children := UScalar.cast .Usize value,
    headerJump := jump_encoded input _ value rest contents majorBound,
    headerSplit := splitInput, headerRead := readFront,
    skipSource := by
      dsimp only [skip, jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call, jump_raw_data_item.closure]
      simp only [uncurry, normal_major, notString, notText, ↓reduceIte],
    itemSplit := splitInput, itemCount := countFront,
    optimal := optimal_encoded input _ value rest contents majorBound notSimple,
    sorted := RegistrationFlatHeader.sorted input _ value rest contents majorBound notSimple notMap }
  exact ⟨item, tailBytes, rfl, rfl⟩
end BeaconcryptCore.Refinement.RegistrationCanonicalItems

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.skip_zero_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.skip_zero_function

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.skip_one_function' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.skip_one_function

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.body_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.body_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.body_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.body_one

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.uint_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.uint_item

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.bytes_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.bytes_item

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalItems.array_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalItems.array_item
