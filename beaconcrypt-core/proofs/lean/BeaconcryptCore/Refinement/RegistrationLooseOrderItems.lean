-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseRawItems
import BeaconcryptCore.Refinement.RegistrationCanonicalItems
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseOrderItems
open beaconcrypt_parse.cbordetveraux RegistrationHeaderJump RegistrationHeaderSize
open RegistrationLooseArgument RegistrationLooseFlatHeader RegistrationCodecArraySingleton RegistrationFlatSkip
open RegistrationCanonicalItems (skip nextCount skip_one_function)
variable [RegistrationValidatorPrimitive.Operations]

structure Item (input : Slice U8) where
  rawHeader : header
  width : Usize
  headerFront : Slice U8
  headerTail : Slice U8
  itemFront : Slice U8
  tail : Slice U8
  stop : Usize
  children : Usize
  headerJump : jump_header input 0#usize = .ok width
  headerSplit : core.slice.Slice.split_at input width = .ok (headerFront, headerTail)
  headerRead : read_header headerFront = .ok rawHeader
  skipSource : skip (rawHeader.fst.major_type, rawHeader.fst, rawHeader.snd, width) () = .ok stop
  itemSplit : core.slice.Slice.split_at input stop = .ok (itemFront, tail)
  itemCount : jump_recursive_step_count_leaf itemFront = .ok children
  sorted : cbor_raw_sorted input = .ok true

def fromCanonical {input : Slice U8} (item : RegistrationCanonicalItems.Item input) : Item input where
  rawHeader := RegistrationHeaderCanonical.normalHeader item.major item.argument
  width := RegistrationHeaderCanonical.writtenCount item.argument
  headerFront := item.headerFront
  headerTail := item.headerTail
  itemFront := item.itemFront
  tail := item.tail
  stop := item.stop
  children := item.children
  headerJump := item.headerJump
  headerSplit := item.headerSplit
  headerRead := item.headerRead
  skipSource := item.skipSource
  itemSplit := item.itemSplit
  itemCount := item.itemCount
  sorted := item.sorted

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
theorem uint_item (input : Slice U8) (form : Form) (rest : List U8)
    (contents : input.val = RegistrationLooseArgument.bytes cbor_major_type_uint64 form ++ rest) :
    ∃ item : Item input, item.tail.val = rest ∧ item.stop = used form ∧ item.children = 0#usize := by
  have majorBound : cbor_major_type_uint64.val < 8 := by simp [cbor_major_type_uint64]
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  have notString : cbor_major_type_uint64 ≠ cbor_major_type_byte_string := by simp [cbor_major_type_uint64, cbor_major_type_byte_string]
  have notText : cbor_major_type_uint64 ≠ cbor_major_type_text_string := by simp [cbor_major_type_uint64, cbor_major_type_text_string]
  have notArray : cbor_major_type_uint64 ≠ cbor_major_type_array := by simp [cbor_major_type_uint64, cbor_major_type_array]
  have notMap : cbor_major_type_uint64 ≠ cbor_major_type_map := by simp [cbor_major_type_uint64, cbor_major_type_map]
  have notTagged : cbor_major_type_uint64 ≠ cbor_major_type_tagged := by simp [cbor_major_type_uint64, cbor_major_type_tagged]
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes, readFront⟩ := header_parts input _ form rest contents majorBound notSimple
  have countFront := count_leaf front _ form [] (by simpa using frontBytes) majorBound notSimple notArray notMap notTagged
  let item : Item input := {
    rawHeader := sourceHeader cbor_major_type_uint64 form, width := used form,
    headerFront := front, headerTail := tail, itemFront := front, tail := tail,
    stop := used form, children := 0#usize,
    headerJump := jump_form input _ form rest contents majorBound,
    headerSplit := splitInput, headerRead := readFront,
    skipSource := by
      dsimp only [skip, jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call, jump_raw_data_item.closure]
      simp only [uncurry, header_major, notString, notText, ↓reduceIte],
    itemSplit := splitInput, itemCount := countFront,
    sorted := RegistrationLooseFlatHeader.sorted input _ form rest contents majorBound notSimple notMap }
  exact ⟨item, tailBytes, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem bytes_item (input payload : Slice U8) (form : Form)
    (size : value form = UScalar.cast .U64 payload.len) (rest : List U8)
    (contents : input.val = (RegistrationLooseArgument.bytes cbor_major_type_byte_string form ++ payload.val) ++ rest) :
    ∃ item : Item input, item.tail.val = rest ∧ item.stop = RegistrationLooseRawItems.itemCount form payload ∧ item.children = 0#usize := by
  have majorBound : cbor_major_type_byte_string.val < 8 := by simp [cbor_major_type_byte_string]
  have notSimple : cbor_major_type_byte_string ≠ cbor_major_type_simple_value := by simp [cbor_major_type_byte_string, cbor_major_type_simple_value]
  have notArray : cbor_major_type_byte_string ≠ cbor_major_type_array := by simp [cbor_major_type_byte_string, cbor_major_type_array]
  have notMap : cbor_major_type_byte_string ≠ cbor_major_type_map := by simp [cbor_major_type_byte_string, cbor_major_type_map]
  have notTagged : cbor_major_type_byte_string ≠ cbor_major_type_tagged := by simp [cbor_major_type_byte_string, cbor_major_type_tagged]
  have headerBytes : input.val = RegistrationLooseArgument.bytes cbor_major_type_byte_string form ++ (payload.val ++ rest) := by
    simpa only [List.append_assoc] using contents
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input _ _ (payload.val ++ rest) headerBytes majorBound notSimple
  have fit : (used form).val + payload.length ≤ input.length := by
    have lengths := congrArg List.length contents
    simp only [List.length_append, ← used_length] at lengths
    change input.length = (used form).val + payload.length + rest.length at lengths
    omega
  have sizeValue := RegistrationLooseRawItems.item_count_value input payload form fit
  obtain ⟨itemFront, suffix, splitItem, itemBytes, suffixBytes⟩ := split_prefix input
    (RegistrationLooseRawItems.itemCount form payload)
    (RegistrationLooseArgument.bytes cbor_major_type_byte_string form ++ payload.val)
    rest contents (by rw [sizeValue, List.length_append, ← used_length])
  have countFront := count_leaf itemFront _ _ payload.val itemBytes majorBound notSimple notArray notMap notTagged
  let item : Item input := {
    rawHeader := sourceHeader cbor_major_type_byte_string form, width := used form,
    headerFront := front, headerTail := tail, itemFront := itemFront, tail := suffix,
    stop := RegistrationLooseRawItems.itemCount form payload, children := 0#usize,
    headerJump := jump_form input _ _ (payload.val ++ rest) headerBytes majorBound,
    headerSplit := splitInput, headerRead := readFront,
    skipSource := by
      dsimp only [skip, jump_raw_data_item.closure.Insts.CoreOpsFunctionFnTupleUsize.call, jump_raw_data_item.closure]
      simp only [uncurry, header_major, ↓reduceIte, argument_value, size, lift, bind_tc_ok, cast_length, add_source,
      RegistrationLooseRawItems.itemCount],
    itemSplit := splitItem, itemCount := countFront,
    sorted := RegistrationLooseFlatHeader.sorted input _ _ (payload.val ++ rest) headerBytes majorBound notSimple notMap }
  exact ⟨item, suffixBytes, rfl, rfl⟩

end BeaconcryptCore.Refinement.RegistrationLooseOrderItems

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderItems.body_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderItems.body_one

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderItems.uint_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderItems.uint_item

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderItems.bytes_item' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderItems.bytes_item
