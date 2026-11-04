-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationValidatorExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderValidation
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Canonical header prefix decomposition feeds the actual generated map-order check and child-count functions. Non-map leaf checks are independent of the complete map/text effects. Container counts and bounded array-count validation are derived from actual source header arithmetic. -/
namespace BeaconcryptCore.Refinement.RegistrationFlatHeader
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump
open RegistrationHeaderSize RegistrationStringFactory

set_option backward.isDefEq.respectTransparency false in
theorem header_parts (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    ∃ front tail, core.slice.Slice.split_at input (writtenCount value) = .ok (front, tail) ∧
      front.val = encodedBytes major value ∧ tail.val = rest ∧
      read_header front = .ok (normalHeader major value) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input
    (writtenCount value) (encodedBytes major value) rest contents (encoded_length major value).symm
  exact ⟨front, tail, splitInput, frontBytes, tailBytes,
    read_encoded front major value [] (by simpa using frontBytes) majorBound notSimple⟩

set_option backward.isDefEq.respectTransparency false in
theorem sorted [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notMap : major ≠ cbor_major_type_map) :
    cbor_raw_sorted input = .ok true := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major value rest contents majorBound notSimple
  simp only [cbor_raw_sorted, jump_encoded input major value rest contents majorBound, bind_tc_ok,
    splitInput, uncurry, readFront, get_header_major_type, normal_major, notMap, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem count_leaf (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notArray : major ≠ cbor_major_type_array) (notMap : major ≠ cbor_major_type_map)
    (notTagged : major ≠ cbor_major_type_tagged) :
    jump_recursive_step_count_leaf input = .ok 0#usize := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major value rest contents majorBound notSimple
  simp only [jump_recursive_step_count_leaf, jump_encoded input major value rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront, impl_remaining_data_items_header,
    get_header_major_type, normal_major, notArray, notMap, notTagged, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem count_array (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_array value ++ rest) :
    jump_recursive_step_count_leaf input = .ok (UScalar.cast .Usize value) := by
  have bound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input _ value rest contents bound notSimple
  simp only [jump_recursive_step_count_leaf, jump_encoded input _ value rest contents bound,
    bind_tc_ok, splitInput, uncurry, readFront, impl_remaining_data_items_header,
    get_header_major_type, normal_major, ↓reduceIte, argument_normal]

set_option backward.isDefEq.respectTransparency false in
theorem validate_leaf (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notArray : major ≠ cbor_major_type_array) (notMap : major ≠ cbor_major_type_map)
    (notTagged : major ≠ cbor_major_type_tagged) (bound before : Usize) :
    validate_recursive_step_count_leaf input bound (cell before) = .ok (false, cell 0#usize) := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major value rest contents majorBound notSimple
  simp only [validate_recursive_step_count_leaf, jump_encoded input major value rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront, get_header_major_type, normal_major,
    notArray, notMap, notTagged, ↓reduceIte, update_cell]

set_option backward.isDefEq.respectTransparency false in
theorem validate_array (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_array value ++ rest)
    (bound before : Usize) (fits : value.val ≤ bound.val) :
    validate_recursive_step_count_leaf input bound (cell before) =
      .ok (false, cell (UScalar.cast .Usize value)) := by
  have majorBound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input _ value rest contents majorBound notSimple
  have fitsCast : value ≤ UScalar.cast .U64 bound := by
    simp only [UScalar.le_equiv, RegistrationSerializerFields.usize_cast]
    exact fits
  have small : ¬ quotient (quotient (quotient (quotient bound))) ≥ 16#usize := by
    have := fourth_bound bound
    scalar_tac
  simp only [validate_recursive_step_count_leaf, jump_encoded input _ value rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront, get_header_major_type, normal_major,
    ↓reduceIte, argument_normal, divide, small, lift, fitsCast, decide_true, update_cell]
end BeaconcryptCore.Refinement.RegistrationFlatHeader

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.header_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.header_parts

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.sorted

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.count_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.count_leaf

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.count_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.count_array

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.validate_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.validate_leaf

/-- info: 'BeaconcryptCore.Refinement.RegistrationFlatHeader.validate_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationFlatHeader.validate_array
