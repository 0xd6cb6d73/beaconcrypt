-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationValidatorExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderValidation
import BeaconcryptCore.Refinement.RegistrationLooseArgument
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! All source argument widths, including nonminimal ones, feed the original generated non-map ordering and leaf-count operations. The complete private map/text effects remain unselected for these primitive headers. -/
namespace BeaconcryptCore.Refinement.RegistrationLooseFlatHeader
open beaconcrypt_parse.cbordetveraux
open RegistrationLooseArgument RegistrationHeaderJump
open RegistrationHeaderSize RegistrationStringFactory

set_option backward.isDefEq.respectTransparency false in
theorem header_parts (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    ∃ front tail, core.slice.Slice.split_at input (used form) = .ok (front, tail) ∧
      front.val = bytes major form ∧ tail.val = rest ∧
      read_header front = .ok (sourceHeader major form) := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_prefix input
    (used form) (bytes major form) rest contents (used_length major form)
  exact ⟨front, tail, splitInput, frontBytes, tailBytes,
    read_form front major form [] (by simpa using frontBytes) majorBound notSimple⟩

set_option backward.isDefEq.respectTransparency false in
theorem sorted [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notMap : major ≠ cbor_major_type_map) :
    cbor_raw_sorted input = .ok true := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major form rest contents majorBound notSimple
  simp only [cbor_raw_sorted, jump_form input major form rest contents majorBound, bind_tc_ok,
    splitInput, uncurry, readFront, get_header_major_type, header_major, notMap, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem count_leaf (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notArray : major ≠ cbor_major_type_array) (notMap : major ≠ cbor_major_type_map)
    (notTagged : major ≠ cbor_major_type_tagged) :
    jump_recursive_step_count_leaf input = .ok 0#usize := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major form rest contents majorBound notSimple
  simp only [jump_recursive_step_count_leaf, jump_form input major form rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront, impl_remaining_data_items_header,
    get_header_major_type, header_major, notArray, notMap, notTagged, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem validate_leaf (input : Slice U8) (major : U8) (form : Form) (rest : List U8)
    (contents : input.val = bytes major form ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (notArray : major ≠ cbor_major_type_array) (notMap : major ≠ cbor_major_type_map)
    (notTagged : major ≠ cbor_major_type_tagged) (bound before : Usize) :
    validate_recursive_step_count_leaf input bound (cell before) = .ok (false, cell 0#usize) := by
  obtain ⟨front, tail, splitInput, _, _, readFront⟩ := header_parts input major form rest contents majorBound notSimple
  simp only [validate_recursive_step_count_leaf, jump_form input major form rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront, get_header_major_type, header_major,
    notArray, notMap, notTagged, ↓reduceIte, update_cell]

end BeaconcryptCore.Refinement.RegistrationLooseFlatHeader

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.header_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.header_parts

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.sorted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.sorted

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.count_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.count_leaf

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.validate_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseFlatHeader.validate_leaf
