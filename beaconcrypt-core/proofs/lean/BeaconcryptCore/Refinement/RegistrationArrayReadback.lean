-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationRawTrace
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual cbor_read reconstructs the original serialized array header and borrowed payload. Composing the complete raw/canonical source validation yields the actual cbor_det_parse object with an empty remainder for every array8 primitive encoding. Schema field readback is separate. -/
namespace BeaconcryptCore.Refinement.RegistrationArrayReadback
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationHeaderCanonicalRead RegistrationHeaderJump RegistrationFlatHeader
open RegistrationCodecArraySingleton RegistrationFlatSkip

abbrev array8 (payload : Slice U8) : cbor_raw := .CBOR_Case_Serialized_Array {
  cbor_serialized_header := { size := 0#u8, value := 8#u64 }
  cbor_serialized_payload := payload }

set_option backward.isDefEq.respectTransparency false in
theorem read (input : Slice U8) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ rest) :
    ∃ payload, payload.val = rest ∧ cbor_read input = .ok (array8 payload) := by
  have majorBound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, _, tailBytes, readFront⟩ := header_parts input _ 8#u64 rest contents majorBound notSimple
  refine ⟨tail, tailBytes, ?_⟩
  simp only [cbor_read, jump_encoded input _ 8#u64 rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront,
    show Array.repeat 1#usize = @pack header from rfl, update_pack, index_pack, normal_major]
  simp only [cbor_major_type_array, cbor_major_type_uint64, cbor_major_type_neg_int64,
    cbor_major_type_text_string, cbor_major_type_byte_string, cbor_major_type_tagged,
    ↓reduceIte]
  simp only [normalHeader, show (8#u64).val = 8 from rfl, Nat.reduceLT, ↓reduceIte,
    lift, bind_tc_ok, cast_roundtrip .U8 8#u64 (by scalar_tac)]
  simp [array8]

set_option backward.isDefEq.respectTransparency false in
theorem parse [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (atoms : List RegistrationCanonicalTrace.Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ RegistrationCanonicalTrace.atomsBytes atoms) :
    ∃ payload, payload.val = RegistrationCanonicalTrace.atomsBytes atoms ∧
      cbordetver.cbor_det_parse input = .ok (.Some (array8 payload, empty)) := by
  obtain ⟨payload, payloadBytes, sourceRead⟩ := read input (RegistrationCanonicalTrace.atomsBytes atoms) contents
  refine ⟨payload, payloadBytes, ?_⟩
  rw [RegistrationRawTrace.parse input atoms size contents, sourceRead]
  simp only [bind_tc_ok]
abbrev array6 (payload : Slice U8) : cbor_raw := .CBOR_Case_Serialized_Array {
  cbor_serialized_header := { size := 0#u8, value := 6#u64 }
  cbor_serialized_payload := payload }

set_option backward.isDefEq.respectTransparency false in
theorem read6 (input : Slice U8) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ rest) :
    ∃ payload, payload.val = rest ∧ cbor_read input = .ok (array6 payload) := by
  have majorBound : cbor_major_type_array.val < 8 := by simp [cbor_major_type_array]
  have notSimple : cbor_major_type_array ≠ cbor_major_type_simple_value := by simp [cbor_major_type_array, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, _, tailBytes, readFront⟩ := header_parts input _ 6#u64 rest contents majorBound notSimple
  refine ⟨tail, tailBytes, ?_⟩
  simp only [cbor_read, jump_encoded input _ 6#u64 rest contents majorBound,
    bind_tc_ok, splitInput, uncurry, readFront,
    show Array.repeat 1#usize = @pack header from rfl, update_pack, index_pack, normal_major]
  simp only [cbor_major_type_array, cbor_major_type_uint64, cbor_major_type_neg_int64,
    cbor_major_type_text_string, cbor_major_type_byte_string, cbor_major_type_tagged,
    ↓reduceIte]
  simp only [normalHeader, show (6#u64).val = 6 from rfl, Nat.reduceLT, ↓reduceIte,
    lift, bind_tc_ok, cast_roundtrip .U8 6#u64 (by scalar_tac)]
  simp [array6]

set_option backward.isDefEq.respectTransparency false in
theorem parse6 [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (atoms : List RegistrationCanonicalTrace.Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ RegistrationCanonicalTrace.atomsBytes atoms) :
    ∃ payload, payload.val = RegistrationCanonicalTrace.atomsBytes atoms ∧
      cbordetver.cbor_det_parse input = .ok (.Some (array6 payload, empty)) := by
  obtain ⟨payload, payloadBytes, sourceRead⟩ := read6 input (RegistrationCanonicalTrace.atomsBytes atoms) contents
  refine ⟨payload, payloadBytes, ?_⟩
  rw [RegistrationRawTrace.parse6 input atoms size contents, sourceRead]
  simp only [bind_tc_ok]
end BeaconcryptCore.Refinement.RegistrationArrayReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayReadback.read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayReadback.read

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayReadback.parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayReadback.parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayReadback.read6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayReadback.read6

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayReadback.parse6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayReadback.parse6
