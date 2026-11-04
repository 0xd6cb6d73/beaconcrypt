-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderBits
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual generated header-reader equations for initial, short and one-byte
arguments, on exact input lists with arbitrary suffixes. They do not assert
canonical validation, public parser success or complete codec readback. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderReadback
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits

theorem first_index (input : Slice U8) (first : U8) (rest : List U8)
    (contents : input.val = first :: rest) : Slice.index_usize input 0#usize = .ok first := by
  simp [Slice.index_usize, Slice.getElem?_Usize_eq, contents]

set_option backward.isDefEq.respectTransparency false in
theorem split_first (input : Slice U8) (first : U8) (rest : List U8)
    (contents : input.val = first :: rest) :
    ∃ front tail, core.slice.Slice.split_at input 1#usize = .ok (front, tail) ∧
      front.val = [first] ∧ tail.val = rest := by
  let front : Slice U8 := ⟨[first], by simp; scalar_tac⟩
  let tail : Slice U8 := ⟨rest, by
    have bound := input.property
    rw [contents] at bound
    simp only [List.length_cons] at bound
    omega⟩
  refine ⟨front, tail, ?_, rfl, rfl⟩
  simp [CoreModels.core.slice.Slice.split_at, CoreModels.rust_primitives.slice.slice_split_at,
    Aeneas.Std.core.slice.Slice.split_at, contents, List.splitAt_eq, front, tail, Slice.length]

theorem read_initial (input : Slice U8) (major additional : U8) (rest : List U8)
    (contents : input.val = packed major additional :: rest)
    (majorBound : major.val < 8) (additionalBound : additional.val < 32) :
    read_initial_byte_t input = .ok { major_type := major, additional_info := additional } := by
  unfold read_initial_byte_t
  rw [first_index input _ rest contents]
  simp only [bind_tc_ok, read_major major additional majorBound,
    read_additional major additional additionalBound]

set_option backward.isDefEq.respectTransparency false in
theorem read_short (input : Slice U8) (major additional : U8) (rest : List U8)
    (contents : input.val = packed major additional :: rest)
    (majorBound : major.val < 8) (additionalBound : additional.val < 24) :
    read_header input = .ok {
      fst := { major_type := major, additional_info := additional }
      snd := .LongArgumentOther } := by
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := split_first input _ rest contents
  unfold read_header
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major additional [] frontBytes majorBound (by omega)]
  simp only [bind_tc_ok]
  have not8 : additional ≠ additional_info_long_argument_8_bits := by
    simp only [additional_info_long_argument_8_bits]
    scalar_tac
  have not16 : additional ≠ additional_info_long_argument_16_bits := by
    simp only [additional_info_long_argument_16_bits]
    scalar_tac
  have not32 : additional ≠ additional_info_long_argument_32_bits := by
    simp only [additional_info_long_argument_32_bits]
    scalar_tac
  have not64 : additional ≠ additional_info_long_argument_64_bits := by
    simp only [additional_info_long_argument_64_bits]
    scalar_tac
  simp only [not8, not16, not32, not64, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem read_byte_argument (input : Slice U8) (major value : U8) (rest : List U8)
    (contents : input.val = packed major 24#u8 :: value :: rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    read_header input = .ok {
      fst := { major_type := major, additional_info := 24#u8 }
      snd := .LongArgumentU8 value } := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_first input _ (value :: rest) contents
  unfold read_header
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major 24#u8 [] frontBytes majorBound (by scalar_tac)]
  simp only [bind_tc_ok, additional_info_long_argument_8_bits, notSimple, ↓reduceIte]
  rw [first_index tail value rest tailBytes]
  rfl

end BeaconcryptCore.Refinement.RegistrationHeaderReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderReadback.first_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderReadback.first_index
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderReadback.split_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderReadback.split_first
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_initial
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_short
/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_byte_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderReadback.read_byte_argument
