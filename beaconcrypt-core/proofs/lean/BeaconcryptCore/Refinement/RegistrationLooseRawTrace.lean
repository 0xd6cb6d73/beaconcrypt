-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationRawTrace
import BeaconcryptCore.Refinement.RegistrationLooseRawItems
import BeaconcryptCore.Refinement.RegistrationLooseFieldSpan
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseRawTrace
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationFlatSkip RegistrationCodecArraySingleton
open RegistrationHeaderSize RegistrationLooseArgument
open RegistrationCanonicalItems (nextCount)
open RegistrationRawTrace (Trace run)
open RegistrationLooseFieldSpan (Atom atomBytes atomsBytes)
variable [RegistrationValidatorPrimitive.Operations]
omit [RegistrationValidatorPrimitive.Operations] in
theorem atom_length (atom : Atom) : 1 ≤ (atomBytes atom).length := by
  cases atom <;> simp [atomBytes, RegistrationLooseArgument.bytes]

omit [RegistrationValidatorPrimitive.Operations] in
theorem atoms_length (atoms : List Atom) : atoms.length ≤ (atomsBytes atoms).length := by
  induction atoms with
  | nil => simp [atomsBytes]
  | cons atom rest ih =>
    simp only [atomsBytes, List.length_append, List.length_cons]
    have positive := atom_length atom
    omega

set_option backward.isDefEq.respectTransparency false in
theorem flat_trace (atoms : List Atom) :
    ∀ (input : Slice U8) (offset count : Usize) (headBytes rest : List U8),
      input.val = headBytes ++ atomsBytes atoms ++ rest → offset.val = headBytes.length →
      count.val = atoms.length →
      ∃ final, Trace input offset count final ∧ final.val = offset.val + (atomsBytes atoms).length := by
  induction atoms with
  | nil =>
    intro input offset count headBytes rest _ _ size
    have countZero : count = 0#usize := by apply UScalar.eq_of_val_eq; simpa using size
    rw [countZero]
    exact ⟨offset, Trace.stop offset, by simp [atomsBytes]⟩
  | cons atom atoms ih =>
    intro input offset count headBytes rest contents position size
    have positive : 0 < count.val := by simp only [List.length_cons] at size; omega
    have countFit : count.val ≤ input.length - offset.val := by
      have lengths := congrArg List.length contents
      simp only [List.length_append] at lengths
      change input.length = headBytes.length + (atomsBytes (atom :: atoms)).length + rest.length at lengths
      have minimum := atoms_length (atom :: atoms)
      omega
    have makeStep : ∃ finish,
        validate_raw_data_item_loop.body input (cell offset) (pack count) (pack true) true =
          .ok (.cont (cell finish, pack (nextCount count 0#usize), pack true,
            decide (nextCount count 0#usize > 0#usize))) ∧
        finish.val = offset.val + (atomBytes atom).length := by
      cases atom with
      | uint form =>
        obtain ⟨finish, body, progress⟩ := RegistrationLooseRawItems.uint_body input offset count form headBytes
          (atomsBytes atoms ++ rest) (by simpa only [atomsBytes, atomBytes, List.append_assoc, cbor_major_type_uint64, cbor_major_type_byte_string] using contents) position countFit
        exact ⟨finish, body, by simpa only [atomBytes, ← used_length] using progress⟩
      | bytes form payload payloadSize =>
        obtain ⟨finish, body, progress⟩ := RegistrationLooseRawItems.bytes_body input payload offset count form payloadSize headBytes
          (atomsBytes atoms ++ rest) (by simpa only [atomsBytes, atomBytes, List.append_assoc, cbor_major_type_uint64, cbor_major_type_byte_string] using contents) position countFit
        have fits : (used form).val + payload.length ≤ input.length := by
          have lengths := congrArg List.length contents
          simp only [atomsBytes, atomBytes, List.length_append, ← used_length] at lengths
          change input.length = headBytes.length + ((used form).val + payload.length + (atomsBytes atoms).length) + rest.length at lengths
          omega
        have sizeValue := RegistrationLooseRawItems.item_count_value input payload form fits
        exact ⟨finish, body, by simpa only [atomBytes, List.length_append, ← used_length, sizeValue] using progress⟩
    obtain ⟨finish, body, progress⟩ := makeStep
    have nextValue : (nextCount count 0#usize).val = atoms.length := by
      rw [RegistrationCanonicalTrace.next_leaf_value count positive]
      simp only [List.length_cons] at size
      omega
    obtain ⟨final, later, finalValue⟩ := ih input finish (nextCount count 0#usize)
      (headBytes ++ atomBytes atom) rest
      (by simpa only [atomsBytes, List.append_assoc] using contents)
      (by rw [List.length_append, ← position]; exact progress) nextValue
    refine ⟨final, Trace.step positive body later, ?_⟩
    rw [finalValue, progress]
    simp only [atomsBytes, List.length_append]
    omega

set_option backward.isDefEq.respectTransparency false in
theorem array8 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    Trace input 0#usize 1#usize input.len := by
  have headerWidth : (writtenCount 8#u64).val = 1 := rfl
  have minimum := atoms_length atoms
  have lengths := congrArg List.length contents
  simp only [List.length_append, encoded_length, headerWidth] at lengths
  change input.length = 1 + (atomsBytes atoms).length at lengths
  obtain ⟨afterHeader, body, afterHeaderValue⟩ := RegistrationRawItems.array_body input 0#usize 1#usize 8#u64 []
    (atomsBytes atoms) (by simpa using contents) rfl
    (by change 1 ≤ input.length - 0; omega) (by change 8 ≤ input.length - 0 - 1; omega)
  have castEight : UScalar.cast .Usize 8#u64 = 8#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationHeaderCanonical.cast_value .Usize 8#u64 (by scalar_tac)]
    rfl
  rw [castEight, RegistrationCanonicalTrace.next_initial] at body
  obtain ⟨final, later, finalValue⟩ := flat_trace atoms input afterHeader 8#usize
    (encodedBytes cbor_major_type_array 8#u64) [] (by simpa using contents)
    (by rw [afterHeaderValue, encoded_length, headerWidth]; rfl) (by simpa using size.symm)
  have finalIsLength : final = input.len := by
    apply UScalar.eq_of_val_eq
    rw [finalValue, afterHeaderValue, headerWidth, Slice.len_val]
    change 0 + 1 + (atomsBytes atoms).length = input.length
    omega
  rw [finalIsLength] at later
  apply Trace.step (children := 8#usize) (by scalar_tac)
  · simpa only [RegistrationCanonicalTrace.next_initial] using body
  · simpa only [RegistrationCanonicalTrace.next_initial] using later

set_option backward.isDefEq.respectTransparency false in
theorem validate_raw (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    validate_raw_data_item input (cell 0#usize) = .ok (true, cell input.len) := by
  have trace := array8 input atoms size contents
  simp only [validate_raw_data_item, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
    run trace, uncurry]
set_option backward.isDefEq.respectTransparency false in
theorem validate (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    cbor_validate input = .ok input.len := by
  simp only [cbor_validate, show Array.repeat 1#usize = @pack Usize from rfl,
    Array.to_slice_mut, lift, bind_tc_ok, uncurry]
  have toSlice : Array.to_slice (pack 0#usize) = cell 0#usize := rfl
  have copyBack : Array.from_slice (pack 0#usize) (cell input.len) = pack input.len := rfl
  rw [toSlice, validate_raw input atoms size contents]
  simp only [bind_tc_ok, uncurry, ↓reduceIte, copyBack, index_pack]

end BeaconcryptCore.Refinement.RegistrationLooseRawTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.atom_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.atom_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.atoms_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.atoms_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.flat_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.flat_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.array8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.array8

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.validate_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.validate_raw

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseRawTrace.validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseRawTrace.validate
