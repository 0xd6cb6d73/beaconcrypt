-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationRawItems
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Finite execution of the actual structural-validation loop covers a canonical array of eight arbitrary UInt64/byte-string atoms. The final source offset equals the complete input length. Combined with both original canonical scans, actual cbor_validate_det accepts exactly that complete encoded input, and actual cbor_det_parse retains an empty remainder before reading the original CBOR object. Schema field validation and public preflight are composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationRawTrace
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationRawItems RegistrationFlatSkip RegistrationCodecArraySingleton
open RegistrationCanonicalTrace (Atom atomBytes atomsBytes)
open RegistrationCanonicalItems (nextCount)
open RegistrationHeaderSize
variable [RegistrationValidatorPrimitive.Operations]

inductive Trace (input : Slice U8) : Usize → Usize → Usize → Prop where
| stop (offset : Usize) : Trace input offset 0#usize offset
| step {offset count finish final children : Usize}
    (positive : 0 < count.val)
    (body : validate_raw_data_item_loop.body input (cell offset) (pack count) (pack true) true =
      .ok (.cont (cell finish, pack (nextCount count children), pack true,
        decide (nextCount count children > 0#usize))))
    (later : Trace input finish (nextCount count children) final) : Trace input offset count final

theorem loop_unfold (input : Slice U8) (offset : Slice Usize) (count : Array Usize 1#usize)
    (success : Array Bool 1#usize) (condition : Bool) :
    validate_raw_data_item_loop input offset count success condition =
      (validate_raw_data_item_loop.body input offset count success condition >>= fun result =>
        match result with
        | .cont (offsetNext, countNext, successNext, conditionNext) =>
          validate_raw_data_item_loop input offsetNext countNext successNext conditionNext
        | .done result => .ok result) := by
  unfold validate_raw_data_item_loop
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem run {input : Slice U8} {offset count final : Usize} (trace : Trace input offset count final) :
    validate_raw_data_item_loop input (cell offset) (pack count) (pack true)
      (decide (count > 0#usize)) = .ok (cell final, pack true) := by
  induction trace with
  | stop offset =>
    rw [loop_unfold]
    simp [validate_raw_data_item_loop.body, bind_tc_ok]
  | @step offset count finish final children positive body later ih =>
    have running : decide (count > 0#usize) = true := by
      simp only [decide_eq_true_eq, UScalar.lt_equiv]
      exact positive
    rw [loop_unfold, running, body]
    simp only [bind_tc_ok]
    exact ih

omit [RegistrationValidatorPrimitive.Operations] in
theorem atom_length (atom : Atom) : 1 ≤ (atomBytes atom).length := by
  cases atom with
  | uint value =>
    simp only [atomBytes, encoded_length]
    exact Nat.succ_le_of_lt (RegistrationSerializerFields.header_positive value)
  | bytes value =>
    simp only [atomBytes, List.length_append, encoded_length]
    have positive : 0 < (writtenCount (UScalar.cast .U64 value.len)).val := RegistrationSerializerFields.header_positive (UScalar.cast .U64 value.len)
    omega

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
      | uint value =>
        obtain ⟨finish, body, progress⟩ := RegistrationRawItems.uint_body input offset count value headBytes
          (atomsBytes atoms ++ rest) (by simpa only [atomsBytes, atomBytes, List.append_assoc] using contents) position countFit
        exact ⟨finish, body, by simpa only [atomBytes, encoded_length] using progress⟩
      | bytes value =>
        obtain ⟨finish, body, progress⟩ := RegistrationRawItems.bytes_body input value offset count headBytes
          (atomsBytes atoms ++ rest) (by simpa only [atomsBytes, atomBytes, List.append_assoc] using contents) position countFit
        have fits : (writtenCount (UScalar.cast .U64 value.len)).val + value.length ≤ input.length := by
          have lengths := congrArg List.length contents
          simp only [atomsBytes, atomBytes, List.length_append, encoded_length] at lengths
          change input.length = headBytes.length + ((writtenCount (UScalar.cast .U64 value.len)).val + value.length + (atomsBytes atoms).length) + rest.length at lengths
          omega
        have sizeValue := RegistrationSerializerFields.byte_count_value input value fits
        exact ⟨finish, body, by simpa only [atomBytes, List.length_append, encoded_length, sizeValue] using progress⟩
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

omit [RegistrationValidatorPrimitive.Operations] in
theorem split_full (input : Slice U8) :
    core.slice.Slice.split_at input input.len = .ok (input, empty) := by
  obtain ⟨front, tail, source, frontBytes, tailBytes⟩ := RegistrationHeaderJump.split_prefix input input.len
    input.val [] (by simp) (Slice.len_val input)
  have frontEq : front = input := Subtype.ext frontBytes
  have tailEq : tail = empty := Subtype.ext tailBytes
  simpa only [frontEq, tailEq] using source

omit [RegistrationValidatorPrimitive.Operations] in
theorem length_nonzero (input : Slice U8) (atoms : List Atom)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    input.len ≠ 0#usize := by
  have lengths := congrArg List.length contents
  simp only [List.length_append, encoded_length] at lengths
  have width : 0 < (writtenCount 8#u64).val := RegistrationSerializerFields.header_positive 8#u64
  intro zero
  have inputZero : input.length = 0 := by simpa using congrArg UScalar.val zero
  change input.length = _ at lengths
  omega

set_option backward.isDefEq.respectTransparency false in
theorem validate_det (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    cbor_validate_det input = .ok input.len := by
  have nonzero := length_nonzero input atoms contents
  obtain ⟨widthScan, orderScan⟩ := RegistrationCanonicalTrace.scans input atoms size contents
  simp only [cbor_validate_det, bcExtractedToken63626f725f76616c69646174655f646574c2b7,
    validate input atoms size contents, bind_tc_ok, nonzero, ↓reduceIte, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero, split_full,
    lift, beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, widthScan, orderScan]

set_option backward.isDefEq.respectTransparency false in
theorem parse (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    beaconcrypt_parse.cbordetver.cbor_det_parse input =
      (do let raw ← cbor_read input
          .ok (.Some (raw, empty))) := by
  have nonzero := length_nonzero input atoms contents
  simp only [beaconcrypt_parse.cbordetver.cbor_det_parse, validate_det input atoms size contents,
    bind_tc_ok, nonzero, ↓reduceIte, split_full, uncurry, core.slice.Slice.len,
    rust_primitives.slice.slice_length, cbor_parse, split_zero,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem array6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    Trace input 0#usize 1#usize input.len := by
  have headerWidth : (writtenCount 6#u64).val = 1 := rfl
  have minimum := atoms_length atoms
  have lengths := congrArg List.length contents
  simp only [List.length_append, encoded_length, headerWidth] at lengths
  change input.length = 1 + (atomsBytes atoms).length at lengths
  obtain ⟨afterHeader, body, afterHeaderValue⟩ := RegistrationRawItems.array_body input 0#usize 1#usize 6#u64 []
    (atomsBytes atoms) (by simpa using contents) rfl
    (by change 1 ≤ input.length - 0; omega) (by change 6 ≤ input.length - 0 - 1; omega)
  have castSix : UScalar.cast .Usize 6#u64 = 6#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationHeaderCanonical.cast_value .Usize 6#u64 (by scalar_tac)]
    rfl
  rw [castSix, RegistrationCanonicalTrace.next_initial] at body
  obtain ⟨final, later, finalValue⟩ := flat_trace atoms input afterHeader 6#usize
    (encodedBytes cbor_major_type_array 6#u64) [] (by simpa using contents)
    (by rw [afterHeaderValue, encoded_length, headerWidth]; rfl) (by simpa using size.symm)
  have finalIsLength : final = input.len := by
    apply UScalar.eq_of_val_eq
    rw [finalValue, afterHeaderValue, headerWidth, Slice.len_val]
    change 0 + 1 + (atomsBytes atoms).length = input.length
    omega
  rw [finalIsLength] at later
  apply Trace.step (children := 6#usize) (by scalar_tac)
  · simpa only [RegistrationCanonicalTrace.next_initial] using body
  · simpa only [RegistrationCanonicalTrace.next_initial] using later

set_option backward.isDefEq.respectTransparency false in
theorem validate_raw6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    validate_raw_data_item input (cell 0#usize) = .ok (true, cell input.len) := by
  have trace := array6 input atoms size contents
  simp only [validate_raw_data_item, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
    run trace, uncurry]
set_option backward.isDefEq.respectTransparency false in
theorem validate6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    cbor_validate input = .ok input.len := by
  simp only [cbor_validate, show Array.repeat 1#usize = @pack Usize from rfl,
    Array.to_slice_mut, lift, bind_tc_ok, uncurry]
  have toSlice : Array.to_slice (pack 0#usize) = cell 0#usize := rfl
  have copyBack : Array.from_slice (pack 0#usize) (cell input.len) = pack input.len := rfl
  rw [toSlice, validate_raw6 input atoms size contents]
  simp only [bind_tc_ok, uncurry, ↓reduceIte, copyBack, index_pack]

omit [RegistrationValidatorPrimitive.Operations] in
theorem length_nonzero6 (input : Slice U8) (atoms : List Atom)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    input.len ≠ 0#usize := by
  have lengths := congrArg List.length contents
  simp only [List.length_append, encoded_length] at lengths
  have width : 0 < (writtenCount 6#u64).val := RegistrationSerializerFields.header_positive 6#u64
  intro zero
  have inputZero : input.length = 0 := by simpa using congrArg UScalar.val zero
  change input.length = _ at lengths
  omega

set_option backward.isDefEq.respectTransparency false in
theorem validate_det6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    cbor_validate_det input = .ok input.len := by
  have nonzero := length_nonzero6 input atoms contents
  obtain ⟨widthScan, orderScan⟩ := RegistrationCanonicalTrace.scans6 input atoms size contents
  simp only [cbor_validate_det, bcExtractedToken63626f725f76616c69646174655f646574c2b7,
    validate6 input atoms size contents, bind_tc_ok, nonzero, ↓reduceIte, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero, split_full,
    lift, beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, widthScan, orderScan]

set_option backward.isDefEq.respectTransparency false in
theorem parse6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    beaconcrypt_parse.cbordetver.cbor_det_parse input =
      (do let raw ← cbor_read input
          .ok (.Some (raw, empty))) := by
  have nonzero := length_nonzero6 input atoms contents
  simp only [beaconcrypt_parse.cbordetver.cbor_det_parse, validate_det6 input atoms size contents,
    bind_tc_ok, nonzero, ↓reduceIte, split_full, uncurry, core.slice.Slice.len,
    rust_primitives.slice.slice_length, cbor_parse, split_zero,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero]

end BeaconcryptCore.Refinement.RegistrationRawTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.loop_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.loop_unfold

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.run

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.atom_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.atom_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.atoms_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.atoms_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.flat_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.flat_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.array8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.array8

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate_raw

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.split_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.split_full

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.length_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.length_nonzero

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate_det

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.parse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.array6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.array6

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate_raw6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate_raw6

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate6

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.length_nonzero6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.length_nonzero6

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.validate_det6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.validate_det6

/-- info: 'BeaconcryptCore.Refinement.RegistrationRawTrace.parse6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationRawTrace.parse6
