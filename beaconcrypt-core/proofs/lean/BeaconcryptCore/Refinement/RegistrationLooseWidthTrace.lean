-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseOptimal
import BeaconcryptCore.Refinement.RegistrationLooseFieldSpan
import BeaconcryptCore.Refinement.RegistrationCanonicalTrace
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseWidthTrace
open beaconcrypt_parse.cbordetveraux RegistrationCodecArraySingleton RegistrationFlatSkip
open RegistrationLooseOrderItems
open RegistrationCanonicalItems (nextCount skip_zero_function)
open RegistrationLooseFieldSpan (Atom atomBytes atomsBytes)
variable [RegistrationValidatorPrimitive.Operations]

def atomMinimal : Atom → Bool
  | .uint form | .bytes form _ _ => RegistrationLooseOptimal.minimal form

set_option backward.isDefEq.respectTransparency false in
theorem body_true (input : Slice U8) (item : Item input) (count : Usize)
    (checked : cbor_raw_ints_optimal input = .ok true) :
    extraction_canonical_scan_0_loop.body (pack count) (pack true) input true =
      .ok (.cont (pack (nextCount count item.children), pack true, item.tail,
        decide (nextCount count item.children > 0#usize))) := by
  simp only [extraction_canonical_scan_0_loop.body, ↓reduceIte, index_pack,
    checked, bind_tc_ok, item.headerJump, split_zero, uncurry,
    RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero,
    item.headerSplit, item.headerRead, skip_zero_function, item.skipSource,
    item.itemSplit, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.lowstar.ignore.bcSchemaRepeatedIgnore2, item.itemCount,
    add_source, update_pack, nextCount]

omit [RegistrationValidatorPrimitive.Operations] in
set_option backward.isDefEq.respectTransparency false in
theorem body_false (input : Slice U8) (count : Usize)
    (checked : cbor_raw_ints_optimal input = .ok false) :
    extraction_canonical_scan_0_loop.body (pack count) (pack true) input true =
      .ok (.cont (pack count, pack false, input, false)) := by
  simp only [extraction_canonical_scan_0_loop.body, ↓reduceIte, index_pack,
    checked, bind_tc_ok, Bool.false_eq_true, update_pack]

omit [RegistrationValidatorPrimitive.Operations] in
set_option backward.isDefEq.respectTransparency false in
theorem stopped (input : Slice U8) (count : Usize) :
    extraction_canonical_scan_0_loop (pack count) (pack false) input false = .ok (pack false) := by
  rw [RegistrationCanonicalTrace.loop_zero_unfold]
  simp only [extraction_canonical_scan_0_loop.body, Bool.false_eq_true, ↓reduceIte, bind_tc_ok]

set_option backward.isDefEq.respectTransparency false in
theorem flat (atoms : List Atom) :
    ∀ (input : Slice U8) (count : Usize), input.val = atomsBytes atoms → count.val = atoms.length →
      extraction_canonical_scan_0_loop (pack count) (pack true) input (decide (count > 0#usize)) =
        .ok (pack (atoms.all atomMinimal)) := by
  induction atoms with
  | nil =>
    intro input count _ size
    have countZero : count = 0#usize := by apply UScalar.eq_of_val_eq; simpa using size
    rw [countZero, RegistrationCanonicalTrace.loop_zero_unfold]
    simp only [extraction_canonical_scan_0_loop.body,
      show decide (0#usize > 0#usize) = false from rfl, Bool.false_eq_true, ↓reduceIte, bind_tc_ok, List.all_nil]
  | cons atom rest ih =>
    intro input count contents size
    have positive : 0 < count.val := by simp only [List.length_cons] at size; omega
    have running : decide (count > 0#usize) = true := by simp only [decide_eq_true_eq, UScalar.lt_equiv]; exact positive
    have makeItem : ∃ item : Item input, item.tail.val = atomsBytes rest ∧ item.children = 0#usize ∧
        cbor_raw_ints_optimal input = .ok (atomMinimal atom) := by
      cases atom with
      | uint form =>
        have bytes : input.val = RegistrationLooseArgument.bytes cbor_major_type_uint64 form ++ atomsBytes rest := by
          simpa only [atomsBytes, atomBytes, cbor_major_type_uint64] using contents
        obtain ⟨item, tail, _, children⟩ := uint_item input form (atomsBytes rest) bytes
        refine ⟨item, tail, children, ?_⟩
        exact RegistrationLooseOptimal.optimal_form input _ form (atomsBytes rest) bytes
          (by simp [cbor_major_type_uint64]) (by simp [cbor_major_type_uint64, cbor_major_type_simple_value])
      | bytes form payload payloadSize =>
        have bytes : input.val = (RegistrationLooseArgument.bytes cbor_major_type_byte_string form ++ payload.val) ++ atomsBytes rest := by
          simpa only [atomsBytes, atomBytes, cbor_major_type_byte_string] using contents
        obtain ⟨item, tail, _, children⟩ := bytes_item input payload form payloadSize (atomsBytes rest) bytes
        refine ⟨item, tail, children, ?_⟩
        exact RegistrationLooseOptimal.optimal_form input _ form (payload.val ++ atomsBytes rest)
          (by simpa only [List.append_assoc] using bytes)
          (by simp [cbor_major_type_byte_string]) (by simp [cbor_major_type_byte_string, cbor_major_type_simple_value])
    obtain ⟨item, tail, children, checked⟩ := makeItem
    cases status : atomMinimal atom with
    | false =>
      rw [status] at checked
      rw [RegistrationCanonicalTrace.loop_zero_unfold, running, body_false input count checked]
      simp only [bind_tc_ok, stopped, List.all_cons, status, Bool.false_and]
    | true =>
      rw [status] at checked
      rw [RegistrationCanonicalTrace.loop_zero_unfold, running, body_true input item count checked]
      simp only [bind_tc_ok, List.all_cons, status, Bool.true_and]
      apply ih item.tail (nextCount count item.children) tail
      rw [children, RegistrationCanonicalTrace.next_leaf_value count positive]
      simp only [List.length_cons] at size
      omega

set_option backward.isDefEq.respectTransparency false in
theorem scan (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = RegistrationHeaderCanonical.encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_0 input = .ok (atoms.all atomMinimal) := by
  obtain ⟨original, tail, _, children⟩ := RegistrationCanonicalItems.array_item input 8#u64 (atomsBytes atoms) contents
  let item := fromCanonical original
  simp only [extraction_canonical_scan_0, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte]
  rw [RegistrationCanonicalTrace.loop_zero_unfold]
  simp only [show decide (1#usize > 0#usize) = true from rfl]
  rw [body_true input item 1#usize original.optimal]
  simp only [bind_tc_ok]
  change (do let result ← extraction_canonical_scan_0_loop (pack (nextCount 1#usize original.children))
               (pack true) original.tail (decide (nextCount 1#usize original.children > 0#usize))
             Array.index_usize result 0#usize) = _
  rw [children, RegistrationCanonicalTrace.next_initial]
  rw [flat atoms original.tail (UScalar.cast .Usize 8#u64) tail (by
    rw [RegistrationHeaderCanonical.cast_value .Usize 8#u64 (by scalar_tac), size]; rfl)]
  simp only [bind_tc_ok, index_pack]

set_option backward.isDefEq.respectTransparency false in
theorem scan6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = RegistrationHeaderCanonical.encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_0 input = .ok (atoms.all atomMinimal) := by
  obtain ⟨original, tail, _, children⟩ := RegistrationCanonicalItems.array_item input 6#u64 (atomsBytes atoms) contents
  let item := fromCanonical original
  simp only [extraction_canonical_scan_0, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte]
  rw [RegistrationCanonicalTrace.loop_zero_unfold]
  simp only [show decide (1#usize > 0#usize) = true from rfl]
  rw [body_true input item 1#usize original.optimal]
  simp only [bind_tc_ok]
  change (do let result ← extraction_canonical_scan_0_loop (pack (nextCount 1#usize original.children))
               (pack true) original.tail (decide (nextCount 1#usize original.children > 0#usize))
             Array.index_usize result 0#usize) = _
  rw [children, RegistrationCanonicalTrace.next_initial]
  rw [flat atoms original.tail (UScalar.cast .Usize 6#u64) tail (by
    rw [RegistrationHeaderCanonical.cast_value .Usize 6#u64 (by scalar_tac), size]; rfl)]
  simp only [bind_tc_ok, index_pack]

def canonicalAtom : Atom → RegistrationCanonicalTrace.Atom
  | .uint form => .uint (RegistrationLooseArgument.value form)
  | .bytes _ payload _ => .bytes payload

omit [RegistrationValidatorPrimitive.Operations] in
theorem atom_canonical (atom : Atom) (accepted : atomMinimal atom = true) :
    atomBytes atom = RegistrationCanonicalTrace.atomBytes (canonicalAtom atom) := by
  cases atom with
  | uint form =>
    simpa only [atomBytes, canonicalAtom, RegistrationCanonicalTrace.atomBytes, cbor_major_type_uint64] using
      RegistrationLooseOptimal.canonical_bytes 0#u8 form accepted
  | bytes form payload size =>
    change RegistrationLooseArgument.bytes 2#u8 form ++ payload.val =
      RegistrationHeaderCanonical.encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val
    rw [RegistrationLooseOptimal.canonical_bytes 2#u8 form accepted, size, cbor_major_type_byte_string]

omit [RegistrationValidatorPrimitive.Operations] in
theorem atoms_canonical (atoms : List Atom) (accepted : atoms.all atomMinimal = true) :
    atomsBytes atoms = RegistrationCanonicalTrace.atomsBytes (atoms.map canonicalAtom) := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
    have pass : atomMinimal atom = true ∧ rest.all atomMinimal = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using accepted
    simp only [atomsBytes, List.map_cons, RegistrationCanonicalTrace.atomsBytes]
    rw [atom_canonical atom pass.1, ih pass.2]

end BeaconcryptCore.Refinement.RegistrationLooseWidthTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.body_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.body_true

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.body_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.body_false

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.stopped

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.flat

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.scan

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.atom_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.atom_canonical

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.atoms_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.atoms_canonical

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.scan6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseWidthTrace.scan6
