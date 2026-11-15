-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseOrderItems
import BeaconcryptCore.Refinement.RegistrationLooseFieldSpan
import BeaconcryptCore.Refinement.RegistrationCanonicalTrace
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationLooseOrderTrace
open beaconcrypt_parse.cbordetveraux RegistrationCodecArraySingleton
open RegistrationLooseOrderItems
open RegistrationCanonicalItems (nextCount)
open RegistrationLooseFieldSpan (Atom atomBytes atomsBytes)
open RegistrationHeaderCanonical
variable [RegistrationValidatorPrimitive.Operations]
inductive Trace : Usize → Slice U8 → Prop where
| stop (input : Slice U8) : Trace 0#usize input
| step {input : Slice U8} {count : Usize} (item : Item input) (positive : 0 < count.val)
    (later : Trace (nextCount count item.children) item.tail) : Trace count input

set_option backward.isDefEq.respectTransparency false in
theorem run_one {input : Slice U8} {count : Usize} (trace : Trace count input) :
    extraction_canonical_scan_1_loop (pack count) (pack true) input
      (decide (count > 0#usize)) = .ok (pack true) := by
  induction trace with
  | stop input =>
    rw [RegistrationCanonicalTrace.loop_one_unfold]
    simp [extraction_canonical_scan_1_loop.body, bind_tc_ok]
  | @step input count item positive later ih =>
    have running : decide (count > 0#usize) = true := by
      simp only [decide_eq_true_eq, UScalar.lt_equiv]
      exact positive
    rw [RegistrationCanonicalTrace.loop_one_unfold, running, body_one input item count]
    simp only [bind_tc_ok]
    exact ih

set_option backward.isDefEq.respectTransparency false in
theorem flat_trace (atoms : List Atom) :
    ∀ (input : Slice U8) (count : Usize), input.val = atomsBytes atoms → count.val = atoms.length → Trace count input := by
  induction atoms with
  | nil =>
    intro input count _ size
    have countZero : count = 0#usize := by apply UScalar.eq_of_val_eq; simpa using size
    rw [countZero]
    exact Trace.stop input
  | cons atom rest ih =>
    intro input count contents size
    have positive : 0 < count.val := by simp only [List.length_cons] at size; omega
    have makeItem : ∃ item : Item input, item.tail.val = atomsBytes rest ∧ item.children = 0#usize := by
      cases atom with
      | uint form =>
        obtain ⟨item, tail, _, children⟩ := uint_item input form (atomsBytes rest) (by simpa only [atomsBytes, atomBytes, cbor_major_type_uint64, cbor_major_type_byte_string] using contents)
        exact ⟨item, tail, children⟩
      | bytes form payload payloadSize =>
        obtain ⟨item, tail, _, children⟩ := bytes_item input payload form payloadSize (atomsBytes rest) (by simpa only [atomsBytes, atomBytes, cbor_major_type_uint64, cbor_major_type_byte_string] using contents)
        exact ⟨item, tail, children⟩
    obtain ⟨item, tail, children⟩ := makeItem
    apply Trace.step item positive
    apply ih item.tail (nextCount count item.children) tail
    rw [children, RegistrationCanonicalTrace.next_leaf_value count positive]
    simp only [List.length_cons] at size
    omega

set_option backward.isDefEq.respectTransparency false in
theorem array8_trace (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    Trace 1#usize input := by
  obtain ⟨original, tail, _, children⟩ := RegistrationCanonicalItems.array_item input 8#u64 (atomsBytes atoms) contents
  let item := fromCanonical original
  apply Trace.step item (by scalar_tac)
  change Trace (nextCount 1#usize original.children) original.tail
  rw [children, RegistrationCanonicalTrace.next_initial]
  apply flat_trace atoms original.tail (UScalar.cast .Usize 8#u64) tail
  rw [RegistrationHeaderCanonical.cast_value .Usize 8#u64 (by scalar_tac), size]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem scan (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_1 input = .ok true := by
  have trace := array8_trace input atoms size contents
  simp only [extraction_canonical_scan_1, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte, run_one trace]
set_option backward.isDefEq.respectTransparency false in
theorem array6_trace (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    Trace 1#usize input := by
  obtain ⟨original, tail, _, children⟩ := RegistrationCanonicalItems.array_item input 6#u64 (atomsBytes atoms) contents
  let item := fromCanonical original
  apply Trace.step item (by scalar_tac)
  change Trace (nextCount 1#usize original.children) original.tail
  rw [children, RegistrationCanonicalTrace.next_initial]
  apply flat_trace atoms original.tail (UScalar.cast .Usize 6#u64) tail
  rw [RegistrationHeaderCanonical.cast_value .Usize 6#u64 (by scalar_tac), size]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem scan6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_1 input = .ok true := by
  have trace := array6_trace input atoms size contents
  simp only [extraction_canonical_scan_1, show Array.repeat 1#usize = @pack Usize from rfl,
    show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte, run_one trace]
end BeaconcryptCore.Refinement.RegistrationLooseOrderTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.run_one

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.flat_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.flat_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.array8_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.array8_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.scan

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.array6_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.array6_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.scan6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationLooseOrderTrace.scan6
