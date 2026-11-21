-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCanonicalItems
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Finite source-call traces prove termination of both actual canonical-validation loops. Every array with eight canonical UInt64/byte-string atoms is covered, including arbitrary byte-string payloads and U64 values. The constructors discharge all item checks from source bytes; no canonical-parser acceptance law is a premise. Structural validation and schema readback remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationCanonicalTrace
open beaconcrypt_parse.cbordetveraux
open RegistrationHeaderCanonical RegistrationCanonicalItems RegistrationFlatSkip RegistrationCodecArraySingleton
variable [RegistrationValidatorPrimitive.Operations]

inductive Trace : Usize → Slice U8 → Prop where
| stop (input : Slice U8) : Trace 0#usize input
| step {input : Slice U8} {count : Usize} (item : Item input) (positive : 0 < count.val)
    (later : Trace (nextCount count item.children) item.tail) : Trace count input

omit [RegistrationValidatorPrimitive.Operations] in
theorem loop_zero_unfold (input : Slice U8) (count : Array Usize 1#usize)
    (success : Array Bool 1#usize) (condition : Bool) :
    extraction_canonical_scan_0_loop count success input condition =
      (extraction_canonical_scan_0_loop.body count success input condition >>= fun result =>
        match result with
        | .cont (countNext, successNext, inputNext, conditionNext) =>
          extraction_canonical_scan_0_loop countNext successNext inputNext conditionNext
        | .done result => .ok result) := by
  unfold extraction_canonical_scan_0_loop
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

theorem loop_one_unfold (input : Slice U8) (count : Array Usize 1#usize)
    (success : Array Bool 1#usize) (condition : Bool) :
    extraction_canonical_scan_1_loop count success input condition =
      (extraction_canonical_scan_1_loop.body count success input condition >>= fun result =>
        match result with
        | .cont (countNext, successNext, inputNext, conditionNext) =>
          extraction_canonical_scan_1_loop countNext successNext inputNext conditionNext
        | .done result => .ok result) := by
  unfold extraction_canonical_scan_1_loop
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem run_zero {input : Slice U8} {count : Usize} (trace : Trace count input) :
    extraction_canonical_scan_0_loop (pack count) (pack true) input
      (decide (count > 0#usize)) = .ok (pack true) := by
  induction trace with
  | stop input =>
    rw [loop_zero_unfold]
    simp [extraction_canonical_scan_0_loop.body, bind_tc_ok]
  | @step input count item positive later ih =>
    have running : decide (count > 0#usize) = true := by
      simp only [decide_eq_true_eq, UScalar.lt_equiv]
      exact positive
    rw [loop_zero_unfold, running, body_zero input item count]
    simp only [bind_tc_ok]
    exact ih

set_option backward.isDefEq.respectTransparency false in
theorem run_one {input : Slice U8} {count : Usize} (trace : Trace count input) :
    extraction_canonical_scan_1_loop (pack count) (pack true) input
      (decide (count > 0#usize)) = .ok (pack true) := by
  induction trace with
  | stop input =>
    rw [loop_one_unfold]
    simp [extraction_canonical_scan_1_loop.body, bind_tc_ok]
  | @step input count item positive later ih =>
    have running : decide (count > 0#usize) = true := by
      simp only [decide_eq_true_eq, UScalar.lt_equiv]
      exact positive
    rw [loop_one_unfold, running, body_one input item count]
    simp only [bind_tc_ok]
    exact ih

inductive Atom where
| uint : U64 → Atom
| bytes : Slice U8 → Atom

def atomBytes : Atom → List U8
| .uint value => encodedBytes cbor_major_type_uint64 value
| .bytes value => encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 value.len) ++ value.val

def atomsBytes : List Atom → List U8
| [] => []
| item :: rest => atomBytes item ++ atomsBytes rest

omit [RegistrationValidatorPrimitive.Operations] in
theorem next_leaf_value (count : Usize) (positive : 0 < count.val) :
    (nextCount count 0#usize).val = count.val - 1 := by
  unfold nextCount
  rw [Usize.wrapping_add_val_eq, RegistrationHeaderSize.sub_value count 1#usize (by scalar_tac)]
  change (count.val - 1 + 0) % UScalar.size .Usize = count.val - 1
  rw [Nat.add_zero, Nat.mod_eq_of_lt (by have bound := count.hBounds; rw [← UScalar.size_def] at bound; omega)]

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
      | uint value =>
        obtain ⟨item, tail, _, children⟩ := uint_item input value (atomsBytes rest) contents
        exact ⟨item, tail, children⟩
      | bytes value =>
        obtain ⟨item, tail, _, children⟩ := bytes_item input value (atomsBytes rest) contents
        exact ⟨item, tail, children⟩
    obtain ⟨item, tail, children⟩ := makeItem
    apply Trace.step item positive
    apply ih item.tail (nextCount count item.children) tail
    rw [children, next_leaf_value count positive]
    simp only [List.length_cons] at size
    omega

omit [RegistrationValidatorPrimitive.Operations] in
theorem next_initial (children : Usize) : nextCount 1#usize children = children := by
  have sub11 : Usize.wrapping_sub 1#usize 1#usize = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [RegistrationHeaderSize.sub_value _ _ (by scalar_tac)]
    rfl
  simp only [nextCount, sub11, RegistrationArrayRotation.add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem array8_trace (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    Trace 1#usize input := by
  obtain ⟨item, tail, _, children⟩ := array_item input 8#u64 (atomsBytes atoms) contents
  apply Trace.step item (by scalar_tac)
  rw [children, next_initial]
  apply flat_trace atoms item.tail (UScalar.cast .Usize 8#u64) tail
  rw [RegistrationHeaderCanonical.cast_value .Usize 8#u64 (by scalar_tac), size]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem scans (input : Slice U8) (atoms : List Atom) (size : atoms.length = 8)
    (contents : input.val = encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_0 input = .ok true ∧ extraction_canonical_scan_1 input = .ok true := by
  have trace := array8_trace input atoms size contents
  constructor
  · simp only [extraction_canonical_scan_0, show Array.repeat 1#usize = @pack Usize from rfl,
      show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
      run_zero trace]
  · simp only [extraction_canonical_scan_1, show Array.repeat 1#usize = @pack Usize from rfl,
      show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
      run_one trace]
set_option backward.isDefEq.respectTransparency false in
theorem array6_trace (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    Trace 1#usize input := by
  obtain ⟨item, tail, _, children⟩ := array_item input 6#u64 (atomsBytes atoms) contents
  apply Trace.step item (by scalar_tac)
  rw [children, next_initial]
  apply flat_trace atoms item.tail (UScalar.cast .Usize 6#u64) tail
  rw [RegistrationHeaderCanonical.cast_value .Usize 6#u64 (by scalar_tac), size]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem scans6 (input : Slice U8) (atoms : List Atom) (size : atoms.length = 6)
    (contents : input.val = encodedBytes cbor_major_type_array 6#u64 ++ atomsBytes atoms) :
    extraction_canonical_scan_0 input = .ok true ∧ extraction_canonical_scan_1 input = .ok true := by
  have trace := array6_trace input atoms size contents
  constructor
  · simp only [extraction_canonical_scan_0, show Array.repeat 1#usize = @pack Usize from rfl,
      show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
      run_zero trace]
  · simp only [extraction_canonical_scan_1, show Array.repeat 1#usize = @pack Usize from rfl,
      show Array.repeat 1#usize = @pack Bool from rfl, index_pack, bind_tc_ok, ↓reduceIte,
      run_one trace]
end BeaconcryptCore.Refinement.RegistrationCanonicalTrace

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.loop_zero_unfold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.loop_zero_unfold

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.loop_one_unfold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.loop_one_unfold

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.run_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.run_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.run_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.run_one

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.next_leaf_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.next_leaf_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.flat_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.flat_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.next_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.next_initial

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.array8_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.array8_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.scans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.scans

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.array6_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.array6_trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalTrace.scans6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalTrace.scans6
