-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.PqxdhBytes

/-!
Exact interpretation and unconditional totality of byte-slice equality. The proof follows the actual range iterator and Boolean accumulator used by the extracted CoreModels implementation, including the remainder of the iterator after a mismatch.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RegistrationBytePrimitives

private theorem range_next_stop (start finish : Std.Usize) (h : finish.val ≤ start.val) :
    core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      core.Usize.Insts.CoreIterRangeStep { start, «end» := finish } =
      ok (.none, { start, «end» := finish }) := by
  simp [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next,
    core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
    Nat.compare_eq_ite_lt, Nat.not_lt.mpr h]
  split_ifs <;> simp_all

private theorem range_next_step (start finish : Std.Usize) (h : start.val < finish.val) :
    ∃ next : Std.Usize, next.val = start.val + 1 ∧
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        core.Usize.Insts.CoreIterRangeStep { start, «end» := finish } =
        ok (.some start, { start := next, «end» := finish }) := by
  have bound : start.val + 1 ≤ UScalar.max .Usize := by scalar_tac
  have overflow : (UScalar.overflowing_add start 1#usize).1.val = start.val + 1 ∧
      (UScalar.overflowing_add start 1#usize).2 = false := by
    simpa [usize_val_1, Nat.not_lt.mpr bound] using UScalar.overflowing_add_eq start 1#usize
  refine ⟨(UScalar.overflowing_add start 1#usize).1, overflow.1, ?_⟩
  simp [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next,
    core.IteratorRange.next, core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
    Nat.compare_eq_ite_lt, h, core.Usize.Insts.CoreCloneClone.clone,
    core.Usize.Insts.CoreIterRangeStep.forward_checked,
    core.convert.TryFromUTInfallible.Blanket.try_from,
    core.convert.From.Blanket.from, core.num.Usize.checked_add, core.num.Usize.overflowing_add,
    rust_primitives.arithmetic.overflowing_add_usize]
  cases step : UScalar.overflowing_add start 1#usize; simp_all

private theorem eq_loop_unfold (left right : Slice Std.U8)
    (iter : core.ops.range.Range Std.Usize) (result : Bool) :
    core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop core.U8.Insts.CoreCmpPartialEqU8
      iter left right result = (do
        let step ← core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop.body
          core.U8.Insts.CoreCmpPartialEqU8 left right iter result
        match step with
        | .cont state =>
            core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop
              core.U8.Insts.CoreCmpPartialEqU8 state.1 left right state.2
        | .done value => ok value) := by
  unfold core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop
  rw [loop_unfold]
  simp only [Prod.eta]
  congr 1
  funext step
  cases step <;> rfl

private theorem slice_index_exact (bytes : Slice Std.U8) (index : Std.Usize)
    (inside : index.val < bytes.val.length) :
    Slice.index_usize bytes index = ok bytes.val[index.val]! := by
  simp [Slice.index_usize, List.getElem?_eq_getElem inside,
    getElem!_pos bytes.val index.val inside]

private theorem slice_eq_loop_aux (left right : Slice Std.U8)
    (same : left.val.length = right.val.length) (remaining : Nat) :
    ∀ index : Std.Usize, index.val + remaining = left.val.length → ∀ result : Bool,
      core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop core.U8.Insts.CoreCmpPartialEqU8
        { start := index, «end» := Slice.len left } left right result =
        ok (result && decide (∀ position, index.val ≤ position → position < left.val.length →
          left.val[position]! = right.val[position]!)) := by
  induction remaining with
  | zero =>
    intro index count result
    rw [eq_loop_unfold]
    simp only [core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop.body,
      range_next_stop index (Slice.len left) (by simp only [Slice.len_val, Slice.length]; omega),
      bind_tc_ok]
    dsimp! only
    simp only [bind_tc_ok]
    have vacuous : ∀ position, index.val ≤ position → position < left.val.length →
        left.val[position]! = right.val[position]! := by grind
    simpa only [Bool.and_true] using
      congrArg (fun value : Bool => (ok (result && value) : RustM Bool))
        (decide_eq_true_eq.mpr vacuous).symm
  | succ remaining ih =>
    intro index count result
    obtain ⟨next, advance, request⟩ := range_next_step index (Slice.len left)
      (by simp only [Slice.len_val, Slice.length]; omega)
    rw [eq_loop_unfold]
    simp only [core.Slice.Insts.CoreCmpPartialEqSlice.eq_loop.body, request, bind_tc_ok]
    dsimp! only
    have rest : next.val + remaining = left.val.length := by omega
    cases result with
    | false =>
      simp only [Bool.false_eq_true, ite_false, bind_tc_ok, Bool.false_and]
      simpa only [Bool.false_and] using ih next rest false
    | true =>
      simp only [ite_true, slice_index_exact left index (by omega),
        slice_index_exact right index (by omega), bind_tc_ok,
        core.U8.Insts.CoreCmpPartialEqU8, Bool.true_and]
      by_cases head : left.val[index.val]! = right.val[index.val]!
      · simp only [head, beq_self_eq_true, ite_true, bind_tc_ok]
        erw [ih next rest true]
        congr 1
        simp only [Bool.true_and, decide_eq_decide]
        constructor <;> intro all position lower upper
        · grind
        · exact all position (by omega) upper
      · have unequal : (left.val[index.val]! == right.val[index.val]!) = false := by
          simpa using head
        simp only [unequal, Bool.false_eq_true, ite_false, bind_tc_ok]
        erw [ih next rest false]
        have mismatch : ¬ (∀ position, index.val ≤ position → position < left.val.length →
            left.val[position]! = right.val[position]!) := by grind
        simpa only [Bool.false_and] using
          congrArg (fun value : Bool => (ok value : RustM Bool))
            (decide_eq_false_iff_not.mpr mismatch).symm

/-- The actual extracted byte-slice comparison always terminates and decides list equality. -/
theorem slice_eq_exact (left right : Slice Std.U8) :
    core.Slice.Insts.CoreCmpPartialEqSlice.eq core.U8.Insts.CoreCmpPartialEqU8 left right =
      ok (decide (left.val = right.val)) := by
  unfold core.Slice.Insts.CoreCmpPartialEqSlice.eq
  simp only [core.slice.Slice.len, rust_primitives.slice.slice_length, bind_tc_ok]
  by_cases same : left.val.length = right.val.length
  · have scalar_same : Slice.len left = Slice.len right := by
      simpa only [UScalar.eq_equiv, Slice.len_val, Slice.length] using same
    simp only [show (Slice.len left != Slice.len right) = false from by simp [scalar_same],
      Bool.false_eq_true, ite_false]
    rw [slice_eq_loop_aux left right same left.val.length 0#usize (by simp) true]
    congr 1
    simp only [Bool.true_and, decide_eq_decide]
    constructor
    · exact fun all => List.ext_getElem same (fun position left_bound right_bound =>
        (getElem!_pos left.val position left_bound).symm.trans
          ((all position (by simp) left_bound).trans
            (getElem!_pos right.val position right_bound)))
    · exact fun equality position _ _ => congrArg (fun bytes : List Std.U8 => bytes[position]!) equality
  · have scalar_ne : Slice.len left ≠ Slice.len right := by
      simpa only [ne_eq, UScalar.eq_equiv, Slice.len_val, Slice.length] using same
    have list_ne : left.val ≠ right.val := fun equality => same (congrArg List.length equality)
    simpa only [show (Slice.len left != Slice.len right) = true from by simp [scalar_ne],
      ite_true] using congrArg (fun value : Bool => (ok value : RustM Bool))
        (decide_eq_false_iff_not.mpr list_ne).symm

/-- Every well-typed byte slice comparison returns a Boolean; no loop or primitive assumption is needed. -/
theorem slice_eq_total (left right : Slice Std.U8) :
    ∃ result, core.Slice.Insts.CoreCmpPartialEqSlice.eq core.U8.Insts.CoreCmpPartialEqU8
      left right = ok result :=
  ⟨_, slice_eq_exact left right⟩

/-- Inequality uses the same total comparison and returns its exact Boolean complement. -/
theorem slice_ne_exact (left right : Slice Std.U8) :
    core.Slice.Insts.CoreCmpPartialEqSlice.ne core.U8.Insts.CoreCmpPartialEqU8 left right =
      ok (decide (left.val ≠ right.val)) := by
  simp only [core.Slice.Insts.CoreCmpPartialEqSlice.ne, slice_eq_exact, bind_tc_ok]
  simp only [decide_eq_false_iff_not, ne_eq]

/-- Optional borrowed slices retain their complete byte lists when present. -/
def optionalSliceValues : core.option.Option (Slice Std.U8) → Option (List Std.U8)
  | .None => none
  | .Some bytes => some bytes.val

/-- The actual optional-slice inequality decides exact presence and byte equality. -/
theorem optional_slice_ne_exact (left right : core.option.Option (Slice Std.U8)) :
    core.cmp.PartialEq.ne.default
      (core.option.Option.Insts.CoreCmpPartialEqOption
        (core.Shared1A.Insts.CoreCmpPartialEqShared0B
          (core.Slice.Insts.CoreCmpPartialEqSlice core.U8.Insts.CoreCmpPartialEqU8))) left right =
      ok (decide (optionalSliceValues left ≠ optionalSliceValues right)) := by
  cases left
  all_goals cases right
  all_goals simp [core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.Shared1A.Insts.CoreCmpPartialEqShared0B,
    core.Slice.Insts.CoreCmpPartialEqSlice, slice_eq_exact, optionalSliceValues]

end BeaconcryptCore.Refinement.RegistrationBytePrimitives

/-- info: 'BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_eq_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_eq_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_eq_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_eq_total
/-- info: 'BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_ne_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBytePrimitives.slice_ne_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationBytePrimitives.optional_slice_ne_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBytePrimitives.optional_slice_ne_exact
