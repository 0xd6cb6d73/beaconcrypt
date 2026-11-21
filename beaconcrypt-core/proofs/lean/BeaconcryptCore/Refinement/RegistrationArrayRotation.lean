-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationArrayIndex
import BeaconcryptCore.Refinement.RegistrationHeaderWrite
import BeaconcryptCore.Refinement.PqxdhBytes
import BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
import BeaconcryptCore.Refinement.RegistrationArrayRotationList

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true

/-! Exact terminating evaluation and byte effects of the original extracted one-byte array-prefix rotation. The natural induction retains the source loop body, bounded indexed reads and writes, wrapping counter calls and returned mutable slice. The final list equation is derived from the actual source execution; it is not a serializer, parser or native-wire assumption. -/

namespace BeaconcryptCore.Refinement.RegistrationArrayRotation
open beaconcrypt_parse.cbordetveraux
open RegistrationCodecArraySingleton (pack index_pack update_pack)

theorem sub_zero (value : Usize) : Usize.wrapping_sub value 0#usize = value := by
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_sub_val_eq, show (0#usize).val = 0 from rfl,
    Nat.sub_zero, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt value.hSize

theorem sub_val (left right : Usize) (bound : right.val ≤ left.val) :
    (Usize.wrapping_sub left right).val = left.val - right.val := by
  rw [Usize.wrapping_sub_val_eq]
  have rightLimit := right.hSize
  have leftLimit := left.hSize
  rw [show left.val + (UScalar.size .Usize - right.val) =
    (left.val - right.val) + UScalar.size .Usize by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem index_predecessor (index length offset : Usize)
    (consecutive : length.val = offset.val + 1) (positive : 0 < index.val) :
    extraction_rotation_index_1 index length offset =
      .ok (Usize.wrapping_sub index 1#usize) := by
  have remaining : Usize.wrapping_sub length offset = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [sub_val length offset (by omega)]
    change length.val - offset.val = 1
    omega
  simp only [extraction_rotation_index_1, RegistrationArrayIndex.wrapping_sub,
    RegistrationArrayIndex.wrapping_add, bind_tc_ok, sub_zero, remaining]
  rw [ite_eq_left (by scalar_tac)]

theorem add_val (left right : Usize)
    (bound : left.val + right.val < UScalar.size .Usize) :
    (Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt bound]

theorem slice_index (input : Slice U8) (index : Usize) (inside : index.val < input.length) :
    Slice.index_usize input index = .ok input.val[index.val]! := by
  simp [Slice.index_usize, List.getElem?_eq_getElem inside,
    getElem!_pos input.val index.val inside]

theorem inner_body_step (before : Slice U8) (offset rounds position index : Usize)
    (length : before.length = offset.val + 1) (positive : 0 < index.val)
    (inside : index.val < before.length) :
    extraction_rotation_inner_1_loop.body offset rounds before (pack position) (pack index) true =
      .ok (.cont (before.set index before.val[(Usize.wrapping_sub index 1#usize).val]!,
        pack (Usize.wrapping_add position 1#usize), pack (Usize.wrapping_sub index 1#usize),
        decide (Usize.wrapping_add position 1#usize < Usize.wrapping_sub rounds 1#usize))) := by
  have previous : (Usize.wrapping_sub index 1#usize).val < before.length := by
    rw [sub_val index 1#usize (by scalar_tac)]
    change index.val - 1 < before.length
    omega
  simp only [extraction_rotation_inner_1_loop.body, ↓reduceIte, index_pack,
    RegistrationArrayIndex.slice_len,
    index_predecessor index before.len offset (by simpa only [Slice.len_val] using length) positive,
    bind_tc_ok, slice_index _ _ previous, RegistrationArrayIndex.wrapping_add,
    RegistrationHeaderWrite.update_set _ _ _ inside, update_pack,
    RegistrationArrayIndex.wrapping_sub]

private theorem inner_unfold (before : Slice U8) (offset rounds : Usize)
    (position index : Array Usize 1#usize) (condition : Bool) :
    extraction_rotation_inner_1_loop before offset rounds position index condition =
      (extraction_rotation_inner_1_loop.body offset rounds before position index condition >>= fun result =>
        match result with
        | .cont (next, nextPosition, nextIndex, nextCondition) =>
          extraction_rotation_inner_1_loop next offset rounds nextPosition nextIndex nextCondition
        | .done result => .ok result) := by
  unfold extraction_rotation_inner_1_loop
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

theorem descending (remaining : Nat) :
    ∀ (before : Slice U8) (offset rounds position index : Usize),
      before.length = offset.val + 1 → rounds.val = before.length → 0 < position.val →
      index.val = remaining + 1 → position.val + index.val = rounds.val →
      ∃ after, extraction_rotation_inner_1_loop before offset rounds (pack position) (pack index)
          (decide (1 < index.val)) = .ok (after, pack 1#usize) ∧
        after.length = before.length ∧
        ∀ k, after.val[k]? =
          if 2 ≤ k ∧ k ≤ index.val then before.val[k - 1]? else before.val[k]? := by
  induction remaining with
  | zero =>
    intro before offset rounds position index length count positionPositive atIndex balance
    have one : index = 1#usize := by
      apply UScalar.eq_of_val_eq
      change index.val = 1
      omega
    refine ⟨before, ?_, rfl, ?_⟩
    · rw [inner_unfold]
      simp only [one, show (1#usize).val = 1 from rfl, Nat.lt_irrefl,
        decide_false, extraction_rotation_inner_1_loop.body, Bool.false_eq_true,
        ↓reduceIte, bind_tc_ok]
    · intro k
      rw [ite_eq_right (by omega)]
  | succ remaining ih =>
    intro before offset rounds position index length count positionPositive atIndex balance
    let next := Usize.wrapping_sub index 1#usize
    let nextPosition := Usize.wrapping_add position 1#usize
    have nextValue : next.val = remaining + 1 := by
      dsimp only [next]
      rw [sub_val index 1#usize (by scalar_tac)]
      change index.val - 1 = remaining + 1
      omega
    have nextPositionValue : nextPosition.val = position.val + 1 := by
      dsimp only [nextPosition]
      rw [add_val position 1#usize (by have limit := rounds.hSize; change position.val + 1 < _; omega)]
      rfl
    have inside : index.val < before.length := by omega
    let changed := before.set index before.val[next.val]!
    have changedLength : changed.length = before.length := Slice.set_length _ _ _
    obtain ⟨after, actual, afterLength, post⟩ := ih changed offset rounds nextPosition next
      (changedLength.trans length) (count.trans changedLength.symm)
      (by omega) nextValue (by omega)
    refine ⟨after, ?_, afterLength.trans changedLength, ?_⟩
    · have nextCondition : decide (nextPosition < Usize.wrapping_sub rounds 1#usize) =
          decide (1 < next.val) := by
        simp only [decide_eq_decide, UScalar.lt_equiv]
        rw [nextPositionValue, sub_val rounds 1#usize (by change 1 ≤ rounds.val; omega)]
        change position.val + 1 < rounds.val - 1 ↔ 1 < next.val
        omega
      have running : decide (1 < index.val) = true := by
        simp only [decide_eq_true_eq]
        omega
      have indexPositive : 0 < index.val := by omega
      rw [inner_unfold, running,
        inner_body_step before offset rounds position index length indexPositive inside]
      simp only [bind_tc_ok]
      change extraction_rotation_inner_1_loop changed offset rounds (pack nextPosition) (pack next)
        (decide (nextPosition < Usize.wrapping_sub rounds 1#usize)) = .ok (after, pack 1#usize)
      rw [nextCondition, actual]
    · intro k
      rw [post]
      simp only [changed, Slice.set_val_eq, List.getElem?_set]
      by_cases shifted : 2 ≤ k ∧ k ≤ next.val
      · rw [ite_eq_left shifted, ite_eq_right (by omega), ite_eq_left (by omega)]
      · by_cases top : index.val = k
        · rw [ite_eq_right shifted, ite_eq_left top, ite_eq_left inside,
            ite_eq_left (by omega), show k - 1 = next.val by omega]
          have previousInside : next.val < before.val.length := by
            change next.val < before.length
            omega
          simp only [List.getElem?_eq_getElem previousInside,
            getElem!_pos before.val next.val previousInside]
        · rw [ite_eq_right shifted, ite_eq_right top, ite_eq_right (by omega)]

theorem add_zero (value : Usize) : Usize.wrapping_add 0#usize value = value := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_add_val_eq]
  change (0 + value.val) % UScalar.size .Usize = value.val
  rw [Nat.zero_add, Nat.mod_eq_of_lt value.hSize]

theorem index_zero (length offset : Usize) (consecutive : length.val = offset.val + 1) :
    extraction_rotation_index_1 0#usize length offset = .ok offset := by
  have remaining : Usize.wrapping_sub length offset = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [sub_val length offset (by omega)]
    change length.val - offset.val = 1
    omega
  simp only [extraction_rotation_index_1, RegistrationArrayIndex.wrapping_sub,
    RegistrationArrayIndex.wrapping_add, bind_tc_ok, sub_zero, remaining]
  rw [ite_eq_right (by scalar_tac), add_zero]

theorem inner_body_first (before : Slice U8) (offset rounds : Usize)
    (length : before.length = offset.val + 1) :
    extraction_rotation_inner_1_loop.body offset rounds before (pack 0#usize) (pack 0#usize) true =
      .ok (.cont (before.set 0#usize before.val[offset.val]!, pack 1#usize, pack offset,
        decide (1#usize < Usize.wrapping_sub rounds 1#usize))) := by
  have lastInside : offset.val < before.length := by omega
  have firstInside : (0#usize).val < before.length := by change 0 < _; omega
  simp only [extraction_rotation_inner_1_loop.body, ↓reduceIte, index_pack,
    RegistrationArrayIndex.slice_len,
    index_zero before.len offset (by simpa only [Slice.len_val] using length),
    bind_tc_ok, slice_index _ _ lastInside, RegistrationArrayIndex.wrapping_add,
    add_zero, RegistrationHeaderWrite.update_set _ _ _ firstInside, update_pack,
    RegistrationArrayIndex.wrapping_sub]

theorem inner (before : Slice U8) (offset : Usize)
    (length : before.length = offset.val + 1) (positive : 0 < offset.val) :
    ∃ after, extraction_rotation_inner_1 before 0#usize offset before.len = .ok (1#usize, after) ∧
      after.length = before.length ∧
      ∀ k, after.val[k]? = if k = 0 then before.val[offset.val]?
        else if 2 ≤ k ∧ k ≤ offset.val then before.val[k - 1]? else before.val[k]? := by
  let changed := before.set 0#usize before.val[offset.val]!
  have changedLength : changed.length = before.length := Slice.set_length _ _ _
  obtain ⟨after, actual, afterLength, post⟩ := descending (offset.val - 1) changed offset before.len
    1#usize offset (changedLength.trans length) (Slice.len_val before |>.trans changedLength.symm)
    (by change 0 < 1; omega) (by omega) (by simp only [Slice.len_val]; change 1 + offset.val = before.length; omega)
  refine ⟨after, ?_, afterLength.trans changedLength, ?_⟩
  · have rounds : Usize.wrapping_sub before.len 1#usize = offset := by
      apply UScalar.eq_of_val_eq
      rw [sub_val before.len 1#usize (by simp only [Slice.len_val]; change 1 ≤ before.length; omega)]
      change before.length - 1 = offset.val
      omega
    have running : decide (0#usize < offset) = true := by
      simp only [decide_eq_true_eq]
      scalar_tac
    simp only [extraction_rotation_inner_1,
      show Array.index_usize (Array.repeat 1#usize 0#usize) 0#usize = .ok 0#usize from rfl,
      RegistrationArrayIndex.wrapping_sub, bind_tc_ok, rounds, running]
    change (do
      let (middle, cell) ← extraction_rotation_inner_1_loop before offset before.len
        (pack 0#usize) (pack 0#usize) true
      let index ← Array.index_usize cell 0#usize
      .ok (index, middle)) = .ok (1#usize, after)
    rw [inner_unfold, inner_body_first before offset before.len length]
    simp only [bind_tc_ok, rounds]
    have condition : decide (1#usize < offset) = decide (1 < offset.val) := by
      simp only [UScalar.lt_equiv]
      rfl
    rw [condition, actual]
    simp only [bind_tc_ok, index_pack]
  · intro k
    rw [post]
    simp only [changed, Slice.set_val_eq, List.getElem?_set, show (0#usize).val = 0 from rfl]
    by_cases zero : k = 0
    · subst k
      have firstInside : 0 < before.val.length := by change 0 < before.length; omega
      have lastInside : offset.val < before.val.length := by change offset.val < before.length; omega
      rw [ite_eq_right (show ¬ (2 ≤ 0 ∧ 0 ≤ offset.val) from by omega),
        ite_eq_left rfl, ite_eq_left firstInside, ite_eq_left rfl]
      simp only [List.getElem?_eq_getElem lastInside, getElem!_pos before.val offset.val lastInside]
    · rw [ite_eq_right zero]
      by_cases shifted : 2 ≤ k ∧ k ≤ offset.val
      · rw [ite_eq_left shifted, ite_eq_right (by omega), ite_eq_left shifted]
      · rw [ite_eq_right shifted, ite_eq_right (by omega), ite_eq_right shifted]

private theorem outer_unfold (before : Slice U8) (offset cycles rounds : Usize)
    (position : Array Usize 1#usize) (condition : Bool) :
    extraction_serialize_array_loop1 offset before cycles rounds position condition =
      (extraction_serialize_array_loop1.body offset cycles rounds before position condition >>= fun result =>
        match result with
        | .cont (next, nextPosition, nextCondition) =>
          extraction_serialize_array_loop1 offset next cycles rounds nextPosition nextCondition
        | .done result => .ok result) := by
  unfold extraction_serialize_array_loop1
  rw [PqxdhRefinement.loop_unfold]
  congr 1
  funext result
  cases result <;> rfl

private theorem outer_stop (before : Slice U8) (offset cycles rounds : Usize)
    (position : Array Usize 1#usize) :
    extraction_serialize_array_loop1 offset before cycles rounds position false = .ok before := by
  rw [outer_unfold]
  rfl

theorem rotate_pointwise (before : Slice U8) (offset : Usize)
    (length : before.length = offset.val + 1) (positive : 0 < offset.val) :
    ∃ after, extraction_serialize_array_loop1 offset before 1#usize before.len (pack 0#usize) true =
        .ok after ∧ after.length = before.length ∧
      ∀ k, after.val[k]? = if k = 0 then before.val[offset.val]?
        else if 1 ≤ k ∧ k ≤ offset.val then before.val[k - 1]? else before.val[k]? := by
  obtain ⟨middle, actual, middleLength, post⟩ := inner before offset length positive
  let final := middle.set 1#usize before.val[0]!
  have firstInside : (0#usize).val < before.val.length := by change 0 < before.length; omega
  have middleInside : (1#usize).val < middle.val.length := by change 1 < middle.length; omega
  have body : extraction_serialize_array_loop1.body offset 1#usize before.len before (pack 0#usize) true =
      .ok (.cont (final, pack 1#usize, false)) := by
    simp only [extraction_serialize_array_loop1.body, ↓reduceIte, index_pack,
      slice_index _ _ firstInside, actual, bind_tc_ok,
      RegistrationArrayIndex.wrapping_add, add_zero, update_pack,
      show ¬ (1#usize < 1#usize) from by scalar_tac, decide_false]
    change (do
      let updated ← Slice.update middle 1#usize before.val[0]!
      .ok (ControlFlow.cont (updated, pack 1#usize, false))) =
        .ok (ControlFlow.cont (final, pack 1#usize, false))
    rw [RegistrationHeaderWrite.update_set _ _ _ middleInside]
    rfl
  refine ⟨final, ?_, (Slice.set_length _ _ _).trans middleLength, ?_⟩
  · rw [outer_unfold, body]
    simp only [bind_tc_ok]
    exact outer_stop final offset 1#usize before.len (pack 1#usize)
  · intro k
    simp only [final, Slice.set_val_eq, List.getElem?_set, show (1#usize).val = 1 from rfl]
    by_cases one : k = 1
    · subst k
      have middleNatInside : 1 < middle.val.length := by change 1 < middle.length; omega
      have firstNatInside : 0 < before.val.length := by change 0 < before.length; omega
      rw [ite_eq_left rfl, ite_eq_left middleNatInside,
        ite_eq_right (show ¬ (1 = 0) from by omega), ite_eq_left (by omega)]
      simp only [Nat.sub_self, List.getElem?_eq_getElem firstNatInside,
        getElem!_pos before.val 0 firstNatInside]
    · rw [ite_eq_right (by omega), post]
      by_cases zero : k = 0
      · rw [ite_eq_left zero, ite_eq_left zero]
      · rw [ite_eq_right zero, ite_eq_right zero]
        by_cases shifted : 2 ≤ k ∧ k ≤ offset.val
        · rw [ite_eq_left shifted, ite_eq_left (by omega)]
        · rw [ite_eq_right shifted, ite_eq_right (by omega)]

theorem rotate_one (before : Slice U8) (offset : Usize)
    (length : before.length = offset.val + 1) (positive : 0 < offset.val) :
    ∃ after, extraction_serialize_array_loop1 offset before 1#usize before.len (pack 0#usize) true =
        .ok after ∧ after.length = before.length ∧
      after.val = before.val.drop offset.val ++ before.val.take offset.val := by
  obtain ⟨after, actual, afterLength, bytes⟩ := rotate_pointwise before offset length positive
  exact ⟨after, actual, afterLength,
    RegistrationArrayRotationList.right_rotation_eq before.val after.val offset.val length bytes⟩

end BeaconcryptCore.Refinement.RegistrationArrayRotation

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.sub_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.sub_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.sub_val' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.sub_val

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.index_predecessor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.index_predecessor

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.add_val' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.add_val

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.slice_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.slice_index

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.inner_body_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.inner_body_step

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.descending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.descending

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.add_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.add_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.index_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.index_zero

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.inner_body_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.inner_body_first

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.inner

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.rotate_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.rotate_pointwise

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotation.rotate_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotation.rotate_one
