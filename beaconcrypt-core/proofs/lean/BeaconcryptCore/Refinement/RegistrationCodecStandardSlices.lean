-- SPDX-License-Identifier: 0BSD
import Aeneas
import CoreModels

/-! Standard-library slice normalization for the extracted handwritten preflight. Checked splitting preserves the exact adjacent parts, rejects out-of-bounds positions, and agrees with the existing CoreModels implementation. Copying a split-first byte is equivalent to guarded indexing and splitting. The source preparer records the exact pinned Rust standard-library bodies; no parser law is assumed. -/

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.RegistrationCodecStandardSlices
open Aeneas.Std
variable {T : Type}

/-- The standard checked split returns the exact two adjacent subslices, or `none`. -/
def checkedSplit (input : Slice T) (mid : Usize) : RustM (Option (Slice T × Slice T)) :=
  if mid ≤ input.length then
    let left := (input.val.splitAt mid.val).fst
    let right := (input.val.splitAt mid.val).snd
    let left : Slice T := ⟨left, by
      have := List.splitAt_length mid.val input.val
      have := input.property
      simp +zetaDelta at *
      omega⟩
    let right : Slice T := ⟨right, by
      have := List.splitAt_length mid.val input.val
      have := input.property
      simp +zetaDelta at *
      omega⟩
    .ok (some (left, right))
  else .ok none

theorem checked_split_lowering (input : Slice T) (mid : Usize) :
    checkedSplit input mid =
      (do
        if mid.val > input.val.length then
          .ok none
        else
          let pair ← Aeneas.Std.core.slice.Slice.split_at input mid
          .ok (some pair)) := by
  by_cases bound : mid.val ≤ input.val.length
  · simp [checkedSplit, Aeneas.Std.core.slice.Slice.split_at, bound, Nat.not_lt_of_ge bound]
  · simp [checkedSplit, bound, Nat.lt_of_not_ge bound]

theorem checked_split_rejected (input : Slice T) (mid : Usize)
    (bound : input.val.length < mid.val) : checkedSplit input mid = .ok none := by
  simp [checkedSplit, Nat.not_le_of_gt bound]

theorem checked_split_parts (input : Slice T) (mid : Usize)
    (bound : mid.val ≤ input.val.length) :
    ∃ left right, checkedSplit input mid = .ok (some (left, right)) ∧
      left.val.length = mid.val ∧ right.val.length = input.val.length - mid.val ∧
      left.val ++ right.val = input.val := by
  simp only [checkedSplit, bound, ite_true]
  refine ⟨_, _, rfl, ?_, ?_, ?_⟩
  all_goals simp [List.splitAt_eq, Nat.min_eq_left bound]

def copiedFirst (input : Slice T) : Option (T × Slice T) :=
  match same : input.val with
  | [] => none
  | value :: rest => some (value, ⟨rest, by
      have bound := input.property
      rw [same] at bound
      simp only [List.length_cons] at bound
      omega⟩)

theorem copied_first_lowering (input : Slice T) :
    RustM.ok (copiedFirst input) =
      (do
        if input.val.isEmpty then
          .ok none
        else
          let value ← Slice.index_usize input 0#usize
          let (_, tail) ← Aeneas.Std.core.slice.Slice.split_at input 1#usize
          .ok (some (value, tail))) := by
  rcases input with ⟨values, bound⟩
  cases values with
  | nil => rfl
  | cons value rest =>
      have index : Slice.index_usize (⟨value :: rest, bound⟩ : Slice T) 0#usize = .ok value := by
        change (match (value :: rest)[(0#usize).val]? with
          | none => RustM.fail .panic
          | some item => RustM.ok item) = RustM.ok value
        simp
      rw [index]
      simp [copiedFirst, Aeneas.Std.core.slice.Slice.split_at, List.splitAt_eq]
      rfl

def coreOptionToOption {A : Type} : CoreModels.core.option.Option A → Option A
  | .None => none
  | .Some value => some value

theorem checked_split_existing_model (input : Slice T) (mid : Usize) :
    (do
      let result ← CoreModels.core.slice.Slice.split_at_checked input mid
      .ok (coreOptionToOption result)) = checkedSplit input mid := by
  by_cases bound : mid.val ≤ input.val.length
  · simp [CoreModels.core.slice.Slice.split_at_checked, CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length, CoreModels.core.slice.Slice.split_at,
      CoreModels.rust_primitives.slice.slice_split_at, checkedSplit, bound,
      Aeneas.Std.core.slice.Slice.split_at, UScalar.le_equiv, coreOptionToOption]
    rfl
  · simp [CoreModels.core.slice.Slice.split_at_checked, CoreModels.core.slice.Slice.len,
      CoreModels.rust_primitives.slice.slice_length, CoreModels.core.slice.Slice.split_at,
      CoreModels.rust_primitives.slice.slice_split_at, checkedSplit, bound,
      UScalar.le_equiv, coreOptionToOption]

def slicePatternIdentity (input : Slice T) : Slice T := input

theorem slice_pattern_identity (input : Slice T) : slicePatternIdentity input = input := rfl

/-- Only `Unit` is used by preflight; no generic destructor behavior is erased. -/
def thenSomeUnit (condition : Bool) (value : Unit) : RustM (CoreModels.core.option.Option Unit) :=
  if condition then .ok (.Some value) else .ok .None

theorem then_some_unit_true (value : Unit) : thenSomeUnit true value = .ok (.Some value) := rfl

theorem then_some_unit_false (value : Unit) : thenSomeUnit false value = .ok .None := rfl

end BeaconcryptCore.Refinement.RegistrationCodecStandardSlices

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_lowering' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_lowering

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_rejected' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_parts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_parts

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.copied_first_lowering' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.copied_first_lowering

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_existing_model' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.checked_split_existing_model

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.slice_pattern_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.slice_pattern_identity

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.then_some_unit_true' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.then_some_unit_true

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.then_some_unit_false' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecStandardSlices.then_some_unit_false
