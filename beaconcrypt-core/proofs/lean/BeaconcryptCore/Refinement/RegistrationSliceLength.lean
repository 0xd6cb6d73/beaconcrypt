-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs
import BeaconcryptCore.RegistrationShallowExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM WP
set_option autoImplicit false
set_option warningAsError true
/-! Length of every successful result of the actual generated header and shallow
serializer/sizer bodies. All rejection values and partial successful poststates
are covered. Bounds, readback and complete public codec source composition are
separate obligations. The proof decomposes actual binds and source branches;
standard mutable-slice back functions and indexed writes preserve length. -/
namespace BeaconcryptCore.Refinement.RegistrationSliceLength

def Success {A : Type} (work : RustM A) (post : A → Prop) : Prop :=
  ∀ result, work = .ok result → post result

theorem bind_success {A B : Type} (work : RustM A) (next : A → RustM B)
    (post : B → Prop) (h : ∀ result, work = .ok result → Success (next result) post) :
    Success (work >>= next) post := by
  cases hw : work with
  | ok value => simpa only [hw, bind_tc_ok] using h value hw
  | fail _ => simp [Success, bind_tc_fail]
  | div => simp [Success, bind_tc_div]

theorem update_length {A : Type} (before after : Slice A) (index : Usize) (value : A)
    (h : Slice.update before index value = .ok after) : after.length = before.length := by
  have hs := Slice.update_spec before index value
  simp only [WP.partialSpec, h] at hs
  rw [hs.2]
  exact Slice.set_length _ _ _

theorem index_mut_length {A : Type} (before : Slice A) (index : Usize) (value : A)
    (back : A → Slice A) (h : Slice.index_mut_usize before index = .ok (value, back)) :
    ∀ replacement, (back replacement).length = before.length := by
  have hs := Slice.index_mut_usize_spec before index
  simp only [WP.partialSpec, h, uncurry'] at hs
  obtain ⟨_, _, rfl⟩ := hs
  exact fun _ => Slice.set_length _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem split_mut_length {A : Type} (before : Slice A) (index : Usize)
    (parts : Slice A × Slice A) (back : (Slice A × Slice A) → Slice A)
    (h : core.slice.Slice.split_at_mut before index = .ok (parts, back)) :
    ∀ replacement, (back replacement).length = before.length := by
  unfold core.slice.Slice.split_at_mut CoreModels.rust_primitives.slice.slice_split_at_mut at h
  unfold Aeneas.Std.core.slice.Slice.split_at_mut at h
  split at h
  · simp only [bind_tc_ok] at h
    obtain ⟨rfl, rfl⟩ := h
    intro replacement
    dsimp only [Slice.length]
    split_ifs with lengths
    · simp [lengths]
      have total := List.splitAt_length index.val before.val
      omega
    · rfl
  · simp only [bind_tc_fail, reduceCtorEq] at h

open Lean Elab Tactic in
elab "registration_peel_success" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Success do throwError "not a success predicate"
  let work := target.getAppArgs[1]!.consumeMData
  unless work.isAppOf ``Bind.bind || work.isAppOf ``Aeneas.Std.bind do throwError "not a source bind"
  let args := work.getAppArgs
  let source := args[args.size - 2]!
  let next := args[args.size - 1]!
  let post := target.getAppArgs[2]!
  let rule ← Lean.Meta.mkAppM ``bind_success #[source, next, post]
  let goals ← goal.apply rule
  replaceMainGoal goals
  evalTactic (← `(tactic| (
    intro result actual
    try (guard_hyp result : _ × _; rcases result with ⟨left, right⟩)
    try (have modifiedLength := update_length _ _ _ _ actual)
    try (have restoredLength := index_mut_length _ _ _ _ actual)
    try (have splitLength := split_mut_length _ _ _ _ actual))))
  evalTactic (← `(tactic| try dsimp only [uncurry]))

open Lean Elab Tactic in
elab "registration_close_success" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Success do throwError "not a success predicate"
  evalTactic (← `(tactic| simp [Success]; all_goals grind))

open beaconcrypt_parse.cbordetveraux

set_option maxHeartbeats 300000 in
theorem write_header_length (header : beaconcrypt_parse.cbordetveraux.header)
    (before : Slice U8) (offset : Usize) :
    Success (write_header header before offset) (fun result => result.2.length = before.length) := by
  unfold write_header
  repeat' first
    | dsimp only [uncurry]
    | registration_peel_success
    | split
    | registration_close_success

theorem write_header_ok (header : beaconcrypt_parse.cbordetveraux.header)
    (before after : Slice U8) (offset written : Usize)
    (h : write_header header before offset = .ok (written, after)) :
    after.length = before.length :=
  write_header_length header before offset (written, after) h

attribute [local grind →] write_header_ok

theorem size_header_length (header : beaconcrypt_parse.cbordetveraux.header)
    (before : Slice Usize) :
    Success (size_header header before) (fun result => result.2.length = before.length) := by
  unfold size_header
  repeat' first
    | dsimp only [uncurry]
    | registration_peel_success
    | split
    | registration_close_success

theorem size_header_ok (header : beaconcrypt_parse.cbordetveraux.header)
    (before after : Slice Usize) (result : Bool)
    (h : size_header header before = .ok (result, after)) :
    after.length = before.length := size_header_length header before (result, after) h

attribute [local grind →] size_header_ok

theorem serialize_int_length (value : cbor_int) (before : Slice U8) (offset : Usize) :
    Success (extraction_serialize_shallow_int value before offset)
      (fun result => result.2.length = before.length) := by
  unfold extraction_serialize_shallow_int
  repeat' first
    | registration_peel_success
    | registration_close_success

theorem serialize_string_length (value : cbor_string) (before : Slice U8) (offset : Usize) :
    Success (extraction_serialize_shallow_string value before offset)
      (fun result => result.2.length = before.length) := by
  unfold extraction_serialize_shallow_string
  repeat' first
    | dsimp only [uncurry]
    | registration_peel_success
    | split
    | registration_close_success

theorem size_int_length (value : cbor_int) (before : Slice Usize) :
    Success (extraction_size_shallow_int value before)
      (fun result => result.2.length = before.length) := by
  unfold extraction_size_shallow_int
  repeat' first
    | registration_peel_success
    | split
    | registration_close_success

theorem size_string_length (value : cbor_string) (before : Slice Usize) :
    Success (extraction_size_shallow_string value before)
      (fun result => result.2.length = before.length) := by
  unfold extraction_size_shallow_string
  repeat' first
    | registration_peel_success
    | split
    | registration_close_success

end BeaconcryptCore.Refinement.RegistrationSliceLength

/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.bind_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.bind_success
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.update_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.update_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.index_mut_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.index_mut_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.split_mut_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.split_mut_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.write_header_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.write_header_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.write_header_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.write_header_ok
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.size_header_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.size_header_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.size_header_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.size_header_ok
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.serialize_int_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.serialize_int_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.serialize_string_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.serialize_string_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.size_int_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.size_int_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationSliceLength.size_string_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSliceLength.size_string_length
