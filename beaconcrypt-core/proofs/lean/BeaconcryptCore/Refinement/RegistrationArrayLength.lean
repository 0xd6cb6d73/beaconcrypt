-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSliceLength
import BeaconcryptCore.RegistrationArrayExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
set_option autoImplicit false
set_option warningAsError true
/-! Partial correctness of actual array-prefix writer lengths, including source
rotation loops and every rejection reply. Loop invariants establish properties
of successful returns; termination, byte permutation and complete codec/source
composition remain separate obligations. No native evaluator dependency is used. -/
namespace BeaconcryptCore.Refinement.RegistrationArrayLength
open RegistrationSliceLength

theorem loop_success {A B : Type} (body : A → RustM (ControlFlow A B))
    (inv : A → Prop) (post : B → Prop)
    (step : ∀ x, inv x → Success (body x) (fun result => match result with
      | .cont next => inv next | .done result => post result))
    (initial : A) (hi : inv initial) : Success (loop body initial) post := by
  have monotone : Lean.Order.monotone (fun (work : A → RustM B) x =>
      match body x with
      | .ok control => match control with
        | .cont next => work next
        | .done result => .ok result
      | .fail error => .fail error
      | .div => .div) := by
    intro left right ordered x
    dsimp only
    cases actual : body x with
    | ok result =>
        cases result with
        | cont next => exact ordered next
        | done result => exact Lean.Order.PartialOrder.rel_refl
    | fail error => exact Lean.Order.PartialOrder.rel_refl
    | div => exact Lean.Order.PartialOrder.rel_refl
  delta loop
  refine Lean.Order.fix_induct monotone
    (motive := fun work => ∀ x, inv x → Success (work x) post) ?_ ?_ initial hi
  · apply Lean.Order.admissible_pi
    intro x
    apply Lean.Order.admissible_pi
    intro _
    apply Lean.Order.admissible_apply (β := fun _ => RustM B)
      (P := fun _ result => Success result post) x
    exact Lean.Order.admissible_flatOrder _ (by
      intro result impossible
      cases impossible)
  · intro work ih x hx
    simp only []
    intro result actual
    have bodyStep := step x hx
    cases hbody : body x with
    | ok cf =>
        cases cf with
        | cont next =>
            have invariant : inv next := bodyStep (.cont next) hbody
            simp only [hbody] at actual
            exact ih next invariant result actual
        | done value =>
            have valid : post value := bodyStep (.done value) hbody
            simp only [hbody] at actual
            cases actual
            exact valid
    | fail err => simp [hbody] at actual
    | div => simp [hbody] at actual

open beaconcrypt_parse.cbordetveraux
attribute [local grind →] write_header_ok

theorem inner_body_length (offset rounds : Usize) (before : Slice U8)
    (position index : Array Usize 1#usize) (condition : Bool) :
    Success (extraction_rotation_inner_1_loop.body offset rounds before position index condition)
      (fun result => match result with
        | .cont next => next.1.length = before.length
        | .done result => result.1.length = before.length) := by
  unfold extraction_rotation_inner_1_loop.body
  repeat' first
    | registration_peel_success
    | split
    | registration_close_success

theorem inner_loop_length (before : Slice U8) (offset rounds : Usize)
    (position index : Array Usize 1#usize) (condition : Bool) :
    Success (extraction_rotation_inner_1_loop before offset rounds position index condition)
      (fun result => result.1.length = before.length) := by
  unfold extraction_rotation_inner_1_loop
  apply loop_success (inv := fun state => state.1.length = before.length)
  · rintro ⟨bytes, position, index, condition⟩ valid result actual
    have preserved := inner_body_length offset rounds bytes position index condition result actual
    cases result <;> exact preserved.trans valid
  · rfl

theorem inner_loop_ok (before after : Slice U8) (offset rounds : Usize)
    (position index finalIndex : Array Usize 1#usize) (condition : Bool)
    (actual : extraction_rotation_inner_1_loop before offset rounds position index condition =
      .ok (after, finalIndex)) : after.length = before.length :=
  inner_loop_length before offset rounds position index condition (after, finalIndex) actual

attribute [local grind →] inner_loop_ok

theorem inner_length (before : Slice U8) (index offset rounds : Usize) :
    Success (extraction_rotation_inner_1 before index offset rounds)
      (fun result => result.2.length = before.length) := by
  unfold extraction_rotation_inner_1
  dsimp only
  repeat' first
    | registration_peel_success
    | registration_close_success

theorem inner_ok (before after : Slice U8) (index offset rounds finalIndex : Usize)
    (actual : extraction_rotation_inner_1 before index offset rounds = .ok (finalIndex, after)) :
    after.length = before.length := inner_length before index offset rounds (finalIndex, after) actual

attribute [local grind →] inner_ok

theorem outer_body_length (offset cycles rounds : Usize) (before : Slice U8)
    (index : Array Usize 1#usize) (condition : Bool) :
    Success (extraction_serialize_array_loop1.body offset cycles rounds before index condition)
      (fun result => match result with
        | .cont next => next.1.length = before.length
        | .done result => result.length = before.length) := by
  unfold extraction_serialize_array_loop1.body
  repeat' first
    | registration_peel_success
    | split
    | registration_close_success

theorem outer_loop_length (before : Slice U8) (offset cycles rounds : Usize)
    (index : Array Usize 1#usize) (condition : Bool) :
    Success (extraction_serialize_array_loop1 offset before cycles rounds index condition)
      (fun result => result.length = before.length) := by
  unfold extraction_serialize_array_loop1
  apply loop_success (inv := fun state => state.1.length = before.length)
  · rintro ⟨bytes, index, condition⟩ valid result actual
    have preserved := outer_body_length offset cycles rounds bytes index condition result actual
    cases result <;> exact preserved.trans valid
  · rfl

theorem serialize_array_length (length : raw_uint64) (before : Slice U8) (offset : Usize) :
    Success (extraction_serialize_array length before offset)
      (fun result => result.2.length = before.length) := by
  unfold extraction_serialize_array
  repeat' first
    | dsimp only [uncurry]
    | registration_peel_success
    | split
    | registration_close_success

theorem serialize_array_ok (length : raw_uint64) (before after : Slice U8) (offset written : Usize)
    (actual : extraction_serialize_array length before offset = .ok (written, after)) :
    after.length = before.length :=
  serialize_array_length length before offset (written, after) actual

attribute [local grind →] serialize_array_ok

theorem array_entry_length (length : U64) (before : Slice U8) (offset : Usize) :
    Success (extraction_array_entry length before offset)
      (fun result => result.2.length = before.length) := by
  unfold extraction_array_entry
  repeat' first
    | registration_peel_success
    | registration_close_success

end BeaconcryptCore.Refinement.RegistrationArrayLength

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.loop_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.loop_success
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.inner_body_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.inner_body_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.inner_loop_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.inner_loop_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.inner_loop_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.inner_loop_ok
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.inner_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.inner_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.inner_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.inner_ok
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.outer_body_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.outer_body_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.outer_loop_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.outer_loop_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.serialize_array_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.serialize_array_length
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.serialize_array_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.serialize_array_ok
/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayLength.array_entry_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayLength.array_entry_length
