-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.FrameDispatchExtraction.Funs

/-! The actual finite source dispatcher reaches the previously extracted ordinary-frame encoder for three input chunks. The arbitrary many-chunk fallback is never invoked at that shape. Classifying the original slice patterns by length is valid for every list, independently of the codec's result or mutable output. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameDispatch

def patternClass {A : Type} : List A → Nat
  | [] => 0
  | [_] => 1
  | [_, _] => 2
  | [_, _, _] => 3
  | _ => 4

def lengthClass {A : Type} (parts : List A) : Nat :=
  if parts.length = 0 then 0 else if parts.length = 1 then 1
  else if parts.length = 2 then 2 else if parts.length = 3 then 3 else 4

theorem classify {A : Type} (parts : List A) : patternClass parts = lengthClass parts := by
  cases parts with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  simp only [patternClass, lengthClass, List.length_cons]
                  split_ifs <;> omega

def three (first second third : Slice U8) : Slice (Slice U8) :=
  ⟨[first, second, third], by change 3 ≤ Usize.max; scalar_tac⟩

theorem selected_three [FrameDispatchFallback.Operations]
    (sequence sender : U64) (first second third output : Slice U8) :
    beaconcrypt_parse_dispatch.frame.encode_parts sequence sender (three first second third) output =
      beaconcrypt_parse.frame.encode_three sequence sender first second third output := by
  rfl

theorem selected_array [FrameDispatchFallback.Operations]
    (sequence sender : U64) (parts : Array (Slice U8) 3#usize) (output : Slice U8) :
    ∃ first second third,
      (Array.to_slice parts) = three first second third ∧
      beaconcrypt_parse_dispatch.frame.encode_parts sequence sender (Array.to_slice parts) output =
        beaconcrypt_parse.frame.encode_three sequence sender first second third output := by
  obtain ⟨first, second, third, exactParts⟩ := List.length_eq_three.mp parts.property
  have same : Array.to_slice parts = three first second third := by
    apply Subtype.ext
    exact exactParts
  exact ⟨first, second, third, same, same ▸ selected_three sequence sender first second third output⟩

theorem fallback_irrelevant
    (left right : FrameDispatchFallback.Operations)
    (sequence sender : U64) (first second third output : Slice U8) :
    @beaconcrypt_parse_dispatch.frame.encode_parts left sequence sender (three first second third) output =
      @beaconcrypt_parse_dispatch.frame.encode_parts right sequence sender (three first second third) output := by
  rw [@selected_three left, @selected_three right]

end BeaconcryptCore.Refinement.FrameDispatch

/-- info: 'BeaconcryptCore.Refinement.FrameDispatch.classify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameDispatch.classify
/-- info: 'BeaconcryptCore.Refinement.FrameDispatch.selected_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameDispatch.selected_three
/-- info: 'BeaconcryptCore.Refinement.FrameDispatch.selected_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameDispatch.selected_array
/-- info: 'BeaconcryptCore.Refinement.FrameDispatch.fallback_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameDispatch.fallback_irrelevant
