-- SPDX-License-Identifier: 0BSD
import Aeneas
open Aeneas.Std
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorString
private theorem chars_bound (text : List Char) :
    (text.map Char.utf8Size).sum ≤ 4 * text.length := by
  induction text with
  | nil => simp
  | cons char rest ih =>
    have small : char.utf8Size ≤ 4 := by
      simp only [Char.utf8Size]
      split_ifs <;> omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Explicit kernel proof for the unchanged source panic message bound. -/
theorem failure_bound : "Failed to construct beacon".toByteArray.size ≤ U32.max := by
  have literal : String.ofList ['F', 'a', 'i', 'l', 'e', 'd', ' ', 't', 'o', ' ', 'c', 'o', 'n', 's', 't', 'r', 'u', 'c', 't', ' ', 'b', 'e', 'a', 'c', 'o', 'n'] = "Failed to construct beacon" := by simp
  rw [← literal, String.toByteArray_ofList]
  simp only [List.utf8Encode, List.size_toByteArray, List.length_flatMap, String.length_utf8EncodeChar]
  apply (chars_bound _).trans
  simp only [List.length_cons, List.length_nil]
  scalar_tac

theorem bound_irrelevant (text : String) (left right : text.toByteArray.size ≤ U32.max) :
    toStr text left = toStr text right := rfl
end BeaconcryptCore.Refinement.AdapterBeaconConstructorString
/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorString.failure_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorString.failure_bound

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorString.bound_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorString.bound_irrelevant
