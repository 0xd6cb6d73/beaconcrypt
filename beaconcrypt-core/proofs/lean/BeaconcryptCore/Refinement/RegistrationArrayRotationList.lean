-- SPDX-License-Identifier: 0BSD
import Aeneas

set_option autoImplicit false
set_option warningAsError true

/-! Pure list presentation of the pointwise right-rotation postcondition. This conversion contains no source, codec, parser or readback assumption. -/

namespace BeaconcryptCore.Refinement.RegistrationArrayRotationList

theorem right_rotation_eq {α : Type} (before after : List α) (off : Nat)
    (length : before.length = off + 1)
    (post : ∀ k, after[k]? = if k = 0 then before[off]?
      else if 1 ≤ k ∧ k ≤ off then before[k - 1]? else before[k]?) :
    after = before.drop off ++ before.take off := by
  apply List.ext_getElem?
  intro k
  rw [post, List.getElem?_append, List.length_drop, length, Nat.add_sub_cancel_left]
  simp only [List.getElem?_drop, List.getElem?_take]
  split_ifs <;> simp_all <;> omega

end BeaconcryptCore.Refinement.RegistrationArrayRotationList

/-- info: 'BeaconcryptCore.Refinement.RegistrationArrayRotationList.right_rotation_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationArrayRotationList.right_rotation_eq
