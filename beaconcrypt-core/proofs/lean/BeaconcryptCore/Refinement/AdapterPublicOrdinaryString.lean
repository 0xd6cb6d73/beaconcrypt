-- SPDX-License-Identifier: 0BSD
import Aeneas
/-! Kernel proof for the unchanged SDK slot panic literal; the generated default native-decide proof is never used. -/
open Aeneas.Std
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryString
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

theorem slot_bound : "a ratchet kernel is absent only while its synchronous effect is running".toByteArray.size ≤ U32.max := by
  have literal : String.ofList ['a', ' ', 'r', 'a', 't', 'c', 'h', 'e', 't', ' ', 'k', 'e', 'r', 'n', 'e', 'l', ' ', 'i', 's', ' ', 'a', 'b', 's', 'e', 'n', 't', ' ', 'o', 'n', 'l', 'y', ' ', 'w', 'h', 'i', 'l', 'e', ' ', 'i', 't', 's', ' ', 's', 'y', 'n', 'c', 'h', 'r', 'o', 'n', 'o', 'u', 's', ' ', 'e', 'f', 'f', 'e', 'c', 't', ' ', 'i', 's', ' ', 'r', 'u', 'n', 'n', 'i', 'n', 'g'] = "a ratchet kernel is absent only while its synchronous effect is running" := by simp
  rw [← literal, String.toByteArray_ofList]
  simp only [List.utf8Encode, List.size_toByteArray, List.length_flatMap, String.length_utf8EncodeChar]
  apply (chars_bound _).trans
  simp only [List.length_cons, List.length_nil]
  scalar_tac
end BeaconcryptCore.Refinement.AdapterPublicOrdinaryString
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryString.slot_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryString.slot_bound
