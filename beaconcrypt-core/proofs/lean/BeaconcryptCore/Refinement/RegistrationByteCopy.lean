-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationShallowExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM WP
set_option autoImplicit false
set_option warningAsError true
/-! Actual standard U8 cloning, mutable splitting and byte-copy/write-back.
Every clone call is retained before proving its result, and the complete
updated slice is returned. No equality for arbitrary effectful Clone is assumed. -/
namespace BeaconcryptCore.Refinement.RegistrationByteCopy

theorem clone_bytes (values : List U8) :
    values.mapM core.U8.Insts.CoreCloneClone.clone = .ok values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, ih, bind_tc_ok]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem copy_bytes (destination source : Slice U8) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy destination source =
      if destination.length = source.length then .ok source else .fail .panic := by
  have mapped : source.val.mapM core.U8.Insts.CoreMarkerCopy.cloneCloneInst.clone = .ok source.val :=
    clone_bytes source.val
  unfold core.slice.Slice.copy_from_slice rust_primitives.slice.slice_clone_from_slice
  split_ifs
  · split
    · rename_i cloned actual
      have same : source.val = cloned := RustM.ok.inj (mapped.symm.trans actual)
      subst cloned
      rfl
    · rename_i error actual
      have impossible := mapped.symm.trans actual
      cases impossible
    · rename_i actual
      have impossible := mapped.symm.trans actual
      cases impossible
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem split_mut_success {A : Type} (input : Slice A) (mid : Usize)
    (bound : mid.val ≤ input.length) :
    ∃ front tail back, core.slice.Slice.split_at_mut input mid = .ok ((front, tail), back) ∧
      front.length = mid.val ∧ tail.length + mid.val = input.length ∧
      front.val = input.val.take mid.val ∧ tail.val = input.val.drop mid.val ∧
      (∀ front' tail', front'.length = mid.val → tail'.length + mid.val = input.length →
        (back (front', tail')).val = front'.val ++ tail'.val ∧
        (back (front', tail')).length = input.length) := by
  have spec := Aeneas.Std.core.slice.Slice.split_at_mut.spec input mid
  cases actual : Aeneas.Std.core.slice.Slice.split_at_mut input mid with
  | ok result =>
    rcases result with ⟨⟨front, tail⟩, back⟩
    simp only [WP.partialSpec, actual, uncurry'] at spec
    refine ⟨front, tail, back, ?_, spec⟩
    unfold core.slice.Slice.split_at_mut rust_primitives.slice.slice_split_at_mut
    rw [actual]
    rfl
  | fail error =>
    simp only [WP.partialSpec, actual] at spec
    cases error <;> simp_all
    omega
  | div =>
    simp only [WP.partialSpec, actual] at spec

/-- Exact nested mutable splitting and byte-copy/write-back used by the source serializer. -/
def copyInto (input : Slice U8) (offset : Usize) (source : Slice U8) : RustM (Slice U8) := do
  let ((front, remaining), back) ← core.slice.Slice.split_at_mut input offset
  let ((destination, tail), back1) ← core.slice.Slice.split_at_mut remaining source.len
  let copied ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy destination source
  .ok (back (front, back1 (copied, tail)))

theorem copy_into (input : Slice U8) (offset : Usize) (source : Slice U8)
    (space : offset.val + source.length ≤ input.length) :
    ∃ after, copyInto input offset source = .ok after ∧ after.length = input.length ∧
      after.val = input.val.take offset.val ++ source.val ++ input.val.drop (offset.val + source.length) := by
  obtain ⟨front, remaining, back, split0, frontLength, remainingLength, frontBytes,
    remainingBytes, backLaw⟩ := split_mut_success input offset (by omega)
  obtain ⟨destination, tail, back1, split1, destinationLength, tailLength, _, tailBytes,
    back1Law⟩ := split_mut_success remaining source.len (by simp only [Slice.len_val]; omega)
  have copied : core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy destination source = .ok source := by
    rw [copy_bytes]
    have same : destination.length = source.length := by simpa only [Slice.len_val] using destinationLength
    simp only [same, ↓reduceIte]
  have inner := back1Law source tail (by simp only [Slice.len_val]) tailLength
  have outer := backLaw front (back1 (source, tail)) frontLength (by rw [inner.2]; exact remainingLength)
  refine ⟨back (front, back1 (source, tail)), ?_, outer.2, ?_⟩
  · unfold copyInto
    rw [split0]
    simp only [bind_tc_ok, uncurry]
    rw [split1]
    simp only [bind_tc_ok, uncurry]
    rw [copied]
    rfl
  · rw [outer.1, frontBytes, inner.1, tailBytes, remainingBytes]
    simp only [Slice.len_val, List.drop_drop, List.append_assoc]

end BeaconcryptCore.Refinement.RegistrationByteCopy

/-- info: 'BeaconcryptCore.Refinement.RegistrationByteCopy.clone_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationByteCopy.clone_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationByteCopy.copy_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationByteCopy.copy_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationByteCopy.split_mut_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationByteCopy.split_mut_success

/-- info: 'BeaconcryptCore.Refinement.RegistrationByteCopy.copy_into' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationByteCopy.copy_into
