-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationByteCopy

/-! Exact source-standard byte vector extension retains every actual U8 clone and checks the final usize bound. Physical heap behavior remains the standard platform boundary. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterByteVector

set_option backward.isDefEq.respectTransparency false in
theorem extend_bytes (before : alloc.vec.Vec U8) (input : Slice U8)
    (room : before.val.length + input.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.U8.Insts.CoreCloneClone before input =
      .ok ⟨before.val ++ input.val, by simpa only [List.length_append] using room⟩ := by
  simp only [alloc.vec.Vec.extend_from_slice, rust_primitives.sequence.seq_extend, RegistrationByteCopy.clone_bytes]
  split
  · rfl
  · exact False.elim (‹¬(before.val ++ input.val).length ≤ Usize.max› (by simpa only [List.length_append] using room))

end BeaconcryptCore.Refinement.AdapterByteVector

/-- info: 'BeaconcryptCore.Refinement.AdapterByteVector.extend_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterByteVector.extend_bytes
