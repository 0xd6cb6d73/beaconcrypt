-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameDispatch
import BeaconcryptCore.AdapterRecordHelpersExtraction.Funs

/-! Three fixed array elements retain the standard left-to-right fold and extension order. The equations hold in any monad, including optional short circuiting and shared platform state; no operation is erased or changed to unconditional success. Array indexing is derived from the actual source representation. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordFixedParts

universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m] {A S : Type}

theorem fold_three (step : S → A → m S) (before : S) (first second third : A) :
    List.foldlM step before [first, second, third] = (do
      let one ← step before first
      let two ← step one second
      step two third) := by
  simp only [List.foldlM, bind_pure]

theorem extend_three (extend : S → A → m S) (before : S) (first second third : A) :
    List.foldlM extend before [first, second, third] = (do
      let one ← extend before first
      let two ← extend one second
      extend two third) :=
  fold_three extend before first second third

omit [Monad m] [LawfulMonad m] in
theorem indices (parts : Array (Slice U8) 3#usize) :
    ∃ first second third,
      parts.val = [first, second, third] ∧
      Array.index_usize parts 0#usize = .ok first ∧
      Array.index_usize parts 1#usize = .ok second ∧
      Array.index_usize parts 2#usize = .ok third := by
  obtain ⟨first, second, third, exactParts⟩ := List.length_eq_three.mp parts.property
  refine ⟨first, second, third, exactParts, ?_⟩
  rcases parts with ⟨values, length⟩
  simp only at exactParts
  subst values
  exact ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.AdapterRecordFixedParts

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFixedParts.fold_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFixedParts.fold_three
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFixedParts.extend_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFixedParts.extend_three
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordFixedParts.indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordFixedParts.indices
