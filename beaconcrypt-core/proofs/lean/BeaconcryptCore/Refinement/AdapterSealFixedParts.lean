-- SPDX-License-Identifier: 0BSD
import Aeneas

set_option autoImplicit false
set_option warningAsError true

/-! Two-element unrolling retains each reached monadic operation, including short-circuiting and mutable state. The index facts use the actual Aeneas fixed-array representation. No join, allocation, serializer or primitive law is assumed. -/

namespace BeaconcryptCore.Refinement.AdapterSealFixedParts

theorem fold_two {m : Type → Type} [Monad m] [LawfulMonad m] {Part Acc : Type}
    (step : Acc → Part → m Acc) (initial : Acc) (first second : Part) :
    [first, second].foldlM step initial = (do
      let middle ← step initial first
      step middle second) := by
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem extend_two {m : Type → Type} [Monad m] [LawfulMonad m] {Part : Type}
    (extend : Part → m Unit) (first second : Part) :
    [first, second].forM extend = (do
      extend first
      extend second) := by
  simp only [List.forM, bind_pure_unit]

theorem indices2 {Part : Type} (first second : Part) :
    Aeneas.Std.Array.index_usize (Aeneas.Std.Array.make 2#usize [first, second]) 0#usize = .ok first ∧
      Aeneas.Std.Array.index_usize (Aeneas.Std.Array.make 2#usize [first, second]) 1#usize = .ok second := by
  exact ⟨rfl, rfl⟩

theorem extend_state_two {m : Type → Type} [Monad m] [LawfulMonad m] {Part State : Type}
    (extend : State → Part → m State) (initial : State) (first second : Part) :
    [first, second].foldlM extend initial = (do
      let middle ← extend initial first
      extend middle second) :=
  fold_two extend initial first second

theorem indices (parts : Aeneas.Std.Array (Aeneas.Std.Slice Aeneas.Std.U8) 2#usize) :
    ∃ first second, parts.val = [first, second] ∧
      Aeneas.Std.Array.index_usize parts 0#usize = .ok first ∧
      Aeneas.Std.Array.index_usize parts 1#usize = .ok second := by
  rcases parts with ⟨values, length⟩
  rcases List.length_eq_two.mp length with ⟨first, second, rfl⟩
  exact ⟨first, second, rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.AdapterSealFixedParts

/-- info: 'BeaconcryptCore.Refinement.AdapterSealFixedParts.fold_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealFixedParts.fold_two
/-- info: 'BeaconcryptCore.Refinement.AdapterSealFixedParts.extend_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealFixedParts.extend_two
/-- info: 'BeaconcryptCore.Refinement.AdapterSealFixedParts.indices2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealFixedParts.indices2

/-- info: 'BeaconcryptCore.Refinement.AdapterSealFixedParts.extend_state_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealFixedParts.extend_state_two
/-- info: 'BeaconcryptCore.Refinement.AdapterSealFixedParts.indices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterSealFixedParts.indices
