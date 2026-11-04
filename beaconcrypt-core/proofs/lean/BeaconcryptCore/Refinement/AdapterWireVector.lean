-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterWireStatefulWriter

/-! Byte-level facts about the actual pinned std vector models used by the source writer. Reservation is deliberately absent from these deterministic lemmas. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterWireVector

def zeros (capacity : Usize) : alloc.vec.Vec U8 :=
  ⟨List.replicate capacity.val 0#u8, by simp only [List.length_replicate]; scalar_tac⟩

theorem clone_list (bytes : List U8) :
    bytes.mapM core.U8.Insts.CoreCloneClone.clone = ok bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
      simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, bind_tc_ok, ih]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem create_zeros (capacity : Usize) :
    rust_primitives.sequence.seq_create core.U8.Insts.CoreCloneClone 0#u8 capacity =
      ok (zeros capacity) := by
  unfold rust_primitives.sequence.seq_create
  split
  · rename_i empty
    congr 1
    apply Subtype.ext
    simp only [Slice.new, zeros, empty, List.replicate_zero]
  · rename_i nonempty
    simp only [clone_list]
    have positive : 0 < capacity.val := Nat.pos_of_ne_zero nonempty
    have bytes : List.replicate (capacity.val - 1) 0#u8 ++ [0#u8] =
        List.replicate capacity.val 0#u8 := by
      rw [← List.replicate_succ']
      congr 1
      omega
    have bounded : capacity.val ≤ Usize.max := by scalar_tac
    simp only [bytes, List.length_replicate, bounded, ↓reduceDIte]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem resize_empty (capacity : Usize) :
    alloc.vec.Vec.resize core.U8.Insts.CoreCloneClone (Slice.new U8) capacity 0#u8 =
      ok (zeros capacity) := by
  unfold alloc.vec.Vec.resize
  simp only [rust_primitives.sequence.seq_len, bind_tc_ok]
  split
  · rw [PqxdhRefinement.usize_sub_eq _ _ (by
      simp only [Slice.len_val, Slice.length, Slice.new, List.length_nil, Nat.zero_le])]
    simp only [Slice.len_val, Slice.length, Slice.new, List.length_nil, Nat.sub_zero]
    have same : (⟨BitVec.ofNat _ capacity.val⟩ : Usize) = capacity := by
      apply UScalar.eq_of_val_eq
      exact Nat.mod_eq_of_lt capacity.hmax
    rw [same]
    simp only [bind_tc_ok, create_zeros, rust_primitives.sequence.seq_concat,
      Slice.new, zeros, List.nil_append, List.length_replicate]
    have bounded : capacity.val ≤ Usize.max := by scalar_tac
    simp only [bounded, ↓reduceDIte, bind_tc_ok]
    rfl
  · rename_i small
    have empty : capacity.val = 0 := by
      simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, Slice.new, List.length_nil] at small
      omega
    simp only [rust_primitives.sequence.seq_drain, Slice.len_val, Slice.length,
      Slice.new, List.length_nil, empty, le_refl, and_self, ↓reduceDIte, bind_tc_ok]
    change ok (Slice.new U8) = ok (zeros capacity)
    congr 1
    apply Subtype.ext
    simp only [Slice.new, zeros, empty, List.replicate_zero]

def take (bytes : alloc.vec.Vec U8) (written : Usize) : alloc.vec.Vec U8 :=
  ⟨bytes.val.take written.val, by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans bytes.property⟩

set_option backward.isDefEq.respectTransparency false in
theorem truncate_bytes (bytes : alloc.vec.Vec U8) (written : Usize) :
    alloc.vec.Vec.truncate bytes written = ok (take bytes written) := by
  unfold alloc.vec.Vec.truncate
  simp only [rust_primitives.sequence.seq_len, bind_tc_ok]
  split
  · rename_i shorter
    have bounded : written.val ≤ bytes.val.length := by
      simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at shorter
      omega
    simp only [rust_primitives.sequence.seq_drain, Slice.len_val, Slice.length,
      bounded, le_refl, and_self, ↓reduceDIte, bind_tc_ok]
    change ok (⟨bytes.val.take written.val ++ bytes.val.drop bytes.val.length, _⟩ :
      alloc.vec.Vec U8) = ok (take bytes written)
    simp only [List.drop_length, List.append_nil, take]
  · rename_i longer
    have bounded : bytes.val.length ≤ written.val := by
      simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at longer
      omega
    congr 1
    apply Subtype.ext
    exact (List.take_of_length_le bounded).symm

theorem deref_mut_bytes (bytes : alloc.vec.Vec U8) :
    alloc.vec.Vec.Insts.CoreOpsDerefDerefMutSlice.deref_mut bytes = ok (bytes, id) := rfl

end BeaconcryptCore.Refinement.AdapterWireVector

/-- info: 'BeaconcryptCore.Refinement.AdapterWireVector.clone_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireVector.clone_list

/-- info: 'BeaconcryptCore.Refinement.AdapterWireVector.create_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireVector.create_zeros

/-- info: 'BeaconcryptCore.Refinement.AdapterWireVector.resize_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireVector.resize_empty

/-- info: 'BeaconcryptCore.Refinement.AdapterWireVector.truncate_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireVector.truncate_bytes

/-- info: 'BeaconcryptCore.Refinement.AdapterWireVector.deref_mut_bytes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterWireVector.deref_mut_bytes
