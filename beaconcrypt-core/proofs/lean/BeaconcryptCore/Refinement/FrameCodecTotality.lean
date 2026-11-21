-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecArgument

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecTotality

def ValidArgument (input : Slice U8) : Option (U64 × Usize) → Prop
  | none => True
  | some (_, used) => 1 ≤ used.val ∧ used.val ≤ input.val.length

private theorem slice_index_exact (input : Slice U8) (index : Usize)
    (bound : index.val < input.val.length) :
    Slice.index_usize input index = ok input.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem bound,
    getElem!_pos input.val index.val bound]

private theorem shift_five (byte : U8) :
    byte >>> 5#i32 = ok (⟨byte.bv >>> 5⟩ : U8) := rfl

private theorem lift_and (left right : U8) :
    lift (left &&& right) = ok (⟨left.bv &&& right.bv⟩ : U8) := rfl

/-- The extracted canonical argument decoder returns normally on every input and every admitted width stays within that input. -/
theorem decode_argument_total (input : Slice U8) (major : U8) :
    ∃ reply, frame.decode_argument input major = ok reply ∧ ValidArgument input reply := by
  unfold frame.decode_argument
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  by_cases empty : input.len = 0#usize
  · simp only [empty, decide_true, ite_true]
    exact ⟨none, rfl, trivial⟩
  · simp only [empty, decide_false, Bool.false_eq_true, ite_false]
    have nonempty : 0 < input.val.length := by
      have unequal : input.len.val ≠ 0 := by
        intro zero
        apply empty
        apply UScalar.eq_of_val_eq
        simpa only [UScalar.ofNatCore_val_eq] using zero
      simpa only [Slice.len_val, Slice.length] using Nat.pos_of_ne_zero unequal
    rw [slice_index_exact input 0#usize (by simpa only [UScalar.ofNatCore_val_eq] using nonempty)]
    simp only [bind_tc_ok, shift_five]
    split
    · exact ⟨none, rfl, trivial⟩
    · simp only [lift_and, bind_tc_ok]
      split
      · simp only [CoreModels.core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok]
        refine ⟨_, rfl, ?_⟩
        norm_num [ValidArgument]
        omega
      · split
        · split
          · exact ⟨none, rfl, trivial⟩
          · rename_i fits
            have width : 2 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            split
            · simp only [CoreModels.core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok]
              refine ⟨_, rfl, ?_⟩
              norm_num [ValidArgument]
              omega
            · exact ⟨none, rfl, trivial⟩
        · split
          · exact ⟨none, rfl, trivial⟩
          · rename_i fits
            have width : 3 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 2#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok]
            split
            · refine ⟨_, rfl, ?_⟩
              norm_num [ValidArgument]
              omega
            · exact ⟨none, rfl, trivial⟩
        · split
          · exact ⟨none, rfl, trivial⟩
          · rename_i fits
            have width : 5 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 2#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 3#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 4#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok]
            split
            · refine ⟨_, rfl, ?_⟩
              norm_num [ValidArgument]
              omega
            · exact ⟨none, rfl, trivial⟩
        · split
          · exact ⟨none, rfl, trivial⟩
          · rename_i fits
            have width : 9 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 2#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 3#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 4#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 5#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 6#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 7#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            rw [slice_index_exact input 8#usize (by norm_num; omega)]
            simp only [bind_tc_ok]
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok]
            split
            · refine ⟨_, rfl, ?_⟩
              norm_num [ValidArgument]
              omega
            · exact ⟨none, rfl, trivial⟩
        · exact ⟨none, rfl, trivial⟩

end BeaconcryptCore.Refinement.FrameCodecTotality

/-- info: 'BeaconcryptCore.Refinement.FrameCodecTotality.decode_argument_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecTotality.decode_argument_total
