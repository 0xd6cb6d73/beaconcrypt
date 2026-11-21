-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationPreflightExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderSize
import BeaconcryptCore.Refinement.RegistrationHeaderWord
import BeaconcryptCore.Refinement.RegistrationByteCopy
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM WP
set_option autoImplicit false
set_option warningAsError true
/-! Exact standard-model suffix borrowing, complete writeback, checked subtraction and actual handwritten argument-word execution. Every bounded width up to eight copies the source bytes into the right-aligned zeroed word through the original mutable array borrow and U8 clone calls, then executes original from_be_bytes. The source integer conversion is inverse to actual to_be_bytes; public preflight acceptance is composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightWord
open beaconcrypt_parse FrameCodecWord

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem from_to (value : U64) :
    Aeneas.Std.core.num.U64.from_be_bytes (Aeneas.Std.core.num.U64.to_be_bytes value) = value := by
  apply UScalar.eq_of_val_eq
  unfold Aeneas.Std.core.num.U64.from_be_bytes Aeneas.Std.core.num.U64.to_be_bytes
  simp only [UScalar.val, BitVec.toNat_cast]
  rw [List.map_map, U8.bv_comp_UScalar_mk, List.map_id]
  unfold BitVec.fromBEBytes BitVec.toBEBytes
  simp only [BitVec.toNat_cast]
  have reversed := congrArg (fun bytes => (BitVec.fromLEBytes bytes).toNat)
    (List.reverse_reverse value.bv.toLEBytes)
  have inverse := congrArg BitVec.toNat (BitVec.fromLEBytes_toLEBytes (by decide) value.bv)
  exact reversed.trans (by simpa only [BitVec.toNat_cast] using inverse)

theorem from_word (value : U64) : core.num.U64.from_be_bytes (word value) = .ok value := by
  have source := word_exact value
  change RustM.ok (Aeneas.Std.core.num.U64.to_be_bytes value) = .ok (word value) at source
  have same := RustM.ok.inj source
  rw [← same]
  change RustM.ok (Aeneas.Std.core.num.U64.from_be_bytes (Aeneas.Std.core.num.U64.to_be_bytes value)) = _
  rw [from_to]
set_option backward.isDefEq.respectTransparency false in
theorem suffix_spec {A : Type} {N : Usize} (before : Array A N) (start : Usize) :
    WP.partialSpec
      (core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice A))
        before { start := start })
      (uncurry' fun (suffix : Slice A) (back : Slice A → Array A N) =>
        suffix.val = before.val.slice start.val N.val ∧
        suffix.length = N.val - start.val ∧
        ∀ replacement, (back replacement).val = before.val.setSlice! start.val replacement.val)
      (fun | .panic => ¬ start.val ≤ N.val | _ => False) False := by
  simp only [core.Array.Insts.CoreOpsIndexIndexMut.index_mut,
    core.array.Array.as_mut_slice, rust_primitives.slice.array_as_mut_slice,

    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,

    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice_mut,
    Array.to_slice_mut, bind_tc_ok, uncurry]
  unfold Slice.subslice
  split <;> rename_i bound
  · simp [WP.partialSpec, Array.from_slice, Array.to_slice, uncurry', Slice.length,
      List.slice_length, List.length_setSlice!, ]
  · simp [WP.partialSpec, Array.to_slice, Slice.length, ] at bound ⊢
    scalar_tac

set_option backward.isDefEq.respectTransparency false in
theorem suffix_success {A : Type} {N : Usize} (before : Array A N) (start : Usize)
    (bound : start.val ≤ N.val) :
    ∃ suffix back,
      core.Array.Insts.CoreOpsIndexIndexMut.index_mut
        (core.Slice.Insts.CoreOpsIndexIndexMut
          (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice A))
        before { start := start } = .ok (suffix, back) ∧
      suffix.val = before.val.slice start.val N.val ∧
      suffix.length = N.val - start.val ∧
      ∀ replacement, (back replacement).val = before.val.setSlice! start.val replacement.val := by
  have spec := suffix_spec before start
  cases actual : core.Array.Insts.CoreOpsIndexIndexMut.index_mut
      (core.Slice.Insts.CoreOpsIndexIndexMut
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice A))
      before { start := start } with
  | ok result =>
    rcases result with ⟨suffix, back⟩
    simp only [WP.partialSpec, actual, uncurry'] at spec
    exact ⟨suffix, back, rfl, spec⟩
  | fail error => cases error <;> simp_all [WP.partialSpec]
  | div => simp_all [WP.partialSpec]

set_option backward.isDefEq.respectTransparency false in
theorem checked_sub (left right result : Usize) (value : left.val = right.val + result.val) :
    (left - right : RustM Usize) = .ok result := by
  have spec := @UScalar.sub_spec .Usize left right
  cases actual : (left - right : RustM Usize) with
  | ok output =>
    simp only [WP.partialSpec, actual] at spec
    congr 1
    apply UScalar.eq_of_val_eq
    omega
  | fail error => cases error <;> simp_all [WP.partialSpec]
  | div => simp_all [WP.partialSpec]

def padded (input : Slice U8) (width : Usize) (length : input.length = width.val)
    (bound : width.val ≤ 8) : Array U8 8#usize :=
  ⟨List.replicate (8 - width.val) 0#u8 ++ input.val, by
    simp only [List.length_append, List.length_replicate]
    change (8 - width.val) + input.length = 8
    omega⟩

set_option backward.isDefEq.respectTransparency false in
theorem argument_word (input : Slice U8) (width : Usize) (length : input.length = width.val)
    (bound : width.val ≤ 8) :
    extraction_argument_word input width = core.num.U64.from_be_bytes (padded input width length bound) := by
  let start := Usize.wrapping_sub 8#usize width
  have startValue : start.val = 8 - width.val := by
    rw [RegistrationHeaderSize.sub_value _ _ (by scalar_tac)]
    rfl
  have subtract : ((8#usize : Usize) - width : RustM Usize) = .ok start :=
    checked_sub 8#usize width start (by change 8 = width.val + start.val; omega)
  obtain ⟨suffix, back, source, _, suffixLength, backBytes⟩ := suffix_success
    (Array.repeat 8#usize 0#u8) start (by change start.val ≤ 8; omega)
  have copied : core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy suffix input = .ok input := by
    rw [RegistrationByteCopy.copy_bytes]
    rw [ite_eq_left (by rw [suffixLength]; change 8 - start.val = input.length; omega)]
  have updated : back input = padded input width length bound := by
    apply Subtype.ext
    rw [backBytes]
    change (List.replicate 8 0#u8).setSlice! start.val input.val = _
    simp only [List.setSlice!, List.length_replicate]
    have inputLength : input.val.length = width.val := length
    have whole : input.val.take width.val = input.val := by rw [← inputLength, List.take_length]
    rw [inputLength, show min width.val (8 - start.val) = width.val by omega,
      whole, show start.val + width.val = 8 by omega]
    simp only [List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.take_replicate, startValue]
    rw [show min (8 - width.val) 8 = 8 - width.val by omega]
    rfl
  unfold extraction_argument_word
  rw [subtract]
  simp only [bind_tc_ok]
  rw [source]
  simp only [bind_tc_ok, uncurry]
  rw [copied]
  simp only [bind_tc_ok, updated]

end BeaconcryptCore.Refinement.RegistrationPreflightWord

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.from_to' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.from_to

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.from_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.from_word

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.suffix_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.suffix_spec

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.suffix_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.suffix_success

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.checked_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.checked_sub

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightWord.argument_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightWord.argument_word
