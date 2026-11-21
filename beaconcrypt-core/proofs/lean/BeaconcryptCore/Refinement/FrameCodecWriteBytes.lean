-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecRepresentation
import BeaconcryptCore.Computational.TransportSizingBridge

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse
open BeaconcryptCore.Refinement.FrameCodecArgument
open BeaconcryptCore.Refinement.FrameCodecRepresentation
open BeaconcryptCore.Computational
open PqxdhRefinement

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecWriteBytes

theorem clone_bytes (bytes : List U8) :
    bytes.mapM core.U8.Insts.CoreCloneClone.clone = ok bytes := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
      simp only [List.mapM_cons, core.U8.Insts.CoreCloneClone.clone, bind_tc_ok, ih]
      rfl

/-- Byte copying returns the supplied bytes exactly, after checking the destination length. -/
theorem copy_bytes (destination source : Slice U8)
    (sameLength : destination.val.length = source.val.length) :
    core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy destination source = ok source := by
  simp only [core.slice.Slice.copy_from_slice, core.U8.Insts.CoreMarkerCopy,
    rust_primitives.slice.slice_clone_from_slice, Slice.length, sameLength, ite_true]
  split
  · rename_i copied copyEq
    have same : copied = source.val := (RustM.ok.inj ((clone_bytes source.val).symm.trans copyEq)).symm
    subst copied
    rfl
  · rename_i error copyEq
    have impossible := (clone_bytes source.val).symm.trans copyEq
    cases impossible
  · rename_i copyEq
    have impossible := (clone_bytes source.val).symm.trans copyEq
    cases impossible

/-- Native mutable subslice write-back changes precisely its selected byte interval. -/
def splice (output source : Slice U8) (offset : Nat) : Slice U8 :=
  ⟨output.val.setSlice! offset source.val, by simpa using output.property⟩

def rangeView (output : Slice U8) (start stop : Nat) : Slice U8 :=
  ⟨output.val.slice start stop, (List.slice_length_le _ _ _).trans output.property⟩

/-- Both the borrowed range and its write-back are the native mutable slice operations. -/
theorem slice_mut_exact (output : Slice U8) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (bound : stop.val ≤ output.val.length) :
    rust_primitives.slice.slice_slice_mut output start stop =
      ok (rangeView output start.val stop.val, fun replacement => splice output replacement start.val) := by
  simp only [rust_primitives.slice.slice_slice_mut, Slice.subslice, Slice.length,
    ordered, bound, and_self, ite_true]
  rfl

/-- The generated writer's full-range mutation forwards the exact borrowed range and write-back. -/
theorem range_mut_exact (output : Slice U8) (start stop : Usize)
    (ordered : start.val ≤ stop.val) (bound : stop.val ≤ output.val.length) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      output { start, «end» := stop } =
      ok (rangeView output start.val stop.val, fun replacement => splice output replacement start.val) := by
  exact slice_mut_exact output start stop ordered bound

/-- Prefix mutation has precisely the same native write-back, starting at byte zero. -/
theorem prefix_mut_exact (output : Slice U8) (stop : Usize) (bound : stop.val ≤ output.val.length) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      output { «end» := stop } =
      ok (rangeView output 0 stop.val, fun replacement => splice output replacement 0) := by
  exact slice_mut_exact output 0#usize stop (by simp) bound

/-- Suffix mutation preserves the complete prefix preceding the selected writer offset. -/
theorem suffix_mut_exact (output : Slice U8) (start : Usize) (bound : start.val ≤ output.val.length) :
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      output { start } =
      ok (rangeView output start.val output.val.length, fun replacement => splice output replacement start.val) := by
  simpa only [core.Slice.Insts.CoreOpsIndexIndexMut.index_mut,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
    rust_primitives.slice.slice_length, bind_tc_ok, Slice.len_val, Slice.length] using
    slice_mut_exact output start output.len bound (by simp)

theorem rangeView_length (output : Slice U8) (start stop : Nat)
    (bound : stop ≤ output.val.length) :
    (rangeView output start stop).val.length = stop - start := by
  simp only [rangeView, List.slice, List.length_drop, List.length_take]
  omega

/-- Read-only native prefix slicing returns precisely the bytes later passed to copying. -/
theorem prefix_read_exact (input : Slice U8) (stop : Usize) (bound : stop.val ≤ input.val.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      input { «end» := stop } = ok (rangeView input 0 stop.val) := by
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, UScalar.le_equiv, Slice.len_val, Slice.length,
    bound, ite_true, rust_primitives.slice.slice_slice, Slice.subslice,
    UScalar.ofNatCore_val_eq, Nat.zero_le, and_self, bind_tc_ok]
  rfl

/-- The array adapter used by the generated writer selects the same exact prefix. -/
theorem array_prefix_exact {N : Usize} (input : Std.Array U8 N) (stop : Usize)
    (bound : stop.val ≤ N.val) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8))
      input { «end» := stop } = ok (rangeView (Std.Array.to_slice input) 0 stop.val) := by
  simp only [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, bind_tc_ok]
  exact prefix_read_exact input.to_slice stop (by simpa only [Std.Array.to_slice, input.property] using bound)

def argumentSlice (major : U8) (value : U64) : Slice U8 :=
  ⟨argumentBytes major value, by
    rw [argumentBytes_length]
    have := (argument_length_pos major value).2
    have maximum : 9 ≤ Usize.max := by scalar_tac
    omega⟩

/-- The selected native encoder bytes are exactly the core write request's borrowed source slice. -/
theorem argumentSlice_view (major : U8) (value : U64) :
    rangeView (Std.Array.to_slice (encoded major value).bytes) 0
      (encoded major value).length.val = argumentSlice major value := by
  apply Subtype.ext
  simp [rangeView, Std.Array.to_slice, List.slice, argumentSlice, argumentBytes]

/-- The actual scalar writer returns its canonical bytes and the exact original destination suffix. -/
theorem write_argument_exact (major : U8) (value : U64) (output : Slice U8)
    (capacity : (encoded major value).length.val ≤ output.val.length) :
    frame.write_argument major value output =
      ok ((encoded major value).length, splice output (argumentSlice major value) 0) := by
  simp only [frame.write_argument, encode_argument_exact, bind_tc_ok,
    prefix_mut_exact output (encoded major value).length capacity]
  rw [array_prefix_exact (encoded major value).bytes (encoded major value).length
    (by have := (argument_length_pos major value).2; simpa using this)]
  simp only [bind_tc_ok, argumentSlice_view]
  change (do
    let copied ← core.slice.Slice.copy_from_slice core.U8.Insts.CoreMarkerCopy
      (rangeView output 0 (encoded major value).length.val) (argumentSlice major value)
    ok ((encoded major value).length, splice output copied 0)) = _
  rw [copy_bytes _ _ (by
    rw [rangeView_length output 0 (encoded major value).length.val capacity]
    simp only [Nat.sub_zero, argumentSlice, argumentBytes_length])]
  rfl

theorem splice_length (output source : Slice U8) (offset : Nat) :
    (splice output source offset).val.length = output.val.length := by
  simp [splice]

/-- Copying a fitting source changes exactly its interval and retains all other output bytes. -/
theorem splice_bytes (output source : Slice U8) (offset : Nat)
    (capacity : offset + source.val.length ≤ output.val.length) :
    (splice output source offset).val =
      output.val.take offset ++ source.val ++ output.val.drop (offset + source.val.length) := by
  simp only [splice, List.setSlice!]
  have fits : source.val.length ≤ output.val.length - offset := by omega
  simp [Nat.min_eq_left fits]

/-- Borrowing a suffix, writing its prefix, then returning the borrow is the same exact interval update. -/
theorem suffix_splice (output source : Slice U8) (offset : Nat)
    (capacity : offset + source.val.length ≤ output.val.length) :
    splice output (splice (rangeView output offset output.val.length) source 0) offset =
      splice output source offset := by
  apply Subtype.ext
  have offsetBound : offset ≤ output.val.length := by omega
  have sourceBound : source.val.length ≤ output.val.length - offset := by omega
  have view : (rangeView output offset output.val.length).val = output.val.drop offset := by
    simp [rangeView, List.slice]
  change output.val.setSlice! offset ((rangeView output offset output.val.length).val.setSlice! 0 source.val) =
    output.val.setSlice! offset source.val
  rw [view]
  simp only [List.setSlice!, List.length_drop, Nat.sub_zero, Nat.min_eq_left sourceBound,
    List.take_zero, List.nil_append, List.take_length, Nat.zero_add, List.length_append]
  have remainder : source.val.length + (output.val.length - offset - source.val.length) =
      output.val.length - offset := by omega
  rw [remainder, Nat.min_self]
  have replacementLength : (source.val ++ (output.val.drop offset).drop source.val.length).length =
      output.val.length - offset := by simp only [List.length_append, List.length_drop]; omega
  have takeRest : (source.val ++ (output.val.drop offset).drop source.val.length).take
      (output.val.length - offset) = source.val ++ (output.val.drop offset).drop source.val.length := by
    rw [← replacementLength, List.take_length]
  have outerDrop : output.val.drop (offset + (output.val.length - offset)) = [] :=
    List.drop_eq_nil_of_le (by omega)
  rw [takeRest, outerDrop, List.append_nil, List.drop_drop]
  simp [List.append_assoc]

/-- Consecutive writes append bytes to the completed prefix while preserving the untouched suffix. -/
theorem splice_extend (original output source : Slice U8) (written : List U8)
    (view : output.val = written ++ original.val.drop written.length)
    (capacity : written.length + source.val.length ≤ output.val.length) :
    (splice output source written.length).val =
      (written ++ source.val) ++ original.val.drop (written.length + source.val.length) := by
  rw [splice_bytes output source written.length capacity, view]
  simp [List.drop_append, List.drop_drop]

def tag : Slice U8 := ⟨[133#u8, 1#u8, 2#u8], by scalar_tac⟩

def headerBytes (sequence sender : U64) (payloadLength : Usize) : List U8 :=
  tag.val ++ argumentBytes 0#u8 sequence ++ argumentBytes 0#u8 sender ++
    argumentBytes 2#u8 (UScalar.cast .U64 payloadLength)

/-- Exact successful source header execution, including every borrowed suffix write-back. -/
theorem write_header_steps (sequence sender : U64) (payloadLength length offset1 offset2 offset3 : Usize)
    (output : Slice U8)
    (admitted : _root_.beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = ok (.Some length))
    (firstOffset : 3 + (encoded 0#u8 sequence).length.val = offset1.val)
    (secondOffset : offset1.val + (encoded 0#u8 sender).length.val = offset2.val)
    (thirdOffset : offset2.val + (encoded 2#u8 (UScalar.cast .U64 payloadLength)).length.val = offset3.val)
    (headerCapacity : offset3.val ≤ output.val.length)
    (frameCapacity : length.val ≤ output.val.length) :
    let afterTag := splice output tag 0
    let afterFirst := splice afterTag (argumentSlice 0#u8 sequence) 3
    let afterSecond := splice afterFirst (argumentSlice 0#u8 sender) offset1.val
    let afterThird := splice afterSecond (argumentSlice 2#u8 (UScalar.cast .U64 payloadLength)) offset2.val
    frame.write_header sequence sender payloadLength output = ok (.Some (offset3, length), afterThird) := by
  let afterTag := splice output tag 0
  let afterFirst := splice afterTag (argumentSlice 0#u8 sequence) 3
  let afterSecond := splice afterFirst (argumentSlice 0#u8 sender) offset1.val
  have lengthTag : afterTag.val.length = output.val.length := splice_length _ _ _
  have lengthFirst : afterFirst.val.length = output.val.length := by simp only [afterFirst, splice_length, lengthTag]
  have lengthSecond : afterSecond.val.length = output.val.length := by simp only [afterSecond, splice_length, lengthFirst]
  have tagCapacity : 3 ≤ output.val.length := by omega
  have firstCapacity : 3 + (argumentSlice 0#u8 sequence).val.length ≤ afterTag.val.length := by
    simp only [argumentSlice, argumentBytes_length, lengthTag]; omega
  have secondCapacity : offset1.val + (argumentSlice 0#u8 sender).val.length ≤ afterFirst.val.length := by
    simp only [argumentSlice, argumentBytes_length, lengthFirst]; omega
  have thirdCapacity : offset2.val + (argumentSlice 2#u8 (UScalar.cast .U64 payloadLength)).val.length ≤ afterSecond.val.length := by
    simp only [argumentSlice, argumentBytes_length, lengthSecond]; omega
  have prefixBorrow := prefix_mut_exact output 3#usize (by simpa using tagCapacity)
  have tagCopy := copy_bytes (rangeView output 0 3) tag (by
    rw [rangeView_length output 0 3 tagCapacity]; rfl)
  have suffixFirst := suffix_mut_exact afterTag 3#usize (by simp only [UScalar.ofNatCore_val_eq, lengthTag]; omega)
  have suffixSecond := suffix_mut_exact afterFirst offset1 (by rw [lengthFirst]; omega)
  have suffixThird := suffix_mut_exact afterSecond offset2 (by rw [lengthSecond]; omega)
  have writeFirst := write_argument_exact 0#u8 sequence
    (rangeView afterTag 3 afterTag.val.length) (by
      rw [rangeView_length _ _ _ (by rfl)];
      simp only [argumentSlice, argumentBytes_length] at firstCapacity; omega)
  have writeSecond := write_argument_exact 0#u8 sender
    (rangeView afterFirst offset1.val afterFirst.val.length) (by
      rw [rangeView_length _ _ _ (by rfl)];
      simp only [argumentSlice, argumentBytes_length] at secondCapacity; omega)
  have writeThird := write_argument_exact 2#u8 (UScalar.cast .U64 payloadLength)
    (rangeView afterSecond offset2.val afterSecond.val.length) (by
      rw [rangeView_length _ _ _ (by rfl)];
      simp only [argumentSlice, argumentBytes_length] at thirdCapacity; omega)
  have addFirst := PqxdhRefinement.usize_add_eq 3#usize (encoded 0#u8 sequence).length offset1 (by simpa using firstOffset)
  have addSecond := PqxdhRefinement.usize_add_eq offset1 (encoded 0#u8 sender).length offset2 secondOffset
  have addThird := PqxdhRefinement.usize_add_eq offset2 (encoded 2#u8 (UScalar.cast .U64 payloadLength)).length offset3 thirdOffset
  have enough : ¬ output.len < length := by simpa only [UScalar.lt_equiv, Slice.len_val, Slice.length] using (Nat.not_lt.mpr frameCapacity)
  simp only [frame.write_header, admitted, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.slice.Slice.len, rust_primitives.slice.slice_length, enough, ite_false,
    prefixBorrow]
  dsimp! only
  have nativeTag : (Array.make 3#usize [133#u8, 1#u8, 2#u8]).to_slice = tag := rfl
  have spliceFirst := suffix_splice afterTag (argumentSlice 0#u8 sequence) 3 firstCapacity
  have spliceSecond := suffix_splice afterFirst (argumentSlice 0#u8 sender) offset1.val secondCapacity
  have spliceThird := suffix_splice afterSecond (argumentSlice 2#u8 (UScalar.cast .U64 payloadLength)) offset2.val thirdCapacity
  dsimp only [afterTag, afterFirst, afterSecond] at *
  simp! only [lift, Bind.bind, Aeneas.Std.bind, bind_ok, uncurry, UScalar.ofNatCore_val_eq, nativeTag, tagCopy, suffixFirst, writeFirst,
    addFirst, spliceFirst,
    suffixSecond, writeSecond, addSecond,
    spliceSecond,
    suffixThird, writeThird, addThird,
    spliceThird]

def headerOutput (sequence sender : U64) (payloadLength : Usize) (output : Slice U8) : Slice U8 :=
  let afterTag := splice output tag 0
  let afterFirst := splice afterTag (argumentSlice 0#u8 sequence) 3
  let afterSecond := splice afterFirst (argumentSlice 0#u8 sender)
    (3 + (argumentBytes 0#u8 sequence).length)
  splice afterSecond (argumentSlice 2#u8 (UScalar.cast .U64 payloadLength))
    (3 + (argumentBytes 0#u8 sequence).length + (argumentBytes 0#u8 sender).length)

theorem headerOutput_length (sequence sender : U64) (payloadLength : Usize) (output : Slice U8) :
    (headerOutput sequence sender payloadLength output).val.length = output.val.length := by
  simp only [headerOutput, splice_length]

/-- Header writes preserve exactly the original suffix after the complete canonical header. -/
theorem headerOutput_bytes (sequence sender : U64) (payloadLength : Usize) (output : Slice U8)
    (capacity : (headerBytes sequence sender payloadLength).length ≤ output.val.length) :
    (headerOutput sequence sender payloadLength output).val =
      headerBytes sequence sender payloadLength ++ output.val.drop (headerBytes sequence sender payloadLength).length := by
  let afterTag := splice output tag 0
  let afterFirst := splice afterTag (argumentSlice 0#u8 sequence) 3
  let afterSecond := splice afterFirst (argumentSlice 0#u8 sender)
    (3 + (argumentBytes 0#u8 sequence).length)
  have lengthTag : afterTag.val.length = output.val.length := splice_length _ _ _
  have lengthFirst : afterFirst.val.length = output.val.length := (splice_length _ _ _).trans lengthTag
  have lengthSecond : afterSecond.val.length = output.val.length := (splice_length _ _ _).trans lengthFirst
  have cap : 3 + (argumentBytes 0#u8 sequence).length + (argumentBytes 0#u8 sender).length +
      (argumentBytes 2#u8 (UScalar.cast .U64 payloadLength)).length ≤ output.val.length := by
    simpa only [headerBytes, List.length_append, tag, List.length_cons, List.length_nil] using capacity
  have tagView : afterTag.val = tag.val ++ output.val.drop tag.val.length := by
    simpa only [afterTag, tag, List.length_cons, List.length_nil, List.take_zero, List.nil_append,
      Nat.zero_add] using splice_bytes output tag 0 (by simpa only [tag, List.length_cons, List.length_nil] using (show 3 ≤ output.val.length by omega))
  have firstView := splice_extend output afterTag (argumentSlice 0#u8 sequence) tag.val tagView
    (by rw [lengthTag]; simp only [tag, List.length_cons, List.length_nil, argumentSlice]; omega)
  have secondView := splice_extend output afterFirst (argumentSlice 0#u8 sender)
    (tag.val ++ argumentBytes 0#u8 sequence) (by
      simpa only [afterFirst, tag, List.length_cons, List.length_nil, argumentSlice, List.length_append] using firstView)
    (by rw [lengthFirst]; simp only [List.length_append, tag,
      List.length_cons, List.length_nil, argumentSlice]; omega)
  have thirdView := splice_extend output afterSecond (argumentSlice 2#u8 (UScalar.cast .U64 payloadLength))
    (tag.val ++ argumentBytes 0#u8 sequence ++ argumentBytes 0#u8 sender) (by
      simpa only [afterSecond, tag, List.length_cons, List.length_nil, argumentSlice, List.length_append] using secondView)
    (by rw [lengthSecond]; simp only [List.length_append, tag,
      List.length_cons, List.length_nil, argumentSlice]; omega)
  simpa only [headerOutput, afterSecond, afterFirst, afterTag, headerBytes, argumentSlice,
    List.length_append, tag, List.length_cons, List.length_nil] using thirdView

theorem argument_size (major : U8) (value : U64) (domain : major = 0#u8 ∨ major = 2#u8) :
    (encoded major value).length.val = CborSizing.argumentLen value.val := by
  have size := congrArg List.length (argument_abs major value domain)
  simpa only [List.length_map, argumentBytes_length, CborTransport.argument_length] using size

def offsetOf (value : Nat) : Usize := ⟨BitVec.ofNat _ value⟩

theorem offsetOf_value (value : Nat) (bound : value < 2 ^ 32) : (offsetOf value).val = value :=
  PqxdhRefinement.usize_mk_val value bound

theorem header_size (sequence sender : U64) (payloadLength : Usize) :
    (headerBytes sequence sender payloadLength).length + payloadLength.val =
      CborSizing.frameLen sequence.val sender.val payloadLength.val := by
  simp only [headerBytes, tag, List.length_append, List.length_cons, List.length_nil,
    argumentBytes_length, argument_size 0#u8 sequence (.inl rfl),
    argument_size 0#u8 sender (.inl rfl),
    argument_size 2#u8 (UScalar.cast .U64 payloadLength) (.inr rfl),
    Transport.usize_to_u64_value, CborSizing.frameLen, CborSizing.byteStringLen, Nat.add_assoc]
  omega

theorem admitted_size (sequence sender : U64) (payloadLength length : Usize)
    (admitted : _root_.beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = ok (.Some length)) :
    length.val = (headerBytes sequence sender payloadLength).length + payloadLength.val := by
  obtain ⟨reply, run, size⟩ := TransportSizingBridge.encoded_frame_len_exact sequence sender payloadLength
  have same : reply = .Some length := RustM.ok.inj (run.symm.trans admitted)
  subst reply
  by_cases bound : CborSizing.frameLen sequence.val sender.val payloadLength.val ≤ 33554432
  · have exactSize : length.val = CborSizing.frameLen sequence.val sender.val payloadLength.val := by
      simpa only [Transport.absLength, Transport.messageCap, bound, ite_true, Option.some.injEq] using size
    exact exactSize.trans (header_size sequence sender payloadLength).symm
  · simp only [Transport.absLength, Transport.messageCap, bound, ite_false] at size
    cases size

/-- The actual header writer succeeds with its exact canonical prefix and original trailing destination bytes. -/
theorem write_header_success (sequence sender : U64) (payloadLength length : Usize) (output : Slice U8)
    (admitted : _root_.beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = ok (.Some length))
    (capacity : length.val ≤ output.val.length) :
    ∃ offset,
      frame.write_header sequence sender payloadLength output =
        ok (.Some (offset, length), headerOutput sequence sender payloadLength output) ∧
      offset.val = (headerBytes sequence sender payloadLength).length ∧
      length.val = offset.val + payloadLength.val := by
  let first := (encoded 0#u8 sequence).length.val
  let second := (encoded 0#u8 sender).length.val
  let third := (encoded 2#u8 (UScalar.cast .U64 payloadLength)).length.val
  have firstBound : first ≤ 9 := (argument_length_pos 0#u8 sequence).2
  have secondBound : second ≤ 9 := (argument_length_pos 0#u8 sender).2
  have thirdBound : third ≤ 9 := (argument_length_pos 2#u8 (UScalar.cast .U64 payloadLength)).2
  let offset1 := offsetOf (3 + first)
  let offset2 := offsetOf (3 + first + second)
  let offset3 := offsetOf (3 + first + second + third)
  have firstValue : offset1.val = 3 + first := offsetOf_value _ (by omega)
  have secondValue : offset2.val = 3 + first + second := offsetOf_value _ (by omega)
  have thirdValue : offset3.val = 3 + first + second + third := offsetOf_value _ (by omega)
  have headerLength : (headerBytes sequence sender payloadLength).length = offset3.val := by
    simp only [headerBytes, List.length_append, tag, List.length_cons, List.length_nil,
      argumentBytes_length, thirdValue, first, second, third]
  have size := admitted_size sequence sender payloadLength length admitted
  refine ⟨offset3, ?_, headerLength.symm, ?_⟩
  · have run := write_header_steps sequence sender payloadLength length offset1 offset2 offset3 output admitted
      firstValue.symm (by rw [firstValue, secondValue]) (by rw [secondValue, thirdValue])
      (by omega) capacity
    simpa only [headerOutput, firstValue, secondValue, first, second, argumentBytes_length] using run
  · omega

theorem checked_add_some (left right result : Usize) (sum : left.val + right.val = result.val) :
    core.num.Usize.checked_add left right = ok (.Some result) := by
  obtain ⟨reply, run, size⟩ := Transport.checked_add_exact left right
  have resultBound : result.val ≤ UScalar.max .Usize := by scalar_tac
  have bound : left.val + right.val ≤ UScalar.max .Usize := by omega
  rw [ite_eq_left bound] at size
  cases reply with
  | none => simp only [Transport.absLength] at size
            cases size
  | some actual =>
    have sameValue : actual.val = result.val := by simpa only [Transport.absLength, Option.some.injEq, sum] using size
    have same := PqxdhRefinement.usize_eq_of_val sameValue
    simpa only [same] using run

/-- Exact three-chunk copy loop after the native header succeeded. Every range and write-back is the generated operation. -/
theorem encode_three_steps (sequence sender : U64) (first second third output headerOutput : Slice U8)
    (prefixLength payloadLength offset length endFirst endSecond : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (payloadSum : prefixLength.val + third.val.length = payloadLength.val)
    (headerRun : frame.write_header sequence sender payloadLength output = ok (.Some (offset, length), headerOutput))
    (headerLength : headerOutput.val.length = output.val.length)
    (firstEnd : offset.val + first.val.length = endFirst.val)
    (secondEnd : endFirst.val + second.val.length = endSecond.val)
    (lastEnd : endSecond.val + third.val.length = length.val)
    (capacity : length.val ≤ output.val.length) :
    frame.encode_three sequence sender first second third output =
      ok (length, splice (splice (splice headerOutput first offset.val) second endFirst.val) third endSecond.val) := by
  let afterFirst := splice headerOutput first offset.val
  let afterSecond := splice afterFirst second endFirst.val
  have lengthFirst : afterFirst.val.length = output.val.length := (splice_length _ _ _).trans headerLength
  have lengthSecond : afterSecond.val.length = output.val.length := (splice_length _ _ _).trans lengthFirst
  have addPrefix := checked_add_some first.len second.len prefixLength (by simpa only [Slice.len_val, Slice.length] using prefixSum)
  have addPayload := checked_add_some prefixLength third.len payloadLength (by simpa only [Slice.len_val, Slice.length] using payloadSum)
  have addFirst := PqxdhRefinement.usize_add_eq offset first.len endFirst (by simpa only [Slice.len_val, Slice.length] using firstEnd)
  have addSecond := PqxdhRefinement.usize_add_eq endFirst second.len endSecond (by simpa only [Slice.len_val, Slice.length] using secondEnd)
  have borrowFirst := range_mut_exact headerOutput offset endFirst (by omega) (by omega)
  have borrowSecond := range_mut_exact afterFirst endFirst endSecond (by omega) (by omega)
  have borrowThird := range_mut_exact afterSecond endSecond length (by omega) (by omega)
  have copyFirst := copy_bytes (rangeView headerOutput offset.val endFirst.val) first (by
    rw [rangeView_length _ _ _ (by omega)]; omega)
  have copySecond := copy_bytes (rangeView afterFirst endFirst.val endSecond.val) second (by
    rw [rangeView_length _ _ _ (by omega)]; omega)
  have copyThird := copy_bytes (rangeView afterSecond endSecond.val length.val) third (by
    rw [rangeView_length _ _ _ (by omega)]; omega)
  simp only [frame.encode_three, core.slice.Slice.len, rust_primitives.slice.slice_length,
    addPrefix, addPayload, headerRun, bind_tc_ok]
  dsimp! only
  dsimp only [afterFirst, afterSecond] at *
  simp! only [addFirst, borrowFirst, copyFirst, copySecond, copyThird, addSecond, borrowSecond, borrowThird,
    Bind.bind, Aeneas.Std.bind, bind_ok, uncurry]

/-- Successful execution of the actual flat native writer produces the complete canonical frame in chunk order and preserves all trailing destination bytes. -/
theorem encode_three_success (sequence sender : U64) (first second third payload output : Slice U8)
    (payloadView : payload.val = first.val ++ second.val ++ third.val)
    (admission : (frameBytes sequence sender payload).length ≤ 33554432)
    (capacity : (frameBytes sequence sender payload).length ≤ output.val.length) :
    ∃ length result,
      frame.encode_three sequence sender first second third output = ok (length, result) ∧
      length.val = (frameBytes sequence sender payload).length ∧
      result.val = frameBytes sequence sender payload ++ output.val.drop length.val := by
  have frameView : frameBytes sequence sender payload = headerBytes sequence sender payload.len ++ payload.val := by
    simp only [frameBytes, headerBytes, tag, List.append_assoc]
  have frameSize : (frameBytes sequence sender payload).length =
      CborSizing.frameLen sequence.val sender.val payload.val.length := by
    rw [frameView, List.length_append]
    simpa only [Slice.len_val, Slice.length] using header_size sequence sender payload.len
  have payloadLength : payload.val.length = first.val.length + second.val.length + third.val.length := by
    rw [payloadView, List.length_append, List.length_append]
  obtain ⟨reply, sizeRun, sizeExact⟩ := TransportSizingBridge.encoded_frame_len_exact sequence sender payload.len
  have admitted : CborSizing.frameLen sequence.val sender.val payload.val.length ≤ 33554432 := by omega
  have selected : Transport.absLength reply = some (frameBytes sequence sender payload).length := by
    simpa only [Transport.messageCap, Slice.len_val, Slice.length, admitted, ite_true, frameSize] using sizeExact
  cases reply with
  | none => simp only [Transport.absLength] at selected; cases selected
  | some length =>
    have lengthValue : length.val = (frameBytes sequence sender payload).length := by
      simpa only [Transport.absLength, Option.some.injEq] using selected
    obtain ⟨offset, headerRun, offsetValue, totalLength⟩ :=
      write_header_success sequence sender payload.len length output sizeRun (by omega)
    have size : length.val = offset.val + first.val.length + second.val.length + third.val.length := by
      simp only [Slice.len_val, Slice.length] at totalLength; omega
    have totalBound : length.val ≤ 33554432 := by omega
    let prefixLength := offsetOf (first.val.length + second.val.length)
    let endFirst := offsetOf (offset.val + first.val.length)
    let endSecond := offsetOf (offset.val + first.val.length + second.val.length)
    have prefixValue : prefixLength.val = first.val.length + second.val.length := offsetOf_value _ (by omega)
    have firstValue : endFirst.val = offset.val + first.val.length := offsetOf_value _ (by omega)
    have secondValue : endSecond.val = offset.val + first.val.length + second.val.length := offsetOf_value _ (by omega)
    let afterHeader := headerOutput sequence sender payload.len output
    let afterFirst := splice afterHeader first offset.val
    let afterSecond := splice afterFirst second endFirst.val
    let afterThird := splice afterSecond third endSecond.val
    have headerLength : afterHeader.val.length = output.val.length := headerOutput_length _ _ _ _
    have firstLength : afterFirst.val.length = output.val.length := (splice_length _ _ _).trans headerLength
    have secondLength : afterSecond.val.length = output.val.length := (splice_length _ _ _).trans firstLength
    have headerCapacity : (headerBytes sequence sender payload.len).length ≤ output.val.length := by omega
    have headerBytesView := headerOutput_bytes sequence sender payload.len output headerCapacity
    have firstView := splice_extend output afterHeader first (headerBytes sequence sender payload.len)
      headerBytesView (by rw [headerLength]; omega)
    have secondView := splice_extend output afterFirst second (headerBytes sequence sender payload.len ++ first.val)
      (by simpa only [afterFirst, offsetValue, List.length_append] using firstView)
      (by rw [firstLength, List.length_append]; omega)
    have thirdView := splice_extend output afterSecond third
      (headerBytes sequence sender payload.len ++ first.val ++ second.val)
      (by simpa only [afterSecond, firstValue, offsetValue, List.length_append] using secondView)
      (by rw [secondLength, List.length_append, List.length_append]; omega)
    refine ⟨length, afterThird, ?_, lengthValue, ?_⟩
    · exact encode_three_steps sequence sender first second third output afterHeader
        prefixLength payload.len offset length endFirst endSecond prefixValue.symm
        (by simp only [Slice.len_val, Slice.length]; omega)
        headerRun headerLength firstValue.symm (by omega) (by omega) (by omega)
    · have totalNatural : length.val = (headerBytes sequence sender payload.len).length +
          first.val.length + second.val.length + third.val.length := by omega
      rw [totalNatural]
      simpa only [afterThird, secondValue, offsetValue, List.length_append,
        frameView, payloadView, List.append_assoc, Nat.add_assoc] using thirdView

/-- The complete prefix returned by the actual writer is exactly the existing computational CBOR rendering. -/
theorem encode_three_render (sequence sender : U64) (first second third payload output : Slice U8)
    (payloadView : payload.val = first.val ++ second.val ++ third.val)
    (admission : (frameBytes sequence sender payload).length ≤ 33554432)
    (capacity : (frameBytes sequence sender payload).length ≤ output.val.length) :
    ∃ length result,
      frame.encode_three sequence sender first second third output = ok (length, result) ∧
      length.val = (CborTransport.render ⟨sequence, sender, payload.val.map absByte⟩).length ∧
      (result.val.take length.val).map absByte =
        CborTransport.render ⟨sequence, sender, payload.val.map absByte⟩ := by
  obtain ⟨length, result, run, size, bytes⟩ :=
    encode_three_success sequence sender first second third payload output payloadView admission capacity
  have renderSize := congrArg List.length (frame_abs sequence sender payload)
  simp only [List.length_map] at renderSize
  refine ⟨length, result, run, size.trans renderSize, ?_⟩
  rw [bytes, size, List.take_left' rfl]
  exact frame_abs sequence sender payload

end BeaconcryptCore.Refinement.FrameCodecWriteBytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.clone_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.clone_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.copy_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.copy_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.slice_mut_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.slice_mut_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.range_mut_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.range_mut_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.prefix_mut_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.prefix_mut_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.suffix_mut_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.suffix_mut_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.rangeView_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.rangeView_length

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.prefix_read_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.prefix_read_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.array_prefix_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.array_prefix_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.argumentSlice_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.argumentSlice_view

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_argument_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_argument_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_length

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.suffix_splice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.suffix_splice

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.splice_extend

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_header_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_header_steps

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.headerOutput_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.headerOutput_length

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.headerOutput_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.headerOutput_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.argument_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.argument_size

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.offsetOf_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.offsetOf_value

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.header_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.header_size

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.admitted_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.admitted_size

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_header_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.write_header_success

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.checked_add_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.checked_add_some

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_steps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_steps

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_success

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_render' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriteBytes.encode_three_render
