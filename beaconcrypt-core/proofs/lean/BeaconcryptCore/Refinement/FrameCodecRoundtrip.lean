-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecArgument

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecRoundtrip

open BeaconcryptCore.Refinement.FrameCodecArgument

def suffix (input : Slice U8) (offset : Nat) : Slice U8 :=
  ⟨input.val.drop offset, by have := input.property; simp only [List.length_drop]; omega⟩

/-- Native range indexing consumes exactly the selected prefix and preserves the remaining bytes. -/
theorem suffix_exact (input : Slice U8) (offset : Usize) (bound : offset.val ≤ input.val.length) :
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice U8)
      input { start := offset } = ok (suffix input offset.val) := by
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, UScalar.le_equiv, Slice.length,
    rust_primitives.slice.slice_slice, Slice.subslice]
  simp only [bind_tc_ok, Slice.len_val, Slice.length, bound, ite_true, le_refl, and_self]
  simp only [Bind.bind, Aeneas.Std.bind]
  congr 1
  apply Subtype.ext
  simp [List.slice, suffix]

/-- Composition of the actual decoder: complete header, three successful canonical arguments, then exact payload consumption. -/
theorem decode_components_result (input payload first second third : Slice U8)
    (sequence sender length : U64) (usedFirst usedSecond usedThird : Usize)
    (size : input.val.length ≤ 33554432)
    (header : input.val = [133#u8, 1#u8, 2#u8] ++ first.val)
    (firstRead : frame.decode_argument first 0#u8 = ok (.Some (sequence, usedFirst)))
    (secondRead : frame.decode_argument second 0#u8 = ok (.Some (sender, usedSecond)))
    (thirdRead : frame.decode_argument third 2#u8 = ok (.Some (length, usedThird)))
    (firstBound : usedFirst.val ≤ first.val.length)
    (secondBound : usedSecond.val ≤ second.val.length)
    (thirdBound : usedThird.val ≤ third.val.length)
    (firstRest : first.val.drop usedFirst.val = second.val)
    (secondRest : second.val.drop usedSecond.val = third.val)
    (thirdRest : third.val.drop usedThird.val = payload.val) :
    frame.decode input =
      if length != UScalar.cast .U64 payload.len then ok .None
      else ok (.Some ⟨sequence, sender, payload⟩) := by
  have minimum : 3 ≤ input.val.length := by rw [header]; simp
  have notLarge : ¬ input.len > (33554432#usize) := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, Std.UScalar.ofNatCore_val_eq]
    omega
  have notShort : ¬ input.len < (3#usize) := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, Std.UScalar.ofNatCore_val_eq]
    omega
  have byte0 : Slice.index_usize input 0#usize = ok (133#u8) := by
    simp [Slice.index_usize, header]
  have byte1 : Slice.index_usize input 1#usize = ok (1#u8) := by
    simp [Slice.index_usize, header]
  have byte2 : Slice.index_usize input 2#usize = ok (2#u8) := by
    simp [Slice.index_usize, header]
  simp only [frame.decode, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE,
    _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE, bind_tc_ok,
    notLarge, notShort, byte0, byte1, byte2, ite_false, bne_self_eq_false, Bool.false_eq_true]
  have zeroRest : suffix input 3 = first := by
    apply Subtype.ext
    simp [suffix, header]
  have firstSuffix : suffix first usedFirst.val = second := Subtype.ext firstRest
  have secondSuffix : suffix second usedSecond.val = third := Subtype.ext secondRest
  have thirdSuffix : suffix third usedThird.val = payload := Subtype.ext thirdRest
  have cut0 := suffix_exact input (3#usize) (by simpa only [UScalar.ofNatCore_val_eq] using minimum)
  have cut1 := suffix_exact first usedFirst firstBound
  have cut2 := suffix_exact second usedSecond secondBound
  have cut3 := suffix_exact third usedThird thirdBound
  rw [show (3#usize).val = 3 from rfl, zeroRest] at cut0
  rw [firstSuffix] at cut1
  rw [secondSuffix] at cut2
  rw [thirdSuffix] at cut3
  simp! only [cut0, cut1, cut2, cut3, firstRead, secondRead, thirdRead,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok, lift,
    bne_self_eq_false, Bool.false_eq_true, ite_false]

/-- Successful whole-frame decoding requires the exact declared payload length. -/
theorem decode_components (input payload first second third : Slice U8)
    (sequence sender length : U64) (usedFirst usedSecond usedThird : Usize)
    (size : input.val.length ≤ 33554432)
    (header : input.val = [133#u8, 1#u8, 2#u8] ++ first.val)
    (firstRead : frame.decode_argument first 0#u8 = ok (.Some (sequence, usedFirst)))
    (secondRead : frame.decode_argument second 0#u8 = ok (.Some (sender, usedSecond)))
    (thirdRead : frame.decode_argument third 2#u8 = ok (.Some (length, usedThird)))
    (firstBound : usedFirst.val ≤ first.val.length)
    (secondBound : usedSecond.val ≤ second.val.length)
    (thirdBound : usedThird.val ≤ third.val.length)
    (firstRest : first.val.drop usedFirst.val = second.val)
    (secondRest : second.val.drop usedSecond.val = third.val)
    (thirdRest : third.val.drop usedThird.val = payload.val)
    (lengthExact : length = UScalar.cast .U64 payload.len) :
    frame.decode input = ok (.Some ⟨sequence, sender, payload⟩) := by
  rw [decode_components_result input payload first second third sequence sender length
    usedFirst usedSecond usedThird size header firstRead secondRead thirdRead
    firstBound secondBound thirdBound firstRest secondRest thirdRest, lengthExact]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]

/-- Oversized complete messages reject before any field or payload is accessed. -/
theorem decode_oversize (input : Slice U8) (large : 33554432 < input.val.length) :
    frame.decode input = ok .None := by
  have tooLarge : input.len > (33554432#usize) := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
    omega
  simp only [frame.decode, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE,
    _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE, bind_tc_ok, tooLarge, ite_true]

/-- A truncated fixed header rejects before any indexing can panic. -/
theorem decode_short (input : Slice U8) (short : input.val.length < 3) :
    frame.decode input = ok .None := by
  have notLarge : ¬ input.len > (33554432#usize) := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
    omega
  have tooShort : input.len < (3#usize) := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
    omega
  simp only [frame.decode, core.slice.Slice.len, rust_primitives.slice.slice_length,
    beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE,
    _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE, bind_tc_ok, notLarge, tooShort, ite_true, ite_false]

/-- The whole native frame decoder recovers its canonical metadata and payload once the actual scalar inverse is supplied. -/
theorem decode_roundtrip_of_arguments
    (argumentDecoder : ∀ (major : U8) (value : U64), (major = 0#u8 ∨ major = 2#u8) →
      ∀ (input : Slice U8) (rest : List U8), input.val = argumentBytes major value ++ rest →
        frame.decode_argument input major = ok (.Some (value, (encoded major value).length)))
    (input payload : Slice U8) (sequence sender : U64)
    (size : input.val.length ≤ 33554432)
    (view : input.val = [133#u8, 1#u8, 2#u8] ++ argumentBytes 0#u8 sequence ++
      argumentBytes 0#u8 sender ++ argumentBytes 2#u8 (UScalar.cast .U64 payload.len) ++ payload.val) :
    frame.decode input = ok (.Some ⟨sequence, sender, payload⟩) := by
  let length := UScalar.cast .U64 payload.len
  let first := suffix input 3
  let second := suffix first (encoded 0#u8 sequence).length.val
  let third := suffix second (encoded 0#u8 sender).length.val
  have firstView : first.val = argumentBytes 0#u8 sequence ++
      (argumentBytes 0#u8 sender ++ argumentBytes 2#u8 length ++ payload.val) := by
    simp [first, suffix, view, length, List.append_assoc]
  have secondView : second.val = argumentBytes 0#u8 sender ++
      (argumentBytes 2#u8 length ++ payload.val) := by
    simp [second, suffix, firstView, ← argumentBytes_length]
  have thirdView : third.val = argumentBytes 2#u8 length ++ payload.val := by
    simp [third, suffix, secondView, ← argumentBytes_length]
  apply decode_components input payload first second third sequence sender length
    (encoded 0#u8 sequence).length (encoded 0#u8 sender).length (encoded 2#u8 length).length size
  · simpa only [firstView, List.append_assoc, length] using view
  · exact argumentDecoder 0#u8 sequence (Or.inl rfl) first _ firstView
  · exact argumentDecoder 0#u8 sender (Or.inl rfl) second _ secondView
  · exact argumentDecoder 2#u8 length (Or.inr rfl) third _ thirdView
  · simp only [firstView, List.length_append, argumentBytes_length]; omega
  · simp only [secondView, List.length_append, argumentBytes_length]; omega
  · simp only [thirdView, List.length_append, argumentBytes_length]; omega
  · rfl
  · rfl
  · simp [thirdView, ← argumentBytes_length]
  · rfl

/-- The actual native decoder reads canonical encoder arguments and the complete payload, with no codec premise. -/
theorem decode_roundtrip (input payload : Slice U8) (sequence sender : U64)
    (size : input.val.length ≤ 33554432)
    (view : input.val = [133#u8, 1#u8, 2#u8] ++ argumentBytes 0#u8 sequence ++
      argumentBytes 0#u8 sender ++ argumentBytes 2#u8 (UScalar.cast .U64 payload.len) ++ payload.val) :
    frame.decode input = ok (.Some ⟨sequence, sender, payload⟩) := by
  exact decode_roundtrip_of_arguments decode_argument_roundtrip input payload sequence sender size view

end BeaconcryptCore.Refinement.FrameCodecRoundtrip

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.suffix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.suffix_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_components_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_components_result

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_components

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_oversize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_oversize

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_short' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_short

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_roundtrip_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_roundtrip_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecRoundtrip.decode_roundtrip
