-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecRepresentation
import BeaconcryptCore.Refinement.FrameCodecTotality

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse PqxdhRefinement
open BeaconcryptCore.Refinement.FrameCodecWord
open BeaconcryptCore.Refinement.FrameCodecArgument

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecCanonical

private theorem toLEBytes_fromLEBytes (bytes : List Byte) :
    (BitVec.fromLEBytes bytes).toLEBytes = bytes := by
  apply List.ext_getElem
  · simp only [BitVec.toLEBytes_length]
    omega
  · intro index leftBound rightBound
    apply (Byte.eq_iff _ _).mpr
    intro bit bitBound
    rw [BitVec.toLEBytes_getElem_testBit _ _ _ leftBound ⟨bitBound, by omega⟩]
    rw [BitVec.fromLEBytes_getElem bytes _ (by omega)]
    simp only [show (8 * index + bit) / 8 = index by omega,
      show (8 * index + bit) % 8 = bit by omega]

private theorem cast_toLEBytes {width other : Nat} (value : BitVec width) (same : width = other) :
    (value.cast same).toLEBytes = value.toLEBytes := by
  cases same
  rfl

private theorem cast_toBEBytes {width other : Nat} (value : BitVec width) (same : width = other) :
    (value.cast same).toBEBytes = value.toBEBytes := by
  cases same
  rfl

private theorem toBEBytes_fromBEBytes (bytes : List Byte) :
    (BitVec.fromBEBytes bytes).toBEBytes = bytes := by
  simp only [BitVec.fromBEBytes, BitVec.toBEBytes, cast_toLEBytes,
    toLEBytes_fromLEBytes, List.reverse_reverse]

/-- Reading any eight bytes and writing the resulting word recovers every original byte. -/
theorem word_from_bytes (bytes : Array U8 8#usize) :
    word (Aeneas.Std.core.num.U64.from_be_bytes bytes) = bytes := by
  have encoded := RustM.ok.inj (word_exact (Aeneas.Std.core.num.U64.from_be_bytes bytes))
  rw [← encoded]
  apply Subtype.ext
  dsimp only [Aeneas.Std.core.num.U64.to_be_bytes, Aeneas.Std.core.num.U64.from_be_bytes]
  rw [cast_toBEBytes, toBEBytes_fromBEBytes]
  simp only [List.map_map, Function.comp_def]
  change bytes.val.map id = bytes.val
  exact List.map_id _

/-- The full native byte-word decoder is injective on its fixed-width input. -/
theorem from_bytes_injective (left right : Array U8 8#usize)
    (same : Aeneas.Std.core.num.U64.from_be_bytes left =
      Aeneas.Std.core.num.U64.from_be_bytes right) : left = right := by
  rw [← word_from_bytes left, ← word_from_bytes right, same]

private def majorOf (byte : U8) : U8 := ⟨byte.bv >>> 5⟩
private def informationOf (byte : U8) : U8 := ⟨byte.bv &&& 31#8⟩

private theorem major_value (byte : U8) : (majorOf byte).val = byte.val / 32 := by
  change (byte.bv >>> 5).toNat = byte.bv.toNat / 32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem information_value (byte : U8) : (informationOf byte).val = byte.val % 32 := by
  change (byte.bv &&& 31#8).toNat = byte.bv.toNat % 32
  rw [BitVec.toNat_and]
  change byte.val &&& 31 = byte.val % 32
  simpa only [Nat.reducePow, Nat.reduceSub] using Nat.and_two_pow_sub_one_eq_mod byte.val 5

private theorem header_recover (byte : U8) :
    header (majorOf byte) (informationOf byte) = byte := by
  apply absByte_injective
  have byteBound : byte.val < 256 := byte.bv.isLt
  rw [FrameCodecRepresentation.header_abs (majorOf byte) (informationOf byte)
    (by rw [major_value]; omega) (by rw [information_value]; omega)]
  rw [major_value, information_value]
  rw [Nat.div_add_mod]
  rfl

private theorem zero_suffix (bytes : List Byte) (padding index : Nat)
    (after : bytes.length ≤ index) :
    (bytes ++ List.replicate padding (0#8))[index]! = 0#8 := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append,
    show ¬ index < bytes.length by omega, ite_false, List.getElem?_replicate]
  split_ifs <;> rfl

private theorem fromLEBytes_upper (bytes : List Byte) (padding : Nat) (positive : 0 < padding) :
    (BitVec.fromLEBytes (bytes ++ List.replicate padding (0#8))).toNat < 2 ^ (8 * bytes.length) := by
  apply (BitVec.toNat_lt_iff_getLsbD_eq_false (8 * bytes.length) (by simp; omega)).mpr
  intro index
  change (BitVec.fromLEBytes (bytes ++ List.replicate padding (0#8))).toNat.testBit
    (8 * bytes.length + index) = false
  rw [← BitVec.getElem!_eq_testBit_toNat, BitVec.fromLEBytes_getElem!]
  rw [zero_suffix bytes padding _ (by omega)]
  exact Byte.testBit_default _

private def fromTwo (first second : U8) : U64 :=
  Aeneas.Std.core.num.U64.from_be_bytes
    (Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, first, second])

private def fromFour (first second third fourth : U8) : U64 :=
  Aeneas.Std.core.num.U64.from_be_bytes
    (Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, first, second, third, fourth])

private theorem from_two_upper (first second : U8) : (fromTwo first second).val ≤ 65535 := by
  unfold fromTwo
  dsimp only [Aeneas.Std.core.num.U64.from_be_bytes, UScalar.val]
  rw [BitVec.toNat_cast]
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast]
  change (BitVec.fromLEBytes ([second.bv, first.bv] ++ List.replicate 6 (0#8))).toNat ≤ 65535
  have bound := fromLEBytes_upper [second.bv, first.bv] 6 (by decide)
  norm_num only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at bound
  omega

private theorem from_four_upper (first second third fourth : U8) :
    (fromFour first second third fourth).val ≤ 4294967295 := by
  unfold fromFour
  dsimp only [Aeneas.Std.core.num.U64.from_be_bytes, UScalar.val]
  rw [BitVec.toNat_cast]
  unfold BitVec.fromBEBytes
  rw [BitVec.toNat_cast]
  change (BitVec.fromLEBytes ([fourth.bv, third.bv, second.bv, first.bv] ++ List.replicate 4 (0#8))).toNat ≤ 4294967295
  have bound := fromLEBytes_upper [fourth.bv, third.bv, second.bv, first.bv] 4 (by decide)
  norm_num only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at bound
  omega

private theorem argument_from_two (major first second : U8)
    (lower : 256 ≤ (fromTwo first second).val) :
    argumentBytes major (fromTwo first second) = [header major 25#u8, first, second] := by
  let value := fromTwo first second
  change 256 ≤ value.val at lower
  have bytes : word value =
      Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, first, second] :=
    word_from_bytes _
  have firstByte : octet value 8 = first := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[6]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have secondByte : octet value 0 = second := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[7]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have notInline : ¬ value ≤ 23#u64 := by change ¬ value.val ≤ 23; omega
  have notByte : ¬ value ≤ 255#u64 := by change ¬ value.val ≤ 255; omega
  have upper : value ≤ 65535#u64 := from_two_upper first second
  change argumentBytes major value = _
  unfold argumentBytes encoded
  simp only [notInline, notByte, upper, ite_false, ite_true]
  change [header major 25#u8, octet value 8, octet value 0] = _
  rw [firstByte, secondByte]

private theorem argument_from_four (major first second third fourth : U8)
    (lower : 65536 ≤ (fromFour first second third fourth).val) :
    argumentBytes major (fromFour first second third fourth) =
      [header major 26#u8, first, second, third, fourth] := by
  let value := fromFour first second third fourth
  change 65536 ≤ value.val at lower
  have bytes : word value =
      Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, first, second, third, fourth] :=
    word_from_bytes _
  have firstByte : octet value 24 = first := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[4]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have secondByte : octet value 16 = second := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[5]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have thirdByte : octet value 8 = third := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[6]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have fourthByte : octet value 0 = fourth := by
    have same := congrArg (fun buffer : Array U8 8#usize => buffer.val[7]!) bytes
    simpa only [word, Array.make, List.getElem!_cons_succ, List.getElem!_cons_zero] using same
  have notInline : ¬ value ≤ 23#u64 := by change ¬ value.val ≤ 23; omega
  have notByte : ¬ value ≤ 255#u64 := by change ¬ value.val ≤ 255; omega
  have notTwo : ¬ value ≤ 65535#u64 := by change ¬ value.val ≤ 65535; omega
  have upper : value ≤ 4294967295#u64 := from_four_upper first second third fourth
  change argumentBytes major value = _
  unfold argumentBytes encoded
  simp only [notInline, notByte, notTwo, upper, ite_false, ite_true]
  change [header major 26#u8, octet value 24, octet value 16, octet value 8, octet value 0] = _
  rw [firstByte, secondByte, thirdByte, fourthByte]

private theorem argument_from_eight (major : U8) (bytes : Array U8 8#usize)
    (lower : 4294967296 ≤ (Aeneas.Std.core.num.U64.from_be_bytes bytes).val) :
    argumentBytes major (Aeneas.Std.core.num.U64.from_be_bytes bytes) =
      header major 27#u8 :: bytes.val := by
  let value := Aeneas.Std.core.num.U64.from_be_bytes bytes
  change 4294967296 ≤ value.val at lower
  have notInline : ¬ value ≤ 23#u64 := by change ¬ value.val ≤ 23; omega
  have notByte : ¬ value ≤ 255#u64 := by change ¬ value.val ≤ 255; omega
  have notTwo : ¬ value ≤ 65535#u64 := by change ¬ value.val ≤ 65535; omega
  have notFour : ¬ value ≤ 4294967295#u64 := by change ¬ value.val ≤ 4294967295; omega
  change argumentBytes major value = _
  unfold argumentBytes encoded
  simp only [notInline, notByte, notTwo, notFour, ite_false]
  change header major 27#u8 :: (word value).val = _
  rw [word_from_bytes]

private def fromByte (byte : U8) : U64 := ⟨byte.bv.setWidth 64⟩

private theorem from_byte_value (byte : U8) : (fromByte byte).val = byte.val := by
  change (byte.bv.setWidth 64).toNat = byte.bv.toNat
  exact BitVec.toNat_setWidth_of_le (by decide)

private theorem from_byte_back (byte : U8) :
    (⟨(fromByte byte).bv.setWidth 8⟩ : U8) = byte := by
  change (⟨(byte.bv.setWidth 64).setWidth 8⟩ : U8) = byte
  rw [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide)]
  rfl

private theorem argument_from_byte (major byte : U8) (lower : 24 ≤ byte.val) :
    argumentBytes major (fromByte byte) = [header major 24#u8, byte] := by
  have upper : (fromByte byte).val ≤ 255 := by rw [from_byte_value]; have bound : byte.val < 256 := byte.bv.isLt; omega
  have notInline : ¬ fromByte byte ≤ 23#u64 := by
    change ¬ (fromByte byte).val ≤ 23
    rw [from_byte_value]
    omega
  unfold argumentBytes encoded
  simp only [notInline, show fromByte byte ≤ 255#u64 from upper, ite_false, ite_true]
  change [header major 24#u8, ⟨((fromByte byte).bv >>> 0).setWidth 8⟩] = _
  simp only [BitVec.ushiftRight_zero, from_byte_back]

private theorem argument_from_inline (major byte : U8) (upper : byte.val ≤ 23) :
    argumentBytes major (fromByte byte) = [header major byte] := by
  have small : fromByte byte ≤ 23#u64 := by change (fromByte byte).val ≤ 23; rw [from_byte_value]; exact upper
  unfold argumentBytes encoded
  simp only [small, ite_true]
  change [header major ⟨(fromByte byte).bv.setWidth 8⟩] = _
  rw [from_byte_back]

private theorem take_indices (bytes : List U8) (count : Nat) (bound : count ≤ bytes.length) :
    bytes.take count = (List.range count).map (fun index => bytes[index]!) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.take_succ_eq_append_getElem (by omega), ih (by omega), List.range_succ,
      List.map_append, List.map_singleton, getElem!_pos bytes count (by omega)]

private theorem slice_index_exact (input : Slice U8) (index : Usize)
    (bound : index.val < input.val.length) :
    Slice.index_usize input index = ok input.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem bound,
    getElem!_pos input.val index.val bound]

private theorem shift_five (byte : U8) : byte >>> 5#i32 = ok (majorOf byte) := rfl

private theorem mask_five (byte : U8) : lift (byte &&& 31#u8) = ok (informationOf byte) := rfl

private theorem decode_argument_prefix (input : Slice U8) (major : U8) (value : U64) (used : Usize)
    (decoded : frame.decode_argument input major = ok (.Some (value, used))) :
    input.val.take used.val = argumentBytes major value := by
  unfold frame.decode_argument at decoded
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_tc_ok] at decoded
  by_cases empty : input.len = 0#usize
  · simp only [empty, decide_true, ite_true] at decoded
    cases decoded
  · simp only [empty, decide_false, Bool.false_eq_true, ite_false] at decoded
    have nonempty : 0 < input.val.length := by
      have unequal : input.len.val ≠ 0 := by
        intro zero
        apply empty
        apply UScalar.eq_of_val_eq
        simpa only [UScalar.ofNatCore_val_eq] using zero
      simpa only [Slice.len_val, Slice.length] using Nat.pos_of_ne_zero unequal
    rw [slice_index_exact input 0#usize (by norm_num; omega)] at decoded
    simp only [bind_tc_ok, shift_five, UScalar.ofNatCore_val_eq] at decoded
    split at decoded
    · cases decoded
    · rename_i headerMatch
      simp only [bne_iff_ne, ne_eq, not_not] at headerMatch
      simp only [mask_five, bind_tc_ok] at decoded
      split at decoded
      · rename_i small
        simp only [CoreModels.core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok] at decoded
        have pair := _root_.Option.some.inj (RustM.ok.inj decoded)
        have values := Prod.mk.inj pair
        rcases values with ⟨rfl, rfl⟩
        change input.val.take 1 = argumentBytes major (fromByte (informationOf input.val[0]!))
        rw [argument_from_inline _ _ small, ← headerMatch, header_recover]
        exact take_indices input.val 1 (by omega)
      · split at decoded
        · rename_i information infoValue
          split at decoded
          · cases decoded
          · rename_i fits
            have width : 2 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            split at decoded
            · rename_i lower
              simp only [CoreModels.core.U64.Insts.CoreConvertFromU8.from, bind_tc_ok] at decoded
              have pair := _root_.Option.some.inj (RustM.ok.inj decoded)
              rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
              change input.val.take 2 = argumentBytes major (fromByte input.val[1]!)
              rw [argument_from_byte _ _ lower]
              have recovered := header_recover input.val[0]!
              rw [headerMatch, infoValue] at recovered
              change header major 24#u8 = input.val[0]! at recovered
              rw [recovered]
              exact take_indices input.val 2 width
            · cases decoded
        · rename_i information infoValue
          split at decoded
          · cases decoded
          · rename_i fits
            have width : 3 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 2#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok] at decoded
            split at decoded
            · rename_i lower
              have pair := _root_.Option.some.inj (RustM.ok.inj decoded)
              rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
              change input.val.take 3 = argumentBytes major (fromTwo input.val[1]! input.val[2]!)
              rw [argument_from_two _ _ _ lower]
              have recovered := header_recover input.val[0]!
              rw [headerMatch, infoValue] at recovered
              change header major 25#u8 = input.val[0]! at recovered
              rw [recovered]
              exact take_indices input.val 3 width
            · cases decoded
        · rename_i information infoValue
          split at decoded
          · cases decoded
          · rename_i fits
            have width : 5 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 2#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 3#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 4#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok] at decoded
            split at decoded
            · rename_i lower
              have pair := _root_.Option.some.inj (RustM.ok.inj decoded)
              rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
              change input.val.take 5 = argumentBytes major (fromFour input.val[1]! input.val[2]! input.val[3]! input.val[4]!)
              rw [argument_from_four _ _ _ _ _ lower]
              have recovered := header_recover input.val[0]!
              rw [headerMatch, infoValue] at recovered
              change header major 26#u8 = input.val[0]! at recovered
              rw [recovered]
              exact take_indices input.val 5 width
            · cases decoded
        · rename_i information infoValue
          split at decoded
          · cases decoded
          · rename_i fits
            have width : 9 ≤ input.val.length := by
              simp only [UScalar.lt_equiv, Slice.len_val, Slice.length] at fits
              norm_num at fits
              omega
            rw [slice_index_exact input 1#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 2#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 3#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 4#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 5#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 6#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 7#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            rw [slice_index_exact input 8#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, UScalar.ofNatCore_val_eq] at decoded
            simp only [CoreModels.core.num.U64.from_be_bytes,
              CoreModels.rust_primitives.arithmetic.from_be_bytes_u64, bind_tc_ok] at decoded
            split at decoded
            · rename_i lower
              have pair := _root_.Option.some.inj (RustM.ok.inj decoded)
              rcases Prod.mk.inj pair with ⟨rfl, rfl⟩
              rw [argument_from_eight _ _ lower]
              have recovered := header_recover input.val[0]!
              rw [headerMatch, infoValue] at recovered
              change header major 27#u8 = input.val[0]! at recovered
              rw [recovered]
              exact take_indices input.val 9 width
            · cases decoded
        · cases decoded

/-- Every successful execution of the actual decoder consumes exactly the encoder's canonical argument prefix. -/
theorem decode_argument_canonical (input : Slice U8) (major : U8) (value : U64) (used : Usize)
    (decoded : frame.decode_argument input major = ok (.Some (value, used))) :
    input.val.take used.val = argumentBytes major value ∧ used = (encoded major value).length := by
  have canonical := decode_argument_prefix input major value used decoded
  obtain ⟨reply, normal, valid⟩ := FrameCodecTotality.decode_argument_total input major
  have same := RustM.ok.inj (normal.symm.trans decoded)
  rw [same] at valid
  change 1 ≤ used.val ∧ used.val ≤ input.val.length at valid
  refine ⟨canonical, UScalar.eq_of_val_eq ?_⟩
  have lengths := congrArg List.length canonical
  simpa only [List.length_take, Nat.min_eq_left valid.2, argumentBytes_length] using lengths

end BeaconcryptCore.Refinement.FrameCodecCanonical

/-- info: 'BeaconcryptCore.Refinement.FrameCodecCanonical.word_from_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecCanonical.word_from_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecCanonical.from_bytes_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecCanonical.from_bytes_injective

/-- info: 'BeaconcryptCore.Refinement.FrameCodecCanonical.decode_argument_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecCanonical.decode_argument_canonical
