-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecWord
import BeaconcryptCore.Refinement.FrameCodecEndian
import BeaconcryptCore.Refinement.PqxdhBytes

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse
open BeaconcryptCore.Refinement.FrameCodecWord

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecArgument

def header (major information : U8) : U8 := ⟨major.bv <<< 5 ||| information.bv⟩

def encoded (major : U8) (value : U64) : frame.Argument :=
  if value ≤ 23#u64 then
    ⟨⟨[header major ⟨value.bv.setWidth 8⟩, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8], by simp⟩, 1#usize⟩
  else if value ≤ 255#u64 then
    ⟨⟨[header major 24#u8, octet value 0, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8], by simp⟩, 2#usize⟩
  else if value ≤ 65535#u64 then
    ⟨⟨[header major 25#u8, octet value 8, octet value 0, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8], by simp⟩, 3#usize⟩
  else if value ≤ 4294967295#u64 then
    ⟨⟨[header major 26#u8, octet value 24, octet value 16, octet value 8, octet value 0, 0#u8, 0#u8, 0#u8, 0#u8], by simp⟩, 5#usize⟩
  else
    ⟨⟨[header major 27#u8, octet value 56, octet value 48, octet value 40, octet value 32,
      octet value 24, octet value 16, octet value 8, octet value 0], by simp⟩, 9#usize⟩

def argumentBytes (major : U8) (value : U64) : List U8 :=
  (encoded major value).bytes.val.take (encoded major value).length.val

/-- Each canonical argument uses between one and nine bytes of its fixed buffer. -/
theorem argument_length_pos (major : U8) (value : U64) :
    1 ≤ (encoded major value).length.val ∧ (encoded major value).length.val ≤ 9 := by
  unfold encoded
  split_ifs <;> norm_num

/-- The used buffer prefix has exactly the length returned by the native encoder. -/
theorem argumentBytes_length (major : U8) (value : U64) :
    (argumentBytes major value).length = (encoded major value).length.val := by
  unfold argumentBytes encoded
  split_ifs <;> simp

private theorem shift_five (major : U8) :
    major <<< 5#i32 = ok (⟨major.bv <<< 5⟩ : U8) := rfl

private theorem lift_or (left right : U8) :
    lift (left ||| right) = ok (⟨left.bv ||| right.bv⟩ : U8) := rfl

private theorem lift_cast (value : U64) :
    lift (UScalar.cast .U8 value) = ok (⟨value.bv.setWidth 8⟩ : U8) := rfl

/-- The concrete generated encoder returns the canonical fixed buffer and its exact used length. -/
theorem encode_argument_exact (major : U8) (value : U64) :
    frame.encode_argument major value = ok (encoded major value) := by
  unfold frame.encode_argument
  rw [word_exact]
  simp only [bind_tc_ok, shift_five, lift_or, lift_cast]
  simp only [
    PqxdhRefinement.index_usize_eq (word value) 0#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 1#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 2#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 3#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 4#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 5#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 6#usize (by decide),
    PqxdhRefinement.index_usize_eq (word value) 7#usize (by decide),
    bind_tc_ok]
  unfold encoded
  split_ifs <;> rfl

private theorem shift_five_right (byte : U8) :
    byte >>> 5#i32 = ok (⟨byte.bv >>> 5⟩ : U8) := rfl

private theorem lift_and (left right : U8) :
    lift (left &&& right) = ok (⟨left.bv &&& right.bv⟩ : U8) := rfl

private theorem from_u8 (byte : U8) :
    CoreModels.core.U64.Insts.CoreConvertFromU8.from byte =
      ok (⟨byte.bv.setWidth 64⟩ : U64) := rfl

private theorem header_parts (major information : BitVec 8)
    (majorBound : major.toNat ≤ 7) (informationBound : information.toNat ≤ 31) :
    ((major <<< 5 ||| information) >>> 5) = major ∧
      ((major <<< 5 ||| information) &&& 31#8) = information := by
  have majorHigh : ∀ k, major.getLsbD (3 + k) = false :=
    (BitVec.toNat_lt_iff_getLsbD_eq_false 3 (by decide)).mp (by omega)
  have informationHigh : ∀ k, information.getLsbD (5 + k) = false :=
    (BitVec.toNat_lt_iff_getLsbD_eq_false 5 (by decide)).mp (by omega)
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases low : i < 3
    · simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, show 5 + i < 8 by omega,
        show ¬ 5 + i < 5 by omega, decide_true, decide_false,
        Bool.not_false, Bool.true_and, informationHigh, Bool.or_false]
      congr 1
      omega
    · have high : major.getLsbD i = false := by
        simpa [show 3 + (i - 3) = i by omega] using majorHigh (i - 3)
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, show ¬ 5 + i < 8 by omega,
        decide_false, Bool.false_and, informationHigh, Bool.false_or, high]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have mask : (31#8) = (BitVec.allOnes 5).setWidth 8 := by decide
    by_cases low : i < 5
    · simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        mask, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hi, low,
        decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.false_or, Bool.and_true]
    · have high : information.getLsbD i = false := by
        simpa [show 5 + (i - 5) = i by omega] using informationHigh (i - 5)
      simp only [BitVec.getLsbD_and, mask, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_allOnes, hi, low, high, decide_true, decide_false,
        Bool.and_false]

private theorem small_cast (bits : BitVec 64) (bound : bits ≤ 23#64) :
    (bits.setWidth 8).setWidth 64 = bits := by
  apply BitVec.setWidth_setWidth_eq_self
  change bits.toNat < 256
  change bits.toNat ≤ 23 at bound
  omega

private theorem small_bits (bits : BitVec 64) (bound : bits.toNat ≤ 23) :
    (bits.setWidth 8).setWidth 64 = bits ∧
      (bits.setWidth 8).toNat ≤ 23 := by
  constructor
  · exact small_cast bits bound
  · change bits.toNat % 256 ≤ 23
    exact (Nat.mod_le _ _).trans bound

private theorem slice_index_view (input : Slice U8) (bytes : List U8)
    (index : Usize) (byte : U8) (view : input.val = bytes)
    (found : bytes[index.val]? = some byte) :
    Slice.index_usize input index = ok byte := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, view, found]

private theorem header_shift (major information : U8)
    (majorBound : major.val ≤ 7) (informationBound : information.val ≤ 31) :
    header major information >>> 5#i32 = ok major := by
  rw [shift_five_right]
  apply congrArg ok
  apply U8.bv_eq_imp_eq
  exact (header_parts major.bv information.bv majorBound informationBound).1

private theorem header_and (major information : U8)
    (majorBound : major.val ≤ 7) (informationBound : information.val ≤ 31) :
    lift (header major information &&& 31#u8) = ok information := by
  rw [lift_and]
  apply congrArg ok
  apply U8.bv_eq_imp_eq
  exact (header_parts major.bv information.bv majorBound informationBound).2

private theorem slice_nonempty (input : Slice U8) (head : U8) (tail : List U8)
    (view : input.val = head :: tail) :
    CoreModels.core.slice.Slice.is_empty input = ok false := by
  simp only [CoreModels.core.slice.Slice.is_empty, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_tc_ok]
  have nonzero : input.len ≠ 0#usize := by
    intro zero
    have values := congrArg (fun x : Usize => x.val) zero
    simp only [Slice.len_val, Slice.length, view, List.length_cons, UScalar.ofNatCore_val_eq] at values
    omega
  simp only [nonzero, decide_false]

private theorem decode_inline (major : U8) (value : U64) (majorBound : major.val ≤ 7)
    (small : value.val ≤ 23) (input : Slice U8) (suffix : List U8)
    (view : input.val = header major ⟨value.bv.setWidth 8⟩ :: suffix) :
    frame.decode_argument input major = ok (.Some (value, 1#usize)) := by
  let information : U8 := ⟨value.bv.setWidth 8⟩
  have infoSmall : information ≤ 23#u8 := (small_bits value.bv small).2
  have infoBound : information.val ≤ 31 := by
    change (value.bv.setWidth 8).toNat ≤ 31
    exact (small_bits value.bv small).2.trans (by decide)
  have converted : CoreModels.core.U64.Insts.CoreConvertFromU8.from information = ok value := by
    rw [from_u8]
    apply congrArg ok
    apply U64.bv_eq_imp_eq
    exact (small_bits value.bv small).1
  have first := slice_index_view input _ 0#usize (header major information) view (by rfl)
  simp only [frame.decode_argument, slice_nonempty input (header major information) suffix view,
    Bool.false_eq_true, ite_false, bind_tc_ok, first, header_shift major information majorBound infoBound,
    bne_self_eq_false, header_and major information majorBound infoBound, infoSmall, ite_true, converted]

private theorem byte_value (value : U64) (small : value.val ≤ 255) :
    (octet value 0).val = value.val := by
  change value.bv.toNat % 256 = value.bv.toNat
  exact Nat.mod_eq_of_lt (by change value.bv.toNat ≤ 255 at small; omega)

private theorem byte_convert (value : U64) (small : value.val ≤ 255) :
    CoreModels.core.U64.Insts.CoreConvertFromU8.from (octet value 0) = ok value := by
  rw [from_u8]
  apply congrArg ok
  apply U64.bv_eq_imp_eq
  simp only [octet, BitVec.ushiftRight_zero]
  apply BitVec.setWidth_setWidth_eq_self
  change value.bv.toNat < 256
  change value.bv.toNat ≤ 255 at small
  omega

private theorem decode_byte (major : U8) (value : U64) (majorBound : major.val ≤ 7)
    (lower : 24 ≤ value.val) (upper : value.val ≤ 255) (input : Slice U8) (suffix : List U8)
    (view : input.val = header major 24#u8 :: octet value 0 :: suffix) :
    frame.decode_argument input major = ok (.Some (value, 2#usize)) := by
  have first := slice_index_view input _ 0#usize (header major 24#u8) view (by rfl)
  have second := slice_index_view input _ 1#usize (octet value 0) view (by rfl)
  have size : ¬ input.len < 2#usize := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, view,
      List.length_cons, UScalar.ofNatCore_val_eq]
    omega
  have admitted : 24#u8 ≤ octet value 0 := by
    change 24 ≤ (octet value 0).val
    rw [byte_value value upper]
    exact lower
  simp only [frame.decode_argument,
    slice_nonempty input (header major 24#u8) (octet value 0 :: suffix) view,
    Bool.false_eq_true, ite_false, bind_tc_ok, first,
    header_shift major 24#u8 majorBound (by decide), bne_self_eq_false,
    header_and major 24#u8 majorBound (by decide)]
  simp only [show ¬ 24#u8 ≤ 23#u8 from by decide, ite_false]
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok, size, ite_false, second, admitted, ite_true, byte_convert value upper]
  rfl

private theorem decode_two (major : U8) (value : U64) (a b : U8)
    (majorBound : major.val ≤ 7) (lower : 256 ≤ value.val)
    (input : Slice U8) (suffix : List U8)
    (view : input.val = header major 25#u8 :: a :: b :: suffix)
    (decoded : CoreModels.core.num.U64.from_be_bytes
      (Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, a, b]) = ok value) :
    frame.decode_argument input major = ok (.Some (value, 3#usize)) := by
  have first := slice_index_view input _ 0#usize (header major 25#u8) view (by rfl)
  have index1 := slice_index_view input _ 1#usize a view (by rfl)
  have index2 := slice_index_view input _ 2#usize b view (by rfl)
  have size : ¬ input.len < 3#usize := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, view,
      List.length_cons, UScalar.ofNatCore_val_eq]
    omega
  have admitted : 256#u64 ≤ value := lower
  simp only [frame.decode_argument,
    slice_nonempty input (header major 25#u8) (a :: b :: suffix) view,
    Bool.false_eq_true, ite_false, bind_tc_ok, first,
    header_shift major 25#u8 majorBound (by decide), bne_self_eq_false,
    header_and major 25#u8 majorBound (by decide)]
  simp only [show ¬ 25#u8 ≤ 23#u8 from by decide, ite_false]
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok, size, ite_false, index1, index2, decoded, admitted, ite_true]
  rfl

private theorem decode_four (major : U8) (value : U64) (a b c d : U8)
    (majorBound : major.val ≤ 7) (lower : 65536 ≤ value.val)
    (input : Slice U8) (suffix : List U8)
    (view : input.val = header major 26#u8 :: a :: b :: c :: d :: suffix)
    (decoded : CoreModels.core.num.U64.from_be_bytes
      (Array.make 8#usize [0#u8, 0#u8, 0#u8, 0#u8, a, b, c, d]) = ok value) :
    frame.decode_argument input major = ok (.Some (value, 5#usize)) := by
  have first := slice_index_view input _ 0#usize (header major 26#u8) view (by rfl)
  have index1 := slice_index_view input _ 1#usize a view (by rfl)
  have index2 := slice_index_view input _ 2#usize b view (by rfl)
  have index3 := slice_index_view input _ 3#usize c view (by rfl)
  have index4 := slice_index_view input _ 4#usize d view (by rfl)
  have size : ¬ input.len < 5#usize := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, view,
      List.length_cons, UScalar.ofNatCore_val_eq]
    omega
  have admitted : 65536#u64 ≤ value := lower
  simp only [frame.decode_argument,
    slice_nonempty input (header major 26#u8) (a :: b :: c :: d :: suffix) view,
    Bool.false_eq_true, ite_false, bind_tc_ok, first,
    header_shift major 26#u8 majorBound (by decide), bne_self_eq_false,
    header_and major 26#u8 majorBound (by decide)]
  simp only [show ¬ 26#u8 ≤ 23#u8 from by decide, ite_false]
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok, size, ite_false, index1, index2, index3, index4, decoded, admitted, ite_true]
  rfl

private theorem decode_eight (major : U8) (value : U64) (a b c d e f g h : U8)
    (majorBound : major.val ≤ 7) (lower : 4294967296 ≤ value.val)
    (input : Slice U8) (suffix : List U8)
    (view : input.val = header major 27#u8 :: a :: b :: c :: d :: e :: f :: g :: h :: suffix)
    (decoded : CoreModels.core.num.U64.from_be_bytes
      (Array.make 8#usize [a, b, c, d, e, f, g, h]) = ok value) :
    frame.decode_argument input major = ok (.Some (value, 9#usize)) := by
  have first := slice_index_view input _ 0#usize (header major 27#u8) view (by rfl)
  have index1 := slice_index_view input _ 1#usize a view (by rfl)
  have index2 := slice_index_view input _ 2#usize b view (by rfl)
  have index3 := slice_index_view input _ 3#usize c view (by rfl)
  have index4 := slice_index_view input _ 4#usize d view (by rfl)
  have index5 := slice_index_view input _ 5#usize e view (by rfl)
  have index6 := slice_index_view input _ 6#usize f view (by rfl)
  have index7 := slice_index_view input _ 7#usize g view (by rfl)
  have index8 := slice_index_view input _ 8#usize h view (by rfl)
  have size : ¬ input.len < 9#usize := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, view,
      List.length_cons, UScalar.ofNatCore_val_eq]
    omega
  have admitted : 4294967296#u64 ≤ value := lower
  simp only [frame.decode_argument,
    slice_nonempty input (header major 27#u8) (a :: b :: c :: d :: e :: f :: g :: h :: suffix) view,
    Bool.false_eq_true, ite_false, bind_tc_ok, first,
    header_shift major 27#u8 majorBound (by decide), bne_self_eq_false,
    header_and major 27#u8 majorBound (by decide)]
  simp only [show ¬ 27#u8 ≤ 23#u8 from by decide, ite_false]
  simp only [CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    bind_tc_ok, size, ite_false, index1, index2, index3, index4, index5, index6, index7, index8, decoded, admitted, ite_true]
  rfl

/-- Every canonical production argument parses back with its exact value and consumed length, independently of following fields. -/
theorem decode_argument_roundtrip (major : U8) (value : U64)
    (domain : major = 0#u8 ∨ major = 2#u8) (input : Slice U8) (suffix : List U8)
    (view : input.val = argumentBytes major value ++ suffix) :
    frame.decode_argument input major = ok (.Some (value, (encoded major value).length)) := by
  have majorBound : major.val ≤ 7 := by
    rcases domain with rfl | rfl <;> decide
  unfold argumentBytes at view
  unfold encoded at view ⊢
  split_ifs at view ⊢ with inline octetWidth shortWidth wordWidth
  · apply decode_inline major value majorBound inline input suffix
    simpa only [UScalar.ofNatCore_val_eq, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append] using view
  · apply decode_byte major value majorBound (by change ¬ value.val ≤ 23 at inline; omega)
      octetWidth input suffix
    simpa only [UScalar.ofNatCore_val_eq, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append] using view
  · apply decode_two major value (octet value 8) (octet value 0) majorBound
      (by change ¬ value.val ≤ 255 at octetWidth; omega) input suffix
    · simpa only [UScalar.ofNatCore_val_eq, List.take_succ_cons, List.take_zero,
        List.cons_append, List.nil_append] using view
    · exact FrameCodecEndian.from_padded_two value shortWidth
  · apply decode_four major value (octet value 24) (octet value 16)
      (octet value 8) (octet value 0) majorBound
      (by change ¬ value.val ≤ 65535 at shortWidth; omega) input suffix
    · simpa only [UScalar.ofNatCore_val_eq, List.take_succ_cons, List.take_zero,
        List.cons_append, List.nil_append] using view
    · exact FrameCodecEndian.from_padded_four value wordWidth
  · apply decode_eight major value (octet value 56) (octet value 48)
      (octet value 40) (octet value 32) (octet value 24) (octet value 16)
      (octet value 8) (octet value 0) majorBound
      (by change ¬ value.val ≤ 4294967295 at wordWidth; omega) input suffix
    · simpa only [UScalar.ofNatCore_val_eq, List.take_succ_cons, List.take_zero,
        List.cons_append, List.nil_append] using view
    · simpa only [word, Array.make] using FrameCodecEndian.from_word value

end BeaconcryptCore.Refinement.FrameCodecArgument

/-- info: 'BeaconcryptCore.Refinement.FrameCodecArgument.argument_length_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecArgument.argument_length_pos

/-- info: 'BeaconcryptCore.Refinement.FrameCodecArgument.argumentBytes_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecArgument.argumentBytes_length

/-- info: 'BeaconcryptCore.Refinement.FrameCodecArgument.encode_argument_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecArgument.encode_argument_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecArgument.decode_argument_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecArgument.decode_argument_roundtrip
