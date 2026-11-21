-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderBits
import BeaconcryptCore.Refinement.RegistrationHeaderWord
import BeaconcryptCore.Refinement.RegistrationHeaderLongReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual source header writer byte output, suffix preservation and reader
composition for short and full U64 arguments at offset zero. The caller supplies
only output capacity and the ordinary bitfield bounds for readback. Complete
public codec validation and other argument-width branches remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderWrite
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits

private theorem add01 : core.num.Usize.wrapping_add 0#usize 1#usize = .ok 1#usize := by
  change RustM.ok (Usize.wrapping_add 0#usize 1#usize) = RustM.ok 1#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_add_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
private theorem sub11 : core.num.Usize.wrapping_sub 1#usize 1#usize = .ok 0#usize := by
  change RustM.ok (Usize.wrapping_sub 1#usize 1#usize) = RustM.ok 0#usize
  congr 1
  apply UScalar.eq_of_val_eq
  simp only [Usize.wrapping_sub_val_eq]
  cases System.Platform.numBits_eq <;> rename_i bits <;>
    simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]

private theorem shr_twice (value : U64) (left right : Nat) :
    RegistrationHeaderWord.shr (RegistrationHeaderWord.shr value left) right =
      RegistrationHeaderWord.shr value (left + right) := by
  apply U64.bv_eq_imp_eq
  exact (BitVec.shiftRight_add value.bv left right).symm

private theorem low_octet (value : U64) :
    UScalar.cast .U8 value = FrameCodecWord.octet value 0 := by
  simp [FrameCodecWord.octet, UScalar.cast, BitVec.zeroExtend]

theorem update_set (out : Slice U8) (index : Usize) (value : U8)
    (bound : index.val < out.val.length) :
    out.update index value = .ok (out.set index value) := by
  simp [Slice.update, List.getElem?_eq_getElem bound, Slice.set, Slice.setAtNat]

set_option backward.isDefEq.respectTransparency false in
theorem write_short (out : Slice U8) (major additional : U8)
    (argument : long_argument) (nonempty : 0 < out.val.length)
    (short : additional.val < 24) :
    write_header { fst := { major_type := major, additional_info := additional }, snd := argument }
      out 0#usize = .ok (1#usize, out.set 0#usize (packed major additional)) := by
  have not24 : additional ≠ 24#u8 := by intro equal; subst additional; scalar_tac
  have not25 : additional ≠ 25#u8 := by intro equal; subst additional; scalar_tac
  have not26 : additional ≠ 26#u8 := by intro equal; subst additional; scalar_tac
  have not27 : additional ≠ 27#u8 := by intro equal; subst additional; scalar_tac
  simp only [write_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bind_tc_ok, add01, sub11, set_additional, set_major]
  simp [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq, nonempty,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits,
    not24, not25, not26, not27]

theorem short_bytes (out : Slice U8) (major additional : U8)
    (nonempty : 0 < out.val.length) :
    (out.set 0#usize (packed major additional)).val =
      packed major additional :: out.val.drop 1 := by
  obtain ⟨first, rest, contents⟩ := List.exists_cons_of_length_pos nonempty
  simp [Slice.set_val_eq, contents]

theorem short_readback (out : Slice U8) (major additional : U8)
    (nonempty : 0 < out.val.length) (majorBound : major.val < 8)
    (short : additional.val < 24) :
    read_header (out.set 0#usize (packed major additional)) = .ok
      (header.mk (initial_byte_t.mk major additional) .LongArgumentOther) := by
  exact RegistrationHeaderReadback.read_short _ major additional _
    (short_bytes out major additional nonempty) majorBound short

def writtenU64 (out : Slice U8) (major : U8) (value : U64) : Slice U8 :=
  ((((((((out.set 0#usize (packed major 27#u8)).set 1#usize (FrameCodecWord.octet value 56)).set 2#usize (FrameCodecWord.octet value 48)).set 3#usize (FrameCodecWord.octet value 40)).set 4#usize (FrameCodecWord.octet value 32)).set 5#usize (FrameCodecWord.octet value 24)).set 6#usize (FrameCodecWord.octet value 16)).set 7#usize (FrameCodecWord.octet value 8)).set 8#usize (FrameCodecWord.octet value 0)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem write_u64 (out : Slice U8) (major : U8) (value : U64)
    (space : 9 ≤ out.val.length) :
    write_header (header.mk (initial_byte_t.mk major 27#u8) (.LongArgumentU64 value)) out 0#usize = .ok (9#usize, writtenU64 out major value) := by
  have sub9 : core.num.Usize.wrapping_sub 9#usize 1#usize = .ok 8#usize := by
    change RustM.ok (Usize.wrapping_sub 9#usize 1#usize) = RustM.ok 8#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub8 : core.num.Usize.wrapping_sub 8#usize 1#usize = .ok 7#usize := by
    change RustM.ok (Usize.wrapping_sub 8#usize 1#usize) = RustM.ok 7#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub7 : core.num.Usize.wrapping_sub 7#usize 1#usize = .ok 6#usize := by
    change RustM.ok (Usize.wrapping_sub 7#usize 1#usize) = RustM.ok 6#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub6 : core.num.Usize.wrapping_sub 6#usize 1#usize = .ok 5#usize := by
    change RustM.ok (Usize.wrapping_sub 6#usize 1#usize) = RustM.ok 5#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub5 : core.num.Usize.wrapping_sub 5#usize 1#usize = .ok 4#usize := by
    change RustM.ok (Usize.wrapping_sub 5#usize 1#usize) = RustM.ok 4#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub4 : core.num.Usize.wrapping_sub 4#usize 1#usize = .ok 3#usize := by
    change RustM.ok (Usize.wrapping_sub 4#usize 1#usize) = RustM.ok 3#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub3 : core.num.Usize.wrapping_sub 3#usize 1#usize = .ok 2#usize := by
    change RustM.ok (Usize.wrapping_sub 3#usize 1#usize) = RustM.ok 2#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub2 : core.num.Usize.wrapping_sub 2#usize 1#usize = .ok 1#usize := by
    change RustM.ok (Usize.wrapping_sub 2#usize 1#usize) = RustM.ok 1#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have add18 : core.num.Usize.wrapping_add 1#usize 8#usize = .ok 9#usize := by
    change RustM.ok (Usize.wrapping_add 1#usize 8#usize) = RustM.ok 9#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_add_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  simp only [write_header,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f315f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken646673745f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken5f5f70726f6a5f5f4d6b647475706c65325f5f6974656d5f5f5f325f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bcExtractedToken64736e645f5f43424f525f537065635f5261775f4576657250617273655f696e697469616c5f627974655f745f43424f525f537065635f5261775f4576657250617273655f6c6f6e675f617267756d656e74,
    bind_tc_ok, add01, sub11, set_additional, set_major]
  have nonempty : 0 < out.val.length := by omega
  simp only [Slice.index_mut_usize, Slice.index_usize, Slice.getElem?_Usize_eq,
    show (0#usize).val = 0 by scalar_tac, List.getElem?_eq_getElem nonempty,
    bind_tc_ok, uncurry, additional_info_long_argument_8_bits,
    additional_info_long_argument_16_bits, additional_info_long_argument_32_bits,
    additional_info_long_argument_64_bits,
    show (27#u8 : U8) ≠ 24#u8 by decide,
    show (27#u8 : U8) ≠ 25#u8 by decide,
    show (27#u8 : U8) ≠ 26#u8 by decide, ↓reduceIte, add18, sub9, sub8,
    sub7, sub6, sub5, sub4, sub3, sub2, RegistrationHeaderWord.divide_256, lift]
  simp only [shr_twice, Nat.reduceAdd, RegistrationHeaderWord.shifted_octet]
  rw [low_octet]
  simp (disch := scalar_tac) only [update_set, bind_tc_ok]
  rfl

theorem written_u64_length (out : Slice U8) (major : U8) (value : U64) :
    (writtenU64 out major value).length = out.length := by
  simp only [writtenU64, Slice.set_length]

theorem written_u64_bytes (out : Slice U8) (major : U8) (value : U64)
    (space : 9 ≤ out.val.length) :
    (writtenU64 out major value).val = packed major 27#u8 ::
      FrameCodecWord.octet value 56 :: FrameCodecWord.octet value 48 ::
      FrameCodecWord.octet value 40 :: FrameCodecWord.octet value 32 ::
      FrameCodecWord.octet value 24 :: FrameCodecWord.octet value 16 ::
      FrameCodecWord.octet value 8 :: FrameCodecWord.octet value 0 :: out.val.drop 9 := by
  obtain ⟨byte0, tail0, shape0⟩ := List.exists_cons_of_length_pos (l := out.val) (by omega)
  have space0 : 8 ≤ tail0.length := by
    rw [shape0] at space
    simp only [List.length_cons] at space
    omega
  obtain ⟨byte1, tail1, shape1⟩ := List.exists_cons_of_length_pos (l := tail0) (by omega)
  have space1 : 7 ≤ tail1.length := by
    rw [shape1] at space0
    simp only [List.length_cons] at space0
    omega
  obtain ⟨byte2, tail2, shape2⟩ := List.exists_cons_of_length_pos (l := tail1) (by omega)
  have space2 : 6 ≤ tail2.length := by
    rw [shape2] at space1
    simp only [List.length_cons] at space1
    omega
  obtain ⟨byte3, tail3, shape3⟩ := List.exists_cons_of_length_pos (l := tail2) (by omega)
  have space3 : 5 ≤ tail3.length := by
    rw [shape3] at space2
    simp only [List.length_cons] at space2
    omega
  obtain ⟨byte4, tail4, shape4⟩ := List.exists_cons_of_length_pos (l := tail3) (by omega)
  have space4 : 4 ≤ tail4.length := by
    rw [shape4] at space3
    simp only [List.length_cons] at space3
    omega
  obtain ⟨byte5, tail5, shape5⟩ := List.exists_cons_of_length_pos (l := tail4) (by omega)
  have space5 : 3 ≤ tail5.length := by
    rw [shape5] at space4
    simp only [List.length_cons] at space4
    omega
  obtain ⟨byte6, tail6, shape6⟩ := List.exists_cons_of_length_pos (l := tail5) (by omega)
  have space6 : 2 ≤ tail6.length := by
    rw [shape6] at space5
    simp only [List.length_cons] at space5
    omega
  obtain ⟨byte7, tail7, shape7⟩ := List.exists_cons_of_length_pos (l := tail6) (by omega)
  have space7 : 1 ≤ tail7.length := by
    rw [shape7] at space6
    simp only [List.length_cons] at space6
    omega
  obtain ⟨byte8, tail8, shape8⟩ := List.exists_cons_of_length_pos (l := tail7) (by omega)
  simp [writtenU64, Slice.set_val_eq, shape0, shape1, shape2, shape3, shape4, shape5, shape6, shape7, shape8]

theorem u64_readback (out : Slice U8) (major : U8) (value : U64)
    (space : 9 ≤ out.val.length) (majorBound : major.val < 8) :
    read_header (writtenU64 out major value) = .ok
      (header.mk (initial_byte_t.mk major 27#u8) (.LongArgumentU64 value)) := by
  exact RegistrationHeaderLongReadback.read_u64 _ major value _
    (written_u64_bytes out major value space) majorBound

end BeaconcryptCore.Refinement.RegistrationHeaderWrite

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.update_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.update_set

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.write_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.write_short

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.short_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.short_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.short_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.short_readback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.write_u64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.write_u64

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.written_u64_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.written_u64_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.written_u64_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.written_u64_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderWrite.u64_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderWrite.u64_readback
