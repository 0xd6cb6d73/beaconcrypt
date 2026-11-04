-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderReadback
import BeaconcryptCore.Refinement.RegistrationHeaderWord
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual extracted header reader on a U64 octet prefix and arbitrary suffix.
This proves the complete eight-byte argument branch without a canonical-size
premise; malformed validation and complete public codec composition remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderLongReadback
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits RegistrationHeaderReadback
open FrameCodecWord RegistrationHeaderWord

set_option backward.isDefEq.respectTransparency false in
theorem read_u64 (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = packed major 27#u8 :: octet value 56 :: octet value 48 ::
      octet value 40 :: octet value 32 :: octet value 24 :: octet value 16 ::
      octet value 8 :: octet value 0 :: rest)
    (majorBound : major.val < 8) :
    read_header input = .ok {
      fst := { major_type := major, additional_info := 27#u8 }
      snd := .LongArgumentU64 value } := by
  obtain ⟨front, tail, splitInput, frontBytes, tailBytes⟩ := split_first input _ _ contents
  unfold read_header
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [read_initial front major 27#u8 [] frontBytes majorBound (by scalar_tac)]
  simp only [bind_tc_ok, additional_info_long_argument_8_bits,
    additional_info_long_argument_16_bits, additional_info_long_argument_32_bits,
    additional_info_long_argument_64_bits,
    show (27#u8 : U8) ≠ 24#u8 by decide,
    show (27#u8 : U8) ≠ 25#u8 by decide,
    show (27#u8 : U8) ≠ 26#u8 by decide, ↓reduceIte]
  have sub76 : core.num.Usize.wrapping_sub 7#usize 1#usize = .ok 6#usize := by
    change RustM.ok (Usize.wrapping_sub 7#usize 1#usize) = RustM.ok 6#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub65 : core.num.Usize.wrapping_sub 6#usize 1#usize = .ok 5#usize := by
    change RustM.ok (Usize.wrapping_sub 6#usize 1#usize) = RustM.ok 5#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub54 : core.num.Usize.wrapping_sub 5#usize 1#usize = .ok 4#usize := by
    change RustM.ok (Usize.wrapping_sub 5#usize 1#usize) = RustM.ok 4#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub43 : core.num.Usize.wrapping_sub 4#usize 1#usize = .ok 3#usize := by
    change RustM.ok (Usize.wrapping_sub 4#usize 1#usize) = RustM.ok 3#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub32 : core.num.Usize.wrapping_sub 3#usize 1#usize = .ok 2#usize := by
    change RustM.ok (Usize.wrapping_sub 3#usize 1#usize) = RustM.ok 2#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub21 : core.num.Usize.wrapping_sub 2#usize 1#usize = .ok 1#usize := by
    change RustM.ok (Usize.wrapping_sub 2#usize 1#usize) = RustM.ok 1#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  simp only [sub76, sub65, sub54, sub43, sub32, sub21, bind_tc_ok]
  simp only [Slice.index_usize, Slice.getElem?_Usize_eq, tailBytes]
  simp [wrapping_mul, wrapping_add, lift]
  change readWord8 (octet value 56) (octet value 48)
      (octet value 40) (octet value 32) (octet value 24) (octet value 16)
      (octet value 8) (octet value 0) = value
  rw [read_word_octets]

end BeaconcryptCore.Refinement.RegistrationHeaderLongReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderLongReadback.read_u64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderLongReadback.read_u64
