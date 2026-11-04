-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderWrite
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual one-byte argument writer, with all byte and suffix effects and
composition with the actual reader. The simple-value branch uses a distinct
source argument constructor and is not identified with the integer branch. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderByteWrite
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits
open RegistrationHeaderWrite (update_set)

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


def written (out : Slice U8) (major value : U8) : Slice U8 :=
  (out.set 0#usize (packed major 24#u8)).set 1#usize value

set_option backward.isDefEq.respectTransparency false in
theorem write (out : Slice U8) (major value : U8)
    (space : 2 ≤ out.val.length) (notSimple : major ≠ cbor_major_type_simple_value) :
    write_header (header.mk (initial_byte_t.mk major 24#u8) (.LongArgumentU8 value))
      out 0#usize = .ok (2#usize, written out major value) := by
  have add11 : core.num.Usize.wrapping_add 1#usize 1#usize = .ok 2#usize := by
    change RustM.ok (Usize.wrapping_add 1#usize 1#usize) = RustM.ok 2#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_add_val_eq]
    cases System.Platform.numBits_eq <;> rename_i bits <;>
      simp [Usize.size, Usize.numBits, UScalarTy.numBits, bits]
  have sub2 : core.num.Usize.wrapping_sub 2#usize 1#usize = .ok 1#usize := by
    change RustM.ok (Usize.wrapping_sub 2#usize 1#usize) = RustM.ok 1#usize
    congr 1
    apply UScalar.eq_of_val_eq
    simp only [Usize.wrapping_sub_val_eq]
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
    notSimple, ↓reduceIte, add11, sub2]
  simp (disch := scalar_tac) only [update_set, bind_tc_ok]
  rfl

theorem length (out : Slice U8) (major value : U8) :
    (written out major value).length = out.length := by
  simp only [written, Slice.set_length]

theorem bytes (out : Slice U8) (major value : U8) (space : 2 ≤ out.val.length) :
    (written out major value).val = packed major 24#u8 :: value :: out.val.drop 2 := by
  obtain ⟨byte0, tail0, shape0⟩ := List.exists_cons_of_length_pos (l := out.val) (by omega)
  have space0 : 1 ≤ tail0.length := by
    rw [shape0] at space
    simp only [List.length_cons] at space
    omega
  obtain ⟨byte1, tail1, shape1⟩ := List.exists_cons_of_length_pos (l := tail0) (by omega)
  simp [written, Slice.set_val_eq, shape0, shape1]

theorem readback (out : Slice U8) (major value : U8) (space : 2 ≤ out.val.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    read_header (written out major value) = .ok
      (header.mk (initial_byte_t.mk major 24#u8) (.LongArgumentU8 value)) := by
  exact RegistrationHeaderReadback.read_byte_argument _ major value _
    (bytes out major value space) majorBound notSimple

end BeaconcryptCore.Refinement.RegistrationHeaderByteWrite

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.write

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderByteWrite.readback
