-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.FrameCodecExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecWord

private theorem extract_extract {w a b c d : Nat} (x : BitVec w) (bound : b + c ≤ d) :
    (x.extractLsb' a d).extractLsb' b c = x.extractLsb' (a+b) c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_extractLsb']
  intro hi
  simp [hi, show b + i < d by omega, Nat.add_assoc]

def octet (value : U64) (offset : Nat) : U8 := ⟨(value.bv >>> offset).setWidth 8⟩
def word (value : U64) : Std.Array U8 8#usize :=
  ⟨[octet value 56, octet value 48, octet value 40, octet value 32,
    octet value 24, octet value 16, octet value 8, octet value 0], by simp⟩
theorem word_exact (value : U64) :
    CoreModels.core.num.U64.to_be_bytes value = ok (word value) := by
  change ok (Aeneas.Std.core.num.U64.to_be_bytes value) = ok (word value)
  congr 1
  apply Subtype.ext
  change value.bv.toBEBytes.map (@UScalar.mk .U8) = (word value).val
  simp only [BitVec.toBEBytes]
  iterate 9
    rw [BitVec.toLEBytes]
    norm_num only [Nat.reduceLT, Nat.reduceSub]
    simp only [ite_true, ite_false, Nat.reduceSub]
  simp only [List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, word, octet]
  simp only [List.cons.injEq, UScalar.mk.injEq]
  simp [BitVec.setWidth_ushiftRight_eq_extractLsb,
    extract_extract, BitVec.setWidth_extractLsb'_of_le]

end BeaconcryptCore.Refinement.FrameCodecWord

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWord.word_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWord.word_exact
