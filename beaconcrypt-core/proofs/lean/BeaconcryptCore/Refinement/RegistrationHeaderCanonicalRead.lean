-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderCanonical
import BeaconcryptCore.Refinement.RegistrationHeaderJump
import BeaconcryptCore.Refinement.RegistrationHeaderOptimal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual jump, adjacent splitting and header read on every canonical encoded
argument prefix, with arbitrary suffix. The actual optimal-width byte check
accepts those prefixes, and actual cbor_read reconstructs the original UInt64
factory result. Complete container scans and public codecs remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open beaconcrypt_parse.cbordetveraux RegistrationHeaderCanonical RegistrationHeaderBits

set_option backward.isDefEq.respectTransparency false in
theorem read_encoded (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    read_header input = .ok (normalHeader major value) := by
  unfold encodedBytes at contents
  unfold normalHeader
  split_ifs with small byte word16 word32
  · simp only [small, ↓reduceIte, List.cons_append, List.nil_append] at contents
    apply RegistrationHeaderReadback.read_short input major _ rest contents majorBound
    rw [cast_value .U8 value (by scalar_tac)]
    exact small
  · simp only [small, byte, ↓reduceIte, List.cons_append, List.nil_append] at contents
    exact RegistrationHeaderReadback.read_byte_argument input major _ rest contents majorBound notSimple
  · simp only [small, byte, word16, ↓reduceIte, List.cons_append, List.nil_append] at contents
    exact RegistrationHeaderNarrowReadback.read_u16 input major _ rest contents majorBound
  · simp only [small, byte, word16, word32, ↓reduceIte, List.cons_append, List.nil_append] at contents
    exact RegistrationHeaderNarrowReadback.read_u32 input major _ rest contents majorBound
  · simp only [small, byte, word16, word32, ↓reduceIte, List.cons_append, List.nil_append] at contents
    exact RegistrationHeaderLongReadback.read_u64 input major value rest contents majorBound

theorem normal_major (major : U8) (value : U64) :
    (normalHeader major value).fst.major_type = major := by
  unfold normalHeader
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem jump_encoded (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest) (majorBound : major.val < 8) :
    jump_header input 0#usize = .ok (writtenCount value) := by
  unfold encodedBytes at contents
  unfold writtenCount
  split_ifs with small byte word16 word32
  · simp only [small, ↓reduceIte, List.cons_append, List.nil_append] at contents
    have bound : (UScalar.cast .U8 value).val < 24 := by
      rw [cast_value .U8 value (by scalar_tac)]
      exact small
    rw [RegistrationHeaderJump.jump_prefix input major _ rest contents majorBound (by omega)]
    unfold RegistrationHeaderJump.count
    have not24 : UScalar.cast .U8 value ≠ 24#u8 := by scalar_tac
    have not25 : UScalar.cast .U8 value ≠ 25#u8 := by scalar_tac
    have not26 : UScalar.cast .U8 value ≠ 26#u8 := by scalar_tac
    have not27 : UScalar.cast .U8 value ≠ 27#u8 := by scalar_tac
    simp only [not24, not25, not26, not27, ↓reduceIte]
  · simp only [small, byte, ↓reduceIte, List.cons_append, List.nil_append] at contents
    rw [RegistrationHeaderJump.jump_prefix input major _ _ contents majorBound (by scalar_tac)]
    rfl
  · simp only [small, byte, word16, ↓reduceIte, List.cons_append, List.nil_append] at contents
    rw [RegistrationHeaderJump.jump_prefix input major _ _ contents majorBound (by scalar_tac)]
    rfl
  · simp only [small, byte, word16, word32, ↓reduceIte, List.cons_append, List.nil_append] at contents
    rw [RegistrationHeaderJump.jump_prefix input major _ _ contents majorBound (by scalar_tac)]
    rfl
  · simp only [small, byte, word16, word32, ↓reduceIte, List.cons_append, List.nil_append] at contents
    rw [RegistrationHeaderJump.jump_prefix input major _ _ contents majorBound (by scalar_tac)]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem optimal_encoded (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes major value ++ rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    cbor_raw_ints_optimal input = .ok true := by
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input (writtenCount value) (encodedBytes major value) rest contents (encoded_length major value).symm
  have readFront : read_header front = .ok (normalHeader major value) :=
    read_encoded front major value [] (by simpa using frontBytes) majorBound notSimple
  unfold cbor_raw_ints_optimal
  rw [jump_encoded input major value rest contents majorBound]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok, get_header_major_type, normal_major, notSimple, ↓reduceIte]
  unfold normalHeader
  split_ifs with small byte word16 word32
  · simp only [lift, bind_tc_ok, uncurry]
    rw [cast_roundtrip .U8 value (by scalar_tac), RegistrationHeaderOptimal.size0]
    congr 1
    simp only [decide_eq_true_eq]
    exact small
  · simp only [lift, bind_tc_ok, uncurry]
    rw [cast_roundtrip .U8 value (by scalar_tac), RegistrationHeaderOptimal.size1]
    congr 1
    simp only [decide_eq_true_eq]
    omega
  · simp only [lift, bind_tc_ok, uncurry]
    rw [cast_roundtrip .U16 value (by scalar_tac), RegistrationHeaderOptimal.size2]
    congr 1
    simp only [decide_eq_true_eq]
    omega
  · simp only [lift, bind_tc_ok, uncurry]
    rw [cast_roundtrip .U32 value (by scalar_tac), RegistrationHeaderOptimal.size3]
    congr 1
    simp only [decide_eq_true_eq]
    omega
  · simp only [bind_tc_ok, uncurry]
    rw [RegistrationHeaderOptimal.size4]
    congr 1
    simp only [decide_eq_true_eq]
    omega

private theorem uint_factory (value : U64) :
    beaconcrypt_parse.cbordetver.cbor_det_mk_int64 .UInt64 value =
      (do let raw ← mk_raw_uint64 value
          .ok (cbor_raw.CBOR_Case_Int (cbor_int.mk cbor_major_type_uint64 raw.size raw.value))) := by
  simp only [beaconcrypt_parse.cbordetver.cbor_det_mk_int64,
    beaconcrypt_parse.cbordetver.cbor_det_int_kind.Insts.CoreCmpPartialEqcbor_det_int_kind.eq, bind_tc_ok]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem read_uint (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    cbor_read input = beaconcrypt_parse.cbordetver.cbor_det_mk_int64 .UInt64 value := by
  have majorBound : cbor_major_type_uint64.val < 8 := by simp [cbor_major_type_uint64]
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by
    simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input (writtenCount value) (encodedBytes cbor_major_type_uint64 value) rest contents
    (encoded_length cbor_major_type_uint64 value).symm
  have readFront : read_header front = .ok (normalHeader cbor_major_type_uint64 value) :=
    read_encoded front _ value [] (by simpa using frontBytes) majorBound notSimple
  unfold cbor_read
  rw [jump_encoded input _ value rest contents majorBound]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok]
  have update (before after : header) :
      Array.update (Array.repeat 1#usize before) 0#usize after = .ok (Array.repeat 1#usize after) := rfl
  have index (after : header) : Array.index_usize (Array.repeat 1#usize after) 0#usize = .ok after := rfl
  rw [update, bind_tc_ok, index]
  simp only [bind_tc_ok, normal_major, ↓reduceIte]
  rw [uint_factory]
  have compare : (value ≤ (UScalar.cast .U64 max_simple_value_additional_info)) ↔
      value.val < 24 := by
    simp only [max_simple_value_additional_info]
    change (value ≤ 23#u64) ↔ _
    scalar_tac
  simp only [mk_raw_uint64, lift, bind_tc_ok, compare]
  simp only [UScalar.lt_equiv,
    show (256#u64 : U64).val = 256 by rfl,
    show (65536#u64 : U64).val = 65536 by rfl,
    show (4294967296#u64 : U64).val = 4294967296 by rfl]
  unfold normalHeader
  split_ifs with small byte word16 word32
  · simp only [bind_tc_ok]
    rw [cast_roundtrip .U8 value (by scalar_tac)]
  · simp only [bind_tc_ok]
    rw [cast_roundtrip .U8 value (by scalar_tac)]
  · simp only [bind_tc_ok]
    rw [cast_roundtrip .U16 value (by scalar_tac)]
  · simp only [bind_tc_ok]
    rw [cast_roundtrip .U32 value (by scalar_tac)]
  · simp only [bind_tc_ok]

end BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.read_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.read_encoded

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.normal_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.normal_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.jump_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.jump_encoded

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.optimal_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.optimal_encoded

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.read_uint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead.read_uint
