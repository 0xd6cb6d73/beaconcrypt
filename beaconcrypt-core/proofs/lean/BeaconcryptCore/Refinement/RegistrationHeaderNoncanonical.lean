-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual optimal-width byte checker rejects every overlong primitive argument
below its source width threshold, with arbitrary following bytes. This proves
actual byte-scan rejection at the primitive check, without claiming complete
container validation or public decoder closure. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits
open RegistrationHeaderReadback RegistrationHeaderNarrowWord

set_option backward.isDefEq.respectTransparency false in
theorem reject_u8 (input : Slice U8) (major : U8) (value : U8) (rest : List U8)
    (contents : input.val = packed major 24#u8 :: value :: rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (overlong : value.val < 24) :
    cbor_raw_ints_optimal input = .ok false := by
  have initial := RegistrationHeaderJump.jump_prefix input major 24#u8 _ contents majorBound (by scalar_tac)
  have jump : jump_header input 0#usize = .ok 2#usize := by
    simpa [RegistrationHeaderJump.count] using initial
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input 2#usize [packed major 24#u8, value] rest (by simpa using contents) (by simp)
  have readFront : read_header front = .ok
      (header.mk (initial_byte_t.mk major 24#u8) (.LongArgumentU8 value)) :=
    read_byte_argument front major value [] (by simpa using frontBytes) majorBound notSimple
  unfold cbor_raw_ints_optimal
  rw [jump]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok, get_header_major_type, notSimple, ↓reduceIte, lift, uncurry]
  rw [RegistrationHeaderOptimal.size1]
  simp only [U8.cast_U64_val_eq]
  simp only [Nat.not_le_of_gt overlong, decide_false]

set_option backward.isDefEq.respectTransparency false in
theorem reject_u16 (input : Slice U8) (major : U8) (value : U16) (rest : List U8)
    (contents : input.val = packed major 25#u8 :: Word16.octet value 8 :: Word16.octet value 0 :: rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (overlong : value.val < 256) :
    cbor_raw_ints_optimal input = .ok false := by
  have initial := RegistrationHeaderJump.jump_prefix input major 25#u8 _ contents majorBound (by scalar_tac)
  have jump : jump_header input 0#usize = .ok 3#usize := by
    simpa [RegistrationHeaderJump.count] using initial
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input 3#usize [packed major 25#u8, Word16.octet value 8, Word16.octet value 0] rest (by simpa using contents) (by simp)
  have readFront : read_header front = .ok
      (header.mk (initial_byte_t.mk major 25#u8) (.LongArgumentU16 value)) :=
    RegistrationHeaderNarrowReadback.read_u16 front major value [] (by simpa using frontBytes) majorBound
  unfold cbor_raw_ints_optimal
  rw [jump]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok, get_header_major_type, notSimple, ↓reduceIte, lift, uncurry]
  rw [RegistrationHeaderOptimal.size2]
  simp only [U16.cast_U64_val_eq]
  simp only [Nat.not_le_of_gt overlong, decide_false]

set_option backward.isDefEq.respectTransparency false in
theorem reject_u32 (input : Slice U8) (major : U8) (value : U32) (rest : List U8)
    (contents : input.val = packed major 26#u8 :: Word32.octet value 24 :: Word32.octet value 16 :: Word32.octet value 8 :: Word32.octet value 0 :: rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (overlong : value.val < 65536) :
    cbor_raw_ints_optimal input = .ok false := by
  have initial := RegistrationHeaderJump.jump_prefix input major 26#u8 _ contents majorBound (by scalar_tac)
  have jump : jump_header input 0#usize = .ok 5#usize := by
    simpa [RegistrationHeaderJump.count] using initial
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input 5#usize [packed major 26#u8, Word32.octet value 24, Word32.octet value 16, Word32.octet value 8, Word32.octet value 0] rest (by simpa using contents) (by simp)
  have readFront : read_header front = .ok
      (header.mk (initial_byte_t.mk major 26#u8) (.LongArgumentU32 value)) :=
    RegistrationHeaderNarrowReadback.read_u32 front major value [] (by simpa using frontBytes) majorBound
  unfold cbor_raw_ints_optimal
  rw [jump]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok, get_header_major_type, notSimple, ↓reduceIte, lift, uncurry]
  rw [RegistrationHeaderOptimal.size3]
  simp only [U32.cast_U64_val_eq]
  simp only [Nat.not_le_of_gt overlong, decide_false]

set_option backward.isDefEq.respectTransparency false in
theorem reject_u64 (input : Slice U8) (major : U8) (value : U64) (rest : List U8)
    (contents : input.val = packed major 27#u8 :: FrameCodecWord.octet value 56 :: FrameCodecWord.octet value 48 :: FrameCodecWord.octet value 40 :: FrameCodecWord.octet value 32 :: FrameCodecWord.octet value 24 :: FrameCodecWord.octet value 16 :: FrameCodecWord.octet value 8 :: FrameCodecWord.octet value 0 :: rest)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value)
    (overlong : value.val < 4294967296) :
    cbor_raw_ints_optimal input = .ok false := by
  have initial := RegistrationHeaderJump.jump_prefix input major 27#u8 _ contents majorBound (by scalar_tac)
  have jump : jump_header input 0#usize = .ok 9#usize := by
    simpa [RegistrationHeaderJump.count] using initial
  obtain ⟨front, tail, splitInput, frontBytes, _⟩ := RegistrationHeaderJump.split_prefix
    input 9#usize [packed major 27#u8, FrameCodecWord.octet value 56, FrameCodecWord.octet value 48, FrameCodecWord.octet value 40, FrameCodecWord.octet value 32, FrameCodecWord.octet value 24, FrameCodecWord.octet value 16, FrameCodecWord.octet value 8, FrameCodecWord.octet value 0] rest (by simpa using contents) (by simp)
  have readFront : read_header front = .ok
      (header.mk (initial_byte_t.mk major 27#u8) (.LongArgumentU64 value)) :=
    RegistrationHeaderLongReadback.read_u64 front major value [] (by simpa using frontBytes) majorBound
  unfold cbor_raw_ints_optimal
  rw [jump]
  simp only [bind_tc_ok]
  rw [splitInput]
  simp only [bind_tc_ok, uncurry]
  rw [readFront]
  simp only [bind_tc_ok, get_header_major_type, notSimple, ↓reduceIte, lift, uncurry]
  rw [RegistrationHeaderOptimal.size4]
  simp only [Nat.not_le_of_gt overlong, decide_false]

end BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u8

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u16

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u32

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderNoncanonical.reject_u64
