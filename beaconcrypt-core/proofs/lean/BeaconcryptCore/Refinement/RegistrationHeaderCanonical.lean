-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationHeaderByteWrite
import BeaconcryptCore.Refinement.RegistrationHeaderNarrowWrite
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact composition of the original raw-integer factory, argument dispatcher,
header writer and header reader for all U64 values and non-simple major types.
The source determines the minimal width; actual bytes, suffix and slice length
are proved. This private header theorem is not complete public codec closure. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderCanonical
open beaconcrypt_parse.cbordetveraux RegistrationHeaderBits

def sourceHeader (major : U8) (value : U64) : RustM header := do
  let raw ← mk_raw_uint64 value
  raw_uint64_as_argument major raw

def normalHeader (major : U8) (value : U64) : header :=
  if value.val < 24 then
    header.mk (initial_byte_t.mk major (UScalar.cast .U8 value)) .LongArgumentOther
  else if value.val < 256 then
    header.mk (initial_byte_t.mk major 24#u8) (.LongArgumentU8 (UScalar.cast .U8 value))
  else if value.val < 65536 then
    header.mk (initial_byte_t.mk major 25#u8) (.LongArgumentU16 (UScalar.cast .U16 value))
  else if value.val < 4294967296 then
    header.mk (initial_byte_t.mk major 26#u8) (.LongArgumentU32 (UScalar.cast .U32 value))
  else header.mk (initial_byte_t.mk major 27#u8) (.LongArgumentU64 value)

theorem source_normal (major : U8) (value : U64) :
    sourceHeader major value = .ok (normalHeader major value) := by
  have compare : (value ≤ (UScalar.cast .U64 max_simple_value_additional_info)) ↔
      value.val < 24 := by
    simp only [max_simple_value_additional_info]
    change (value ≤ 23#u64) ↔ _
    scalar_tac
  simp only [sourceHeader, mk_raw_uint64, lift, bind_tc_ok, compare, UScalar.lt_equiv]
  unfold normalHeader
  split_ifs <;> simp_all [raw_uint64_as_argument, lift,
    additional_info_long_argument_8_bits, additional_info_long_argument_16_bits,
    additional_info_long_argument_32_bits, additional_info_long_argument_64_bits]

theorem cast_roundtrip (type : UScalarTy) (value : U64)
    (bound : value.val < 2 ^ type.numBits) :
    UScalar.cast .U64 (UScalar.cast type value) = value := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.cast_val_eq]
  rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt value.hBounds]

theorem cast_value (type : UScalarTy) (value : U64)
    (bound : value.val < 2 ^ type.numBits) :
    (UScalar.cast type value).val = value.val := by
  rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt bound]

def writtenCount (value : U64) : Usize :=
  if value.val < 24 then 1#usize else if value.val < 256 then 2#usize
  else if value.val < 65536 then 3#usize else if value.val < 4294967296 then 5#usize
  else 9#usize

def written (out : Slice U8) (major : U8) (value : U64) : Slice U8 :=
  if value.val < 24 then out.set 0#usize (packed major (UScalar.cast .U8 value))
  else if value.val < 256 then RegistrationHeaderByteWrite.written out major (UScalar.cast .U8 value)
  else if value.val < 65536 then RegistrationHeaderNarrowWrite.Header16.written out major (UScalar.cast .U16 value)
  else if value.val < 4294967296 then RegistrationHeaderNarrowWrite.Header32.written out major (UScalar.cast .U32 value)
  else RegistrationHeaderWrite.writtenU64 out major value

def sourceWrite (out : Slice U8) (major : U8) (value : U64) : RustM (Usize × Slice U8) := do
  let argument ← sourceHeader major value
  write_header argument out 0#usize

theorem source_write (out : Slice U8) (major : U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length)
    (notSimple : major ≠ cbor_major_type_simple_value) :
    sourceWrite out major value = .ok (writtenCount value, written out major value) := by
  unfold sourceWrite
  rw [source_normal]
  simp only [bind_tc_ok]
  unfold normalHeader written writtenCount at *
  split_ifs with small byte word16 word32
  all_goals simp_all only [↓reduceIte]
  · apply RegistrationHeaderWrite.write_short out major _ .LongArgumentOther (by scalar_tac)
    rw [cast_value .U8 value (by scalar_tac)]
    exact small
  · exact RegistrationHeaderByteWrite.write out major _ (by scalar_tac) notSimple
  · exact RegistrationHeaderNarrowWrite.Header16.write out major _ (by scalar_tac)
  · exact RegistrationHeaderNarrowWrite.Header32.write out major _ (by scalar_tac)
  · exact RegistrationHeaderWrite.write_u64 out major value (by scalar_tac)

theorem written_length (out : Slice U8) (major : U8) (value : U64) :
    (written out major value).length = out.length := by
  unfold written
  split_ifs
  · exact Slice.set_length _ _ _
  · exact RegistrationHeaderByteWrite.length _ _ _
  · exact RegistrationHeaderNarrowWrite.Header16.length _ _ _
  · exact RegistrationHeaderNarrowWrite.Header32.length _ _ _
  · exact RegistrationHeaderWrite.written_u64_length _ _ _

def readArgument (input : Slice U8) : RustM U64 := do
  let argument ← read_header input
  argument_as_uint64 argument.fst argument.snd

theorem argument_normal (major : U8) (value : U64) :
    argument_as_uint64 (normalHeader major value).fst (normalHeader major value).snd = .ok value := by
  unfold normalHeader
  split_ifs with small byte word16 word32
  · exact congrArg RustM.ok (cast_roundtrip .U8 value (by scalar_tac))
  · exact congrArg RustM.ok (cast_roundtrip .U8 value (by scalar_tac))
  · exact congrArg RustM.ok (cast_roundtrip .U16 value (by scalar_tac))
  · exact congrArg RustM.ok (cast_roundtrip .U32 value (by scalar_tac))
  · rfl

theorem header_readback (out : Slice U8) (major : U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    read_header (written out major value) = .ok (normalHeader major value) := by
  unfold written normalHeader writtenCount at *
  split_ifs with small byte word16 word32
  all_goals simp_all only [↓reduceIte]
  · apply RegistrationHeaderWrite.short_readback _ major _ (by scalar_tac) majorBound
    rw [cast_value .U8 value (by scalar_tac)]
    exact small
  · exact RegistrationHeaderByteWrite.readback _ major _ (by scalar_tac) majorBound notSimple
  · exact RegistrationHeaderNarrowWrite.Header16.readback _ major _ (by scalar_tac) majorBound
  · exact RegistrationHeaderNarrowWrite.Header32.readback _ major _ (by scalar_tac) majorBound
  · exact RegistrationHeaderWrite.u64_readback _ major value (by scalar_tac) majorBound

theorem argument_readback (out : Slice U8) (major : U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    readArgument (written out major value) = .ok value := by
  unfold readArgument
  rw [header_readback out major value space majorBound notSimple]
  simp only [bind_tc_ok, argument_normal]

def encodedBytes (major : U8) (value : U64) : List U8 :=
  if value.val < 24 then [packed major (UScalar.cast .U8 value)]
  else if value.val < 256 then [packed major 24#u8, UScalar.cast .U8 value]
  else if value.val < 65536 then
    [packed major 25#u8, RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 8,
      RegistrationHeaderNarrowWord.Word16.octet (UScalar.cast .U16 value) 0]
  else if value.val < 4294967296 then
    [packed major 26#u8, RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 24,
      RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 16,
      RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 8,
      RegistrationHeaderNarrowWord.Word32.octet (UScalar.cast .U32 value) 0]
  else [packed major 27#u8, FrameCodecWord.octet value 56, FrameCodecWord.octet value 48,
    FrameCodecWord.octet value 40, FrameCodecWord.octet value 32, FrameCodecWord.octet value 24,
    FrameCodecWord.octet value 16, FrameCodecWord.octet value 8, FrameCodecWord.octet value 0]

theorem encoded_length (major : U8) (value : U64) :
    (encodedBytes major value).length = (writtenCount value).val := by
  unfold encodedBytes writtenCount
  split_ifs <;> simp

theorem written_bytes (out : Slice U8) (major : U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length) :
    (written out major value).val = encodedBytes major value ++ out.val.drop (writtenCount value).val := by
  unfold written encodedBytes writtenCount at *
  split_ifs with small byte word16 word32
  all_goals simp_all only [↓reduceIte]
  · simpa using RegistrationHeaderWrite.short_bytes out major (UScalar.cast .U8 value) (by scalar_tac)
  · simpa using RegistrationHeaderByteWrite.bytes out major (UScalar.cast .U8 value) (by scalar_tac)
  · simpa using RegistrationHeaderNarrowWrite.Header16.bytes out major (UScalar.cast .U16 value) (by scalar_tac)
  · simpa using RegistrationHeaderNarrowWrite.Header32.bytes out major (UScalar.cast .U32 value) (by scalar_tac)
  · simpa using RegistrationHeaderWrite.written_u64_bytes out major value (by scalar_tac)

theorem codec (out : Slice U8) (major : U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length)
    (majorBound : major.val < 8) (notSimple : major ≠ cbor_major_type_simple_value) :
    ∃ after, sourceWrite out major value = .ok (writtenCount value, after) ∧
      after.length = out.length ∧
      after.val = encodedBytes major value ++ out.val.drop (writtenCount value).val ∧
      readArgument after = .ok value := by
  exact ⟨written out major value, source_write out major value space notSimple,
    written_length out major value, written_bytes out major value space,
    argument_readback out major value space majorBound notSimple⟩

end BeaconcryptCore.Refinement.RegistrationHeaderCanonical

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.source_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.source_normal

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.cast_roundtrip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.cast_roundtrip

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.cast_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.cast_value

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.source_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.source_write

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.written_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.written_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.argument_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.argument_normal

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.header_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.header_readback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.argument_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.argument_readback

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.encoded_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.encoded_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.written_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.written_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderCanonical.codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderCanonical.codec
