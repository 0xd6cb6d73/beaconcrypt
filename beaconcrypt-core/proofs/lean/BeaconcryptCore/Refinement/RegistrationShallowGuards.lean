-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationShallowExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationConstructorGuards

set_option autoImplicit false
set_option warningAsError true

/-! Source-constructor specialization preserves the original factory's size and
failure branches. The unreachable UTF8 operation is left completely arbitrary.
This is the explicit specialization boundary recorded by the source preparer;
it does not assert a complete Rust byte-parser or public codec law. -/

namespace BeaconcryptCore.Refinement.RegistrationShallowGuards
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_parse
open cbordetveraux
abbrev Kind := cbordetver.cbor_det_string_kind
abbrev RawOption := cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177

/-- Original factory control with the exact extracted scalar/constructor leaves.
The source manifest retains the full original UTF8 implementation syntax. -/
def factoryWithUtf8 (utf8 : Slice U8 → RustM Bool) (ty : Kind) (s : Slice U8) :
    RustM RawOption := do
  let i ← core.slice.Slice.len s
  let q1 ← core.num.Usize.wrapping_div i 32768#usize
  let q2 ← core.num.Usize.wrapping_div q1 32768#usize
  let q3 ← core.num.Usize.wrapping_div q2 32768#usize
  let q4 ← core.num.Usize.wrapping_div q3 32768#usize
  if q4 < 16#usize then
    let isText ← extraction_string_kind_equal ty .TextString
    let correct ← if isText then utf8 s else RustM.ok true
    if correct then
      let i1 ← lift (UScalar.cast .U64 i)
      let len64 ← mk_raw_uint64 i1
      let isByte ← extraction_string_kind_equal ty .ByteString
      let major ← if isByte then RustM.ok cbor_major_type_byte_string
        else RustM.ok cbor_major_type_text_string
      RustM.ok (.Some (.CBOR_Case_String {
        cbor_string_type := major
        cbor_string_size := len64.size
        cbor_string_ptr := s }))
    else RustM.ok .None
  else RustM.ok .None

theorem byte_not_text : extraction_string_kind_equal .ByteString .TextString =
    .ok false := by
  simp [extraction_string_kind_equal, cbordetver.cbor_det_string_kind.Insts.CoreCmpPartialEqcbor_det_string_kind.eq, cbordetver.cbor_det_string_kind.read_discriminant]

theorem byte_is_byte : extraction_string_kind_equal .ByteString .ByteString =
    .ok true := by
  simp [extraction_string_kind_equal, cbordetver.cbor_det_string_kind.Insts.CoreCmpPartialEqcbor_det_string_kind.eq, cbordetver.cbor_det_string_kind.read_discriminant]

theorem byte_factory_preserved (utf8 : Slice U8 → RustM Bool) (s : Slice U8) :
    factoryWithUtf8 utf8 .ByteString s = extraction_mk_byte_string s := by
  simp only [factoryWithUtf8, extraction_mk_byte_string, byte_not_text, byte_is_byte, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]

/-- The literal generated registration field discriminator selects ByteString. -/
theorem registration_byte_kind :
    (if (2#u8 : U8) = cbor_major_type_byte_string then cbordetver.cbor_det_string_kind.ByteString else cbordetver.cbor_det_string_kind.TextString) =
      cbordetver.cbor_det_string_kind.ByteString := by
  simp [cbor_major_type_byte_string]

end BeaconcryptCore.Refinement.RegistrationShallowGuards

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_not_text' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_not_text

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_is_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_is_byte

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_factory_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowGuards.byte_factory_preserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowGuards.registration_byte_kind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowGuards.registration_byte_kind
