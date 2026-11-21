-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationShallowExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderCanonicalRead
import BeaconcryptCore.Refinement.RegistrationConstructorGuards
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Actual UInt64 factory composed with the extracted original shallow integer
serializer branch. Capacity suffices for exact byte output, same slice length,
untouched suffix and equality of actual cbor_read to the original source factory.
The generic public serializer dispatcher and complete registration remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationShallowUInt
open beaconcrypt_parse cbordetveraux RegistrationHeaderCanonical

/-- Composition of the actual integer factory and extracted original shallow branch.
The public generic serializer dispatcher and complete message remain separate. -/
def sourceSerialize (out : Slice U8) (value : U64) : RustM (Usize × Slice U8) := do
  let raw ← cbordetver.cbor_det_mk_int64 .UInt64 value
  match raw with
  | .CBOR_Case_Int integer => extraction_serialize_shallow_int integer out 0#usize
  | _ => .fail .panic

set_option backward.isDefEq.respectTransparency false in
theorem source_serialize (out : Slice U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length) :
    sourceSerialize out value = .ok (writtenCount value, written out cbor_major_type_uint64 value) := by
  have notSimple : cbor_major_type_uint64 ≠ cbor_major_type_simple_value := by
    simp [cbor_major_type_uint64, cbor_major_type_simple_value]
  obtain ⟨size, raw⟩ := RegistrationConstructorGuards.mk_raw_exists value
  have argument : raw_uint64_as_argument cbor_major_type_uint64 { size := size, value := value } =
      .ok (normalHeader cbor_major_type_uint64 value) := by
    have result := source_normal cbor_major_type_uint64 value
    unfold sourceHeader at result
    rw [raw] at result
    simpa only [bind_tc_ok] using result
  have writer := source_write out cbor_major_type_uint64 value space notSimple
  simp only [sourceWrite, source_normal, bind_tc_ok] at writer
  unfold sourceSerialize
  simp only [cbordetver.cbor_det_mk_int64,
    cbordetver.cbor_det_int_kind.Insts.CoreCmpPartialEqcbor_det_int_kind.eq]
  rw [raw]
  simp
  unfold extraction_serialize_shallow_int cbor_raw_with_perm_get_header_d cbor_raw_get_header_d
  dsimp only
  rw [argument]
  simp only [bind_tc_ok]
  rw [writer]
  simp [RegistrationHeaderCanonicalRead.normal_major, cbor_major_type_uint64,
    cbor_major_type_byte_string, cbor_major_type_text_string, cbor_major_type_array,
    cbor_major_type_map, cbor_major_type_tagged, uncurry]

theorem readback (out : Slice U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length) :
    cbor_read (written out cbor_major_type_uint64 value) = cbordetver.cbor_det_mk_int64 .UInt64 value := by
  exact RegistrationHeaderCanonicalRead.read_uint _ value _
    (written_bytes out cbor_major_type_uint64 value space)

theorem codec (out : Slice U8) (value : U64)
    (space : (writtenCount value).val ≤ out.val.length) :
    ∃ after, sourceSerialize out value = .ok (writtenCount value, after) ∧
      after.length = out.length ∧
      after.val = encodedBytes cbor_major_type_uint64 value ++ out.val.drop (writtenCount value).val ∧
      cbor_read after = cbordetver.cbor_det_mk_int64 .UInt64 value := by
  exact ⟨written out cbor_major_type_uint64 value, source_serialize out value space,
    written_length out cbor_major_type_uint64 value, written_bytes out cbor_major_type_uint64 value space,
    readback out value space⟩

end BeaconcryptCore.Refinement.RegistrationShallowUInt

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowUInt.source_serialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowUInt.source_serialize

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowUInt.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowUInt.readback

/-- info: 'BeaconcryptCore.Refinement.RegistrationShallowUInt.codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationShallowUInt.codec
