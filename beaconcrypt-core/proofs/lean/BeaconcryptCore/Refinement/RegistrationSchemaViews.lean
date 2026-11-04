-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaIteratorReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Original schema major-type, destruct, validation and projection functions return the exact UInt64 values and borrowed byte payloads produced by the source iterator. The original serialized array starts its source iterator at count eight. Small source U64 count updates are evaluated exactly. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaViews
open beaconcrypt_parse cbordetveraux
open RegistrationArrayReadback RegistrationSchemaIteratorReadback

def uint (size : U8) (value : U64) : cbor_raw := .CBOR_Case_Int (cbor_int.mk cbor_major_type_uint64 size value)
def bytes (size : U8) (payload : Slice U8) : cbor_raw := .CBOR_Case_String (cbor_string.mk cbor_major_type_byte_string size payload)

theorem uint_major (size : U8) (value : U64) : cbordetver.cbor_det_major_type (uint size value) = .ok cbor_major_type_uint64 := rfl

theorem bytes_major (size : U8) (payload : Slice U8) : cbordetver.cbor_det_major_type (bytes size payload) = .ok cbor_major_type_byte_string := rfl

theorem array_major (payload : Slice U8) : cbordetver.cbor_det_major_type (array8 payload) = .ok cbor_major_type_array := rfl

theorem uint_view (size : U8) (value : U64) :
    cbordetver.cbor_det_destruct (uint size value) = .ok (.Int64 .UInt64 value) := by
  simp [cbordetver.cbor_det_destruct, cbordetver.cbor_det_major_type, impl_major_type,
    cbordetver.extraction_destruct_scalar_0, cbordetver.extraction_destruct_branch_3,
    cbordetver.extraction_destruct_scalar_1, cbordetver.extraction_destruct_match_2,
    uint, cbor_major_type_uint64, bind_tc_ok]

theorem bytes_view (size : U8) (payload : Slice U8) :
    cbordetver.cbor_det_destruct (bytes size payload) = .ok (.String .ByteString payload) := by
  simp [cbordetver.cbor_det_destruct, cbordetver.cbor_det_major_type, impl_major_type,
    cbordetver.extraction_destruct_scalar_0, cbordetver.extraction_destruct_branch_20,
    cbordetver.extraction_destruct_scalar_4, cbordetver.extraction_destruct_branch_7,
    cbordetver.extraction_destruct_scalar_5, cbordetver.extraction_destruct_match_6,
    bytes, cbor_major_type_uint64, cbor_major_type_neg_int64, cbor_major_type_byte_string, bind_tc_ok]

theorem array_view (payload : Slice U8) :
    cbordetver.cbor_det_destruct (array8 payload) = .ok (.Array (array8 payload)) := by
  simp [cbordetver.cbor_det_destruct, cbordetver.cbor_det_major_type, impl_major_type, array8,
    cbordetver.extraction_destruct_scalar_0, cbordetver.extraction_destruct_branch_20,
    cbordetver.extraction_destruct_scalar_4, cbordetver.extraction_destruct_branch_19,
    cbordetver.extraction_destruct_scalar_8, cbordetver.extraction_destruct_branch_9,
    cbor_major_type_uint64, cbor_major_type_neg_int64, cbor_major_type_byte_string,
    cbor_major_type_text_string, cbor_major_type_array, bind_tc_ok]

theorem array_start (payload : Slice U8) :
    cbordetver.cbor_det_array_iterator_start (array8 payload) = .ok (iterator payload 8#u64) := rfl

theorem uint_validate (size : U8) (value : U64) : transport.validate_uint (uint size value) = .ok true := by
  simp [transport.validate_uint, uint_major, bind_tc_ok]

theorem bytes_validate (size : U8) (payload : Slice U8) : transport.validate_bstr (bytes size payload) = .ok true := by
  simp [transport.validate_bstr, bytes_major, bind_tc_ok]

theorem uint_parse (size : U8) (value : U64) : transport.parse_uint (uint size value) = .ok value := by
  simp [transport.parse_uint, uint_view, transport.evercddl_uint_right, bind_tc_ok]

theorem bytes_parse (size : U8) (payload : Slice U8) : transport.parse_bstr (bytes size payload) = .ok payload := by
  simp [transport.parse_bstr, bytes_view, transport.bstr_right, bind_tc_ok]

theorem sub_small (count : Nat) (bound : count < 8) :
    U64.wrapping_sub (U64.ofNat (count + 1) (by scalar_tac)) 1#u64 = U64.ofNat count (by scalar_tac) := by
  interval_cases count <;> apply UScalar.eq_of_val_eq <;>
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
end BeaconcryptCore.Refinement.RegistrationSchemaViews

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.array_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.array_major

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_view

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_view

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.array_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.array_view

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.array_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.array_start

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_validate

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_validate

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.uint_parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.bytes_parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaViews.sub_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaViews.sub_small
