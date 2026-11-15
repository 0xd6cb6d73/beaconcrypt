import BeaconcryptCore.RegistrationPrimitiveExtraction.Funs

set_option warningAsError true

/-!
Payload-preservation and malformed-case equations for the actual generated CBOR
argument dispatcher. These are source primitive facts used by later field and
whole-registration readback proofs; they do not assert public codec readback.
-/

namespace BeaconcryptCore.Refinement.RegistrationPrimitiveHeader

open Aeneas.Std
open beaconcrypt_parse.cbordetveraux

theorem argument_u8 (header : initial_byte_t) (value : U8) :
    argument_as_uint64 header (.LongArgumentU8 value) =
      .ok (UScalar.cast .U64 value) := rfl

theorem argument_u16 (header : initial_byte_t) (value : U16) :
    argument_as_uint64 header (.LongArgumentU16 value) =
      .ok (UScalar.cast .U64 value) := rfl

theorem argument_u32 (header : initial_byte_t) (value : U32) :
    argument_as_uint64 header (.LongArgumentU32 value) =
      .ok (UScalar.cast .U64 value) := rfl

theorem argument_u64 (header : initial_byte_t) (value : U64) :
    argument_as_uint64 header (.LongArgumentU64 value) = .ok value := rfl

theorem argument_short (header : initial_byte_t) :
    argument_as_uint64 header .LongArgumentOther =
      .ok (UScalar.cast .U64 header.additional_info) := rfl

theorem argument_simple_rejected (header : initial_byte_t) (value : U8) :
    argument_as_uint64 header (.LongArgumentSimpleValue value) = .fail .panic := rfl

theorem init_fields (identity pre oneTime pq : Slice U8) :
    beaconcrypt_parse.transport.initkex_right
      ((), ((), (identity, (pre, (oneTime, pq))))) =
      .ok {
        identity_key := identity, pre_key := pre, one_time_key := oneTime,
        pq_key := pq } := rfl

theorem response_fields (identity ephemeral kem app signature : Slice U8) (keyId : U64) :
    beaconcrypt_parse.transport.kexresponse_right
      ((), ((), (identity, (ephemeral, (kem, (app, (keyId, signature))))))) =
      .ok {
        identity_key := identity, ephemeral_key := ephemeral, kem_cipher_text := kem,
        app_cipher_text := app, key_id := keyId, signature := signature } := rfl

/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_u8' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_u8
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_u16' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_u16
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_u32' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_u32
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_u64' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_u64
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_short' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_short
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.argument_simple_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms argument_simple_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.init_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms init_fields
/-- info: 'BeaconcryptCore.Refinement.RegistrationPrimitiveHeader.response_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms response_fields

end BeaconcryptCore.Refinement.RegistrationPrimitiveHeader
