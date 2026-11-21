-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaAtoms
import BeaconcryptCore.Refinement.RegistrationSchemaTransitions
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Eight byte-derived source iterator transitions drive the original Response schema validator and parser, retaining every original check, truncated reread, mutable update and field projection. Application payloads and key identifiers are arbitrary. The final original validate_and_parse_kexresponse result reconstructs all six input fields with an empty remainder; public preflight is composed separately. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaResponseStages
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationCanonicalTrace RegistrationSchemaAtoms
open RegistrationSchemaIteratorReadback RegistrationSchemaViews RegistrationSchemaTransitions RegistrationCodecArraySingleton

structure Stages (value : transport.kexresponse) (payload : Slice U8) where
  size0 : U8
  first : Transition payload (uint size0 3#u64)
  size1 : U8
  second : Transition first.tail (uint size1 1#u64)
  size2 : U8
  identity : Transition second.tail (bytes size2 value.identity_key)
  size3 : U8
  ephemeral : Transition identity.tail (bytes size3 value.ephemeral_key)
  size4 : U8
  kem : Transition ephemeral.tail (bytes size4 value.kem_cipher_text)
  size5 : U8
  application : Transition kem.tail (bytes size5 value.app_cipher_text)
  size6 : U8
  key : Transition application.tail (uint size6 value.key_id)
  size7 : U8
  signature : Transition key.tail (bytes size7 value.signature)
  consumed : signature.tail.val = []

set_option backward.isDefEq.respectTransparency false in
theorem stages (value : transport.kexresponse) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerResponseBytes.payload value) :
    Nonempty (Stages value payload) := by
  have whole : payload.val = atomsBytes (responseAtoms value) := by rw [response_bytes]; exact contents
  obtain ⟨size0, first, firstBytes⟩ := uint_transition payload 3#u64
    (atomsBytes [ .uint 1#u64, .bytes value.identity_key, .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using whole)
  obtain ⟨size1, second, secondBytes⟩ := uint_transition first.tail 1#u64
    (atomsBytes [ .bytes value.identity_key, .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using firstBytes)
  obtain ⟨size2, identity, identityBytes⟩ := bytes_transition second.tail value.identity_key
    (atomsBytes [ .bytes value.ephemeral_key, .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using secondBytes)
  obtain ⟨size3, ephemeral, ephemeralBytes⟩ := bytes_transition identity.tail value.ephemeral_key
    (atomsBytes [ .bytes value.kem_cipher_text, .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using identityBytes)
  obtain ⟨size4, kem, kemBytes⟩ := bytes_transition ephemeral.tail value.kem_cipher_text
    (atomsBytes [ .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using ephemeralBytes)
  obtain ⟨size5, application, applicationBytes⟩ := bytes_transition kem.tail value.app_cipher_text
    (atomsBytes [ .uint value.key_id, .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using kemBytes)
  obtain ⟨size6, key, keyBytes⟩ := uint_transition application.tail value.key_id
    (atomsBytes [ .bytes value.signature ]) (by simpa only [responseAtoms, atomsBytes, atomBytes] using applicationBytes)
  obtain ⟨size7, signature, signatureBytes⟩ := bytes_transition key.tail value.signature
    (atomsBytes []) (by simpa only [responseAtoms, atomsBytes, atomBytes] using keyBytes)
  exact ⟨{
    size0 := size0
    first := first
    size1 := size1
    second := second
    size2 := size2
    identity := identity
    size3 := size3
    ephemeral := ephemeral
    size4 := size4
    kem := kem
    size5 := size5
    application := application
    size6 := size6
    key := key
    size7 := size7
    signature := signature
    consumed := signatureBytes }⟩

theorem index_mut_pack {A : Type} (value : A) :
    Array.index_mut_usize (pack value) 0#usize = .ok (value, pack) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem validate (value : transport.kexresponse) (payload : Slice U8) (work : Stages value payload)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.validate_kexresponse (RegistrationArrayReadback.array8 payload) = .ok true := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  have dec7 : U64.wrapping_sub 7#u64 1#u64 = 6#u64 := sub_small 6 (by decide)
  have dec8 : U64.wrapping_sub 8#u64 1#u64 = 7#u64 := sub_small 7 (by decide)
  simp [transport.validate_kexresponse.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.bcSchemaRepeatedClosure5.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.bcSchemaRepeatedClosure4.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.bcSchemaRepeatedClosure3.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.bcSchemaRepeatedClosure2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.closure.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_1.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse.closure_2.Insts.bcExtractedToken436f72654f707346756e6374696f6e466e5475706c65417272617963626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f72617731426f6f6c.call,
    transport.validate_kexresponse,
    RegistrationArrayReadback.array8,
    array_major,
    array_view,
    array_start,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    index_mut_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.ephemeral.source,
    work.kem.source,
    work.application.source,
    work.key.source,
    work.signature.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    uint_validate,
    bytes_validate,


    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    identityLength,
    ephemeralLength,
    kemLength,
    signatureLength,
    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,
    dec7,
    dec8,
    bind_tc_ok,
    uncurry,
    cbor_major_type_uint64,
    cbor_major_type_byte_string,
    cbor_major_type_array]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem parse (value : transport.kexresponse) (payload : Slice U8) (work : Stages value payload)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.parse_kexresponse (RegistrationArrayReadback.array8 payload) = .ok value := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  have dec1 : U64.wrapping_sub 1#u64 1#u64 = 0#u64 := sub_small 0 (by decide)
  have dec2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := sub_small 1 (by decide)
  have dec3 : U64.wrapping_sub 3#u64 1#u64 = 2#u64 := sub_small 2 (by decide)
  have dec4 : U64.wrapping_sub 4#u64 1#u64 = 3#u64 := sub_small 3 (by decide)
  have dec5 : U64.wrapping_sub 5#u64 1#u64 = 4#u64 := sub_small 4 (by decide)
  have dec6 : U64.wrapping_sub 6#u64 1#u64 = 5#u64 := sub_small 5 (by decide)
  have dec7 : U64.wrapping_sub 7#u64 1#u64 = 6#u64 := sub_small 6 (by decide)
  have dec8 : U64.wrapping_sub 8#u64 1#u64 = 7#u64 := sub_small 7 (by decide)
  have gap2 : U64.wrapping_sub 2#u64 1#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap3 : U64.wrapping_sub 3#u64 2#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap4 : U64.wrapping_sub 4#u64 3#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap5 : U64.wrapping_sub 5#u64 4#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap6 : U64.wrapping_sub 6#u64 5#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap7 : U64.wrapping_sub 7#u64 6#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  have gap8 : U64.wrapping_sub 8#u64 7#u64 = 1#u64 := by
    apply UScalar.eq_of_val_eq
    norm_num [U64.wrapping_sub_val_eq, UScalar.size_def]
  simp [transport.kexresponse_right, transport.extraction_parse_kexresponse_check_6,
    transport.extraction_parse_kexresponse_check_5,
    transport.extraction_parse_kexresponse_check_4,
    transport.extraction_parse_kexresponse_check_3,
    transport.extraction_parse_kexresponse_check_2,
    transport.extraction_parse_kexresponse_check_1,
    transport.extraction_parse_kexresponse_check_0,
    transport.parse_kexresponse,
    RegistrationArrayReadback.array8,
    array_view,
    array_start,
    show Array.repeat 1#usize = @pack Iterator from rfl,
    index_pack,
    index_mut_pack,
    update_pack,
    RegistrationSchemaIteratorReadback.is_empty,
    RegistrationSchemaIteratorReadback.length,
    RegistrationSchemaIteratorReadback.truncate,
    sub_u64,
    lowstar.ignore.bcSchemaRepeatedIgnore2,
    work.first.source,
    work.second.source,
    work.identity.source,
    work.ephemeral.source,
    work.kem.source,
    work.application.source,
    work.key.source,
    work.signature.source,
    uint_major,
    bytes_major,
    uint_view,
    bytes_view,
    uint_validate,
    bytes_validate,
    uint_parse,
    bytes_parse,
    core.slice.Slice.len,
    rust_primitives.slice.slice_length,
    RegistrationSerializerFields.usize_lte_u64,
    RegistrationSerializerFields.u64_lte_usize,
    identityLength,
    ephemeralLength,
    kemLength,

    dec1,
    dec2,
    dec3,
    dec4,
    dec5,
    dec6,
    dec7,
    dec8,







    bind_tc_ok,
    uncurry,
    cbor_major_type_uint64,
    cbor_major_type_byte_string]

theorem validate_source (value : transport.kexresponse) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerResponseBytes.payload value)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.validate_kexresponse (RegistrationArrayReadback.array8 payload) = .ok true := by
  obtain ⟨work⟩ := stages value payload contents
  exact validate value payload work shape

theorem parse_source (value : transport.kexresponse) (payload : Slice U8)
    (contents : payload.val = RegistrationSerializerResponseBytes.payload value)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.parse_kexresponse (RegistrationArrayReadback.array8 payload) = .ok value := by
  obtain ⟨work⟩ := stages value payload contents
  exact parse value payload work shape

set_option backward.isDefEq.respectTransparency false in
theorem validated [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.validate_and_parse_kexresponse input = .ok (.Some (value, RegistrationFlatSkip.empty)) := by
  obtain ⟨payload, payloadBytes, source⟩ := response_parsed input value contents
  simp only [transport.validate_and_parse_kexresponse, source, bind_tc_ok, uncurry,
    validate_source value payload payloadBytes shape, ↓reduceIte,
    parse_source value payload payloadBytes shape]

end BeaconcryptCore.Refinement.RegistrationSchemaResponseStages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.stages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.stages

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.index_mut_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.index_mut_pack

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validate

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.parse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.parse

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validate_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.parse_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.parse_source

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaResponseStages.validated
