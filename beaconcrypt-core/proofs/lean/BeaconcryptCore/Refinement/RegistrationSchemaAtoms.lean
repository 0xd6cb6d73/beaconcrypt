-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaViews
import BeaconcryptCore.Refinement.RegistrationSerializerResponseBytes
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The complete actual serializer payloads are precisely six Init or eight Response canonical primitive atoms. Therefore the original raw/canonical parser reconstructs the actual serialized array with complete consumption for every source Init or Response payload, independently of the unselected text/map effects. Schema field checks and public preflight remain separate. -/
namespace BeaconcryptCore.Refinement.RegistrationSchemaAtoms
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationCanonicalTrace RegistrationArrayReadback RegistrationFlatSkip

def initAtoms (value : transport.initkex) : List Atom := [ .uint 3#u64, .uint 0#u64,
  .bytes value.identity_key, .bytes value.pre_key, .bytes value.one_time_key,
  .bytes value.pq_key ]

def responseAtoms (value : transport.kexresponse) : List Atom := [ .uint 3#u64, .uint 1#u64,
  .bytes value.identity_key, .bytes value.ephemeral_key, .bytes value.kem_cipher_text,
  .bytes value.app_cipher_text, .uint value.key_id, .bytes value.signature ]

theorem init_length (value : transport.initkex) : (initAtoms value).length = 6 := rfl
theorem response_length (value : transport.kexresponse) : (responseAtoms value).length = 8 := rfl

theorem init_bytes (value : transport.initkex) :
    atomsBytes (initAtoms value) = RegistrationSerializerInitBytes.payload value := by
  simp only [initAtoms, atomsBytes, atomBytes, RegistrationSerializerInitBytes.encoded_three,
    RegistrationSerializerInitBytes.encoded_zero, RegistrationSerializerInitBytes.payload,
    RegistrationSerializerInitBytes.fieldBytes, List.cons_append, List.nil_append, List.append_nil,
    List.append_assoc]

theorem response_bytes (value : transport.kexresponse) :
    atomsBytes (responseAtoms value) = RegistrationSerializerResponseBytes.payload value := by
  simp only [responseAtoms, atomsBytes, atomBytes, RegistrationSerializerInitBytes.encoded_three,
    RegistrationSerializerResponseBytes.encoded_one, RegistrationSerializerResponseBytes.payload,
    RegistrationSerializerInitBytes.fieldBytes, List.cons_append, List.nil_append, List.append_nil,
    List.append_assoc]

theorem array_header : encodedBytes cbor_major_type_array 8#u64 = [136#u8] := by
  have cast : UScalar.cast .U8 8#u64 = 8#u8 := by
    apply UScalar.eq_of_val_eq
    rw [cast_value .U8 8#u64 (by scalar_tac)]
    rfl
  simp only [encodedBytes, show (8#u64).val < 24 by scalar_tac, ↓reduceIte,
    cast, cbor_major_type_array]
  rfl

theorem array_header6 : encodedBytes cbor_major_type_array 6#u64 = [134#u8] := by
  have cast : UScalar.cast .U8 6#u64 = 6#u8 := by
    apply UScalar.eq_of_val_eq
    rw [cast_value .U8 6#u64 (by scalar_tac)]
    rfl
  simp only [encodedBytes, show (6#u64).val < 24 by scalar_tac, ↓reduceIte,
    cast, cbor_major_type_array]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem init_parsed [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value) :
    ∃ payload, payload.val = RegistrationSerializerInitBytes.payload value ∧
      cbordetver.cbor_det_parse input = .ok (.Some (array6 payload, empty)) := by
  apply RegistrationArrayReadback.parse6 input (initAtoms value) (init_length value) ?_ |>.imp (by
    intro payload facts
    simpa only [init_bytes] using facts)
  simpa only [array_header6, init_bytes, List.cons_append, List.nil_append] using contents

set_option backward.isDefEq.respectTransparency false in
theorem response_parsed [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value) :
    ∃ payload, payload.val = RegistrationSerializerResponseBytes.payload value ∧
      cbordetver.cbor_det_parse input = .ok (.Some (array8 payload, empty)) := by
  apply RegistrationArrayReadback.parse input (responseAtoms value) (response_length value) ?_ |>.imp (by
    intro payload facts
    simpa only [response_bytes] using facts)
  simpa only [array_header, response_bytes, List.cons_append, List.nil_append] using contents
end BeaconcryptCore.Refinement.RegistrationSchemaAtoms

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_bytes

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.array_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.array_header

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.init_parsed

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.response_parsed

/-- info: 'BeaconcryptCore.Refinement.RegistrationSchemaAtoms.array_header6' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSchemaAtoms.array_header6
