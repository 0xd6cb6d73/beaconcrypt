-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightRecords
import BeaconcryptCore.Refinement.RegistrationSchemaInitStages
import BeaconcryptCore.Refinement.RegistrationSchemaResponseStages
import BeaconcryptCore.Refinement.RegistrationPublicDecoderControl
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPublicReadback
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationPreflightRecords

theorem init_payload_length (value : transport.initkex) (shape : RegistrationSerializerInitBytes.InitShape value) :
    (RegistrationSerializerInitBytes.payload value).length = 1489 := by
  rcases shape with ⟨identityLength, preLength, oneTimeLength, pqLength⟩
  simp only [Slice.length] at identityLength preLength oneTimeLength pqLength
  simp [RegistrationSerializerInitBytes.payload, RegistrationSerializerInitBytes.fieldBytes,
    encoded_length, writtenCount,
    identityLength, preLength, oneTimeLength, pqLength]

theorem response_payload_length (value : transport.kexresponse) (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    (RegistrationSerializerResponseBytes.payload value).length + 1 = RegistrationSerializerResponseBytes.totalLength value := by
  rcases shape with ⟨identityLength, ephemeralLength, kemLength, signatureLength⟩
  simp only [Slice.length] at identityLength ephemeralLength kemLength signatureLength
  have identityHeader : (writtenCount (UScalar.cast .U64 value.identity_key.len)).val = 2 := by
    simp [writtenCount,   identityLength]
  have ephemeralHeader : (writtenCount (UScalar.cast .U64 value.ephemeral_key.len)).val = 2 := by
    simp [writtenCount,   ephemeralLength]
  have kemHeader : (writtenCount (UScalar.cast .U64 value.kem_cipher_text.len)).val = 3 := by
    simp [writtenCount,   kemLength]
  have signatureHeader : (writtenCount (UScalar.cast .U64 value.signature.len)).val = 3 := by
    simp [writtenCount,   signatureLength]
  simp only [RegistrationSerializerResponseBytes.payload, RegistrationSerializerInitBytes.fieldBytes,
    List.length_append, List.length_cons, List.length_nil, encoded_length,
    identityHeader, ephemeralHeader, kemHeader, signatureHeader,
    RegistrationSerializerResponseBytes.totalLength, RegistrationSerializerResponseBytes.bodyLength,
    RegistrationSerializerResponseBytes.applicationLength, RegistrationSerializerResponseBytes.keyLength,
    Slice.length, identityLength, ephemeralLength, kemLength, signatureLength]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem preflight_init (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    registration_validator_primitive.preflightSlice input initStart ((Array.repeat 4#usize 2#u8).to_slice) = .ok (.Some ()) := by
  rw [RegistrationPublicDecoderControl.preflight_array_four, ← init_kinds_source]
  apply RegistrationPreflightRecords.init input value contents
  have length : input.length = 1490 := by
    rw [Slice.length, contents, List.length_cons, init_payload_length value shape]
  omega

set_option backward.isDefEq.respectTransparency false in
theorem preflight_response (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value)
    (admitted : RegistrationSerializerResponseBytes.totalLength value ≤ BeaconcryptCore.Computational.CborSizing.maxMessageSize) :
    registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ()) := by
  rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source]
  apply RegistrationPreflightRecords.response input value contents
  have length : input.length = RegistrationSerializerResponseBytes.totalLength value := by
    rw [Slice.length, contents, List.length_cons]
    exact response_payload_length value shape
  rw [length]
  exact admitted

set_option backward.isDefEq.respectTransparency false in
theorem decode_init [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value)
    (shape : RegistrationSerializerInitBytes.InitShape value) :
    extraction_decode_init input = .ok (.Some value) := by
  have gate := preflight_init input value contents shape
  dsimp only [initStart] at gate
  have parsed := RegistrationSchemaInitStages.validated input value contents shape
  simp only [extraction_decode_init, lift, bind_tc_ok, gate,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    parsed, uncurry, RegistrationPublicDecoderControl.empty_rest,
    RegistrationPublicDecoderControl.emptyPattern, RegistrationFlatSkip.empty, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem decode_response [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value)
    (admitted : RegistrationSerializerResponseBytes.totalLength value ≤ BeaconcryptCore.Computational.CborSizing.maxMessageSize) :
    extraction_decode_response input = .ok (.Some value) := by
  have gate := preflight_response input value contents shape admitted
  dsimp only [responseStart] at gate
  have parsed := RegistrationSchemaResponseStages.validated input value contents shape
  simp only [extraction_decode_response, lift, bind_tc_ok, gate,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    parsed, uncurry, RegistrationPublicDecoderControl.empty_rest,
    RegistrationPublicDecoderControl.emptyPattern, RegistrationFlatSkip.empty, ↓reduceIte]
end BeaconcryptCore.Refinement.RegistrationPublicReadback

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.init_payload_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.init_payload_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.response_payload_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.response_payload_length

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.preflight_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.preflight_init

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.preflight_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.preflight_response

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.decode_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.decode_init

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicReadback.decode_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicReadback.decode_response
