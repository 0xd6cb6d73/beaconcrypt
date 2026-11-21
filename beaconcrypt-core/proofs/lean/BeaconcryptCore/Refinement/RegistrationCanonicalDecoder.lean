-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSchemaValidationTotal
import BeaconcryptCore.Refinement.RegistrationPublicReadback
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationCanonicalDecoder
open beaconcrypt_parse RegistrationPreflightRecords

local instance (value : transport.initkex) : Decidable (RegistrationSerializerInitBytes.InitShape value) := by
  unfold RegistrationSerializerInitBytes.InitShape
  infer_instance
local instance (value : transport.kexresponse) : Decidable (RegistrationSerializerResponseBytes.ResponseShape value) := by
  unfold RegistrationSerializerResponseBytes.ResponseShape
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem init_schema_rejected [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value)
    (malformed : ¬ RegistrationSerializerInitBytes.InitShape value) :
    transport.validate_and_parse_initkex input = .ok .None := by
  obtain ⟨payload, payloadBytes, parsed⟩ := RegistrationSchemaAtoms.init_parsed input value contents
  obtain ⟨work⟩ := RegistrationSchemaInitStages.stages value payload payloadBytes
  simp only [transport.validate_and_parse_initkex, parsed, bind_tc_ok, uncurry,
    RegistrationSchemaValidationTotal.init value payload work, malformed, decide_false,
    Bool.false_eq_true, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem response_schema_rejected [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (malformed : ¬ RegistrationSerializerResponseBytes.ResponseShape value) :
    transport.validate_and_parse_kexresponse input = .ok .None := by
  obtain ⟨payload, payloadBytes, parsed⟩ := RegistrationSchemaAtoms.response_parsed input value contents
  obtain ⟨work⟩ := RegistrationSchemaResponseStages.stages value payload payloadBytes
  simp only [transport.validate_and_parse_kexresponse, parsed, bind_tc_ok, uncurry,
    RegistrationSchemaValidationTotal.response value payload work, malformed, decide_false,
    Bool.false_eq_true, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem init [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload value)
    (admitted : input.length ≤ 33554432) :
    extraction_decode_init input = .ok (if RegistrationSerializerInitBytes.InitShape value then .Some value else .None) := by
  by_cases shape : RegistrationSerializerInitBytes.InitShape value
  · rw [ite_eq_left shape]
    exact RegistrationPublicReadback.decode_init input value contents shape
  · rw [ite_eq_right shape]
    have gate : registration_validator_primitive.preflightSlice input initStart
        ((Array.repeat 4#usize 2#u8).to_slice) = .ok (.Some ()) := by
      rw [RegistrationPublicDecoderControl.preflight_array_four, ← init_kinds_source]
      exact RegistrationPreflightRecords.init input value contents admitted
    have rejected := init_schema_rejected input value contents shape
    dsimp only [initStart] at gate
    simp only [extraction_decode_init, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, rejected]

set_option backward.isDefEq.respectTransparency false in
theorem response [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value)
    (admitted : input.length ≤ 33554432) :
    extraction_decode_response input = .ok (if RegistrationSerializerResponseBytes.ResponseShape value then .Some value else .None) := by
  by_cases shape : RegistrationSerializerResponseBytes.ResponseShape value
  · rw [ite_eq_left shape]
    have length : input.length = RegistrationSerializerResponseBytes.totalLength value := by
      rw [Slice.length, contents, List.length_cons]
      exact RegistrationPublicReadback.response_payload_length value shape
    exact RegistrationPublicReadback.decode_response input value contents shape (by rw [← length]; exact admitted)
  · rw [ite_eq_right shape]
    have gate : registration_validator_primitive.preflightSlice input responseStart
        ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ()) := by
      rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source]
      exact RegistrationPreflightRecords.response input value contents admitted
    have rejected := response_schema_rejected input value contents shape
    dsimp only [responseStart] at gate
    simp only [extraction_decode_response, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, rejected]
end BeaconcryptCore.Refinement.RegistrationCanonicalDecoder

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.init_schema_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.init_schema_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.response_schema_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.response_schema_rejected

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCanonicalDecoder.response
