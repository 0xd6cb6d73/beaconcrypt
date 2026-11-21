-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightValidation
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence
open beaconcrypt_parse cbordetveraux RegistrationPreflightRecords

/-- An analysis normal form retaining the original complete canonical-width scan. -/
def widthResult (input : Slice U8) : RustM Usize :=
  if input.len = 0#usize then .ok input.len else do
    let minimal ← extraction_canonical_scan_0 input
    if minimal then .ok input.len else .ok 0#usize

set_option backward.isDefEq.respectTransparency false in
theorem det_of_checks [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (raw : cbor_validate input = .ok input.len)
    (sorted : extraction_canonical_scan_1 input = .ok true) :
    cbor_validate_det input = widthResult input := by
  simp only [cbor_validate_det, bcExtractedToken63626f725f76616c69646174655f646574c2b7,
    raw, bind_tc_ok, widthResult]
  by_cases zero : input.len = 0#usize
  · simp only [zero, ↓reduceIte]
  · simp only [zero, ↓reduceIte, RegistrationFlatSkip.split_zero, bind_tc_ok, uncurry,
      RegistrationHeaderValidation.sub_source, RegistrationArrayRotation.sub_zero,
      RegistrationRawTrace.split_full, lift, lowstar.ignore.bcSchemaRepeatedIgnore2, sorted]

set_option backward.isDefEq.respectTransparency false in
theorem init_det [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input initStart
      ((Array.repeat 4#usize 2#u8).to_slice) = .ok (.Some ())) :
    cbor_validate_det input = widthResult input := by
  obtain ⟨raw, sorted⟩ := RegistrationPreflightValidation.init_checks input accepted
  exact det_of_checks input raw sorted

set_option backward.isDefEq.respectTransparency false in
theorem response_det [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ())) :
    cbor_validate_det input = widthResult input := by
  obtain ⟨raw, sorted⟩ := RegistrationPreflightValidation.response_checks input accepted
  exact det_of_checks input raw sorted

set_option backward.isDefEq.respectTransparency false in
theorem init_schema_independent (left right : RegistrationValidatorPrimitive.Operations) (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input initStart
      ((Array.repeat 4#usize 2#u8).to_slice) = .ok (.Some ())) :
    @transport.validate_and_parse_initkex left input = @transport.validate_and_parse_initkex right input := by
  have same := (@init_det left input accepted).trans (@init_det right input accepted).symm
  simp only [transport.validate_and_parse_initkex, cbordetver.cbor_det_parse, same]

set_option backward.isDefEq.respectTransparency false in
theorem response_schema_independent (left right : RegistrationValidatorPrimitive.Operations) (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ())) :
    @transport.validate_and_parse_kexresponse left input = @transport.validate_and_parse_kexresponse right input := by
  have same := (@response_det left input accepted).trans (@response_det right input accepted).symm
  simp only [transport.validate_and_parse_kexresponse, cbordetver.cbor_det_parse, same]

set_option backward.isDefEq.respectTransparency false in
theorem init_independent (left right : RegistrationValidatorPrimitive.Operations) (input : Slice U8) :
    @extraction_decode_init left input = @extraction_decode_init right input := by
  obtain ⟨result, run⟩ := RegistrationPreflightTotal.complete_total_four input initStart 2#u8 2#u8 2#u8 2#u8
  have gate : registration_validator_primitive.preflightSlice input initStart
      ((Array.repeat 4#usize 2#u8).to_slice) = .ok result := by
    rw [RegistrationPublicDecoderControl.preflight_array_four, ← init_kinds_source]
    exact run
  cases result with
  | none =>
    dsimp only [initStart] at gate
    simp only [extraction_decode_init, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  | some item =>
    cases item
    have schema := init_schema_independent left right input gate
    dsimp only [initStart] at gate
    simp only [extraction_decode_init, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, schema]

set_option backward.isDefEq.respectTransparency false in
theorem response_independent (left right : RegistrationValidatorPrimitive.Operations) (input : Slice U8) :
    @extraction_decode_response left input = @extraction_decode_response right input := by
  obtain ⟨result, run⟩ := RegistrationPreflightTotal.complete_total input responseStart 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8
  have gate : registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok result := by
    rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source]
    exact run
  cases result with
  | none =>
    dsimp only [responseStart] at gate
    simp only [extraction_decode_response, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  | some item =>
    cases item
    have schema := response_schema_independent left right input gate
    dsimp only [responseStart] at gate
    simp only [extraction_decode_response, lift, gate, bind_tc_ok,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, schema]

end BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.det_of_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.det_of_checks

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_det

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_det

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_schema_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_schema_independent

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_schema_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_schema_independent

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.init_independent

/-- info: 'BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence.response_independent
