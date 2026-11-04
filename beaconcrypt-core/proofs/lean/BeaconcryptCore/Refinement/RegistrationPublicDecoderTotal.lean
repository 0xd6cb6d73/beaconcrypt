-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAcceptedSyntax
import BeaconcryptCore.Refinement.RegistrationCanonicalDecoder
import BeaconcryptCore.Refinement.RegistrationDecoderBranchIndependence
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal
open beaconcrypt_parse cbordetveraux RegistrationPreflightRecords

def InitResult (input : Slice U8) : core.option.Option transport.initkex → Prop
  | .None => True
  | .Some value => RegistrationSerializerInitBytes.InitShape value ∧
      input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value ∧ input.length ≤ 33554432

def ResponseResult (input : Slice U8) : core.option.Option transport.kexresponse → Prop
  | .None => True
  | .Some value => RegistrationSerializerResponseBytes.ResponseShape value ∧
      input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value ∧ input.length ≤ 33554432

set_option backward.isDefEq.respectTransparency false in
theorem width_false [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (source : cbor_validate_det input = RegistrationDecoderBranchIndependence.widthResult input)
    (failed : extraction_canonical_scan_0 input = .ok false) :
    cbor_validate_det input = .ok 0#usize := by
  rw [source, RegistrationDecoderBranchIndependence.widthResult]
  by_cases zero : input.len = 0#usize
  · simp only [zero, ↓reduceIte]
  · simp only [zero, ↓reduceIte, failed, bind_tc_ok, Bool.false_eq_true]

set_option backward.isDefEq.respectTransparency false in
theorem init_preflight_none [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input initStart
      ((Array.repeat 6#usize 2#u8).to_slice) = .ok .None) :
    extraction_decode_init input = .ok .None := by
  dsimp only [initStart] at gate
  simp only [extraction_decode_init, lift, gate, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

set_option backward.isDefEq.respectTransparency false in
theorem response_preflight_none [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok .None) :
    extraction_decode_response input = .ok .None := by
  dsimp only [responseStart] at gate
  simp only [extraction_decode_response, lift, gate, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

set_option backward.isDefEq.respectTransparency false in
theorem init_nonminimal [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input initStart
      ((Array.repeat 6#usize 2#u8).to_slice) = .ok (.Some ()))
    (failed : extraction_canonical_scan_0 input = .ok false) :
    extraction_decode_init input = .ok .None := by
  have rejected := width_false input (RegistrationDecoderBranchIndependence.init_det input gate) failed
  dsimp only [initStart] at gate
  simp only [extraction_decode_init, lift, gate, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    transport.validate_and_parse_initkex, cbordetver.cbor_det_parse, rejected, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem response_nonminimal [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ()))
    (failed : extraction_canonical_scan_0 input = .ok false) :
    extraction_decode_response input = .ok .None := by
  have rejected := width_false input (RegistrationDecoderBranchIndependence.response_det input gate) failed
  dsimp only [responseStart] at gate
  simp only [extraction_decode_response, lift, gate, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    transport.validate_and_parse_kexresponse, cbordetver.cbor_det_parse, rejected, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem init_total [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    ∃ reply, extraction_decode_init input = .ok reply ∧ InitResult input reply := by
  obtain ⟨result, run⟩ := RegistrationPreflightTotal.complete_total input initStart 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8
  have gate : registration_validator_primitive.preflightSlice input initStart ((Array.repeat 6#usize 2#u8).to_slice) = .ok result := by
    rw [RegistrationPublicDecoderControl.preflight_array, ← init_kinds_source]
    exact run
  cases result with
  | none => exact ⟨.None, init_preflight_none input gate, True.intro⟩
  | some item =>
    cases item
    have admittedGate := gate
    rw [RegistrationPublicDecoderControl.preflight_array, ← init_kinds_source] at admittedGate
    obtain ⟨values, length, contents, _⟩ := RegistrationPreflightValidation.atoms input initStart false 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8
      (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) rfl admittedGate
    have width := RegistrationLooseWidthTrace.scan input values length contents
    cases minimal : values.all RegistrationLooseWidthTrace.atomMinimal with
    | false =>
      rw [minimal] at width
      exact ⟨.None, init_nonminimal input gate width, True.intro⟩
    | true =>
      rw [minimal] at width
      obtain ⟨recordValue, bytes, admitted⟩ := RegistrationAcceptedSyntax.init input gate width
      have source := RegistrationCanonicalDecoder.init input recordValue bytes admitted
      by_cases shape : RegistrationSerializerInitBytes.InitShape recordValue
      · rw [ite_eq_left shape] at source
        exact ⟨.Some recordValue, source, shape, bytes, admitted⟩
      · rw [ite_eq_right shape] at source
        exact ⟨.None, source, True.intro⟩

set_option backward.isDefEq.respectTransparency false in
theorem response_total [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    ∃ reply, extraction_decode_response input = .ok reply ∧ ResponseResult input reply := by
  obtain ⟨result, run⟩ := RegistrationPreflightTotal.complete_total input responseStart 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8
  have gate : registration_validator_primitive.preflightSlice input responseStart ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok result := by
    rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source]
    exact run
  cases result with
  | none => exact ⟨.None, response_preflight_none input gate, True.intro⟩
  | some item =>
    cases item
    have admittedGate := gate
    rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source] at admittedGate
    obtain ⟨values, length, contents, _⟩ := RegistrationPreflightValidation.atoms input responseStart true 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8
      (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) rfl admittedGate
    have width := RegistrationLooseWidthTrace.scan input values length contents
    cases minimal : values.all RegistrationLooseWidthTrace.atomMinimal with
    | false =>
      rw [minimal] at width
      exact ⟨.None, response_nonminimal input gate width, True.intro⟩
    | true =>
      rw [minimal] at width
      obtain ⟨recordValue, bytes, admitted⟩ := RegistrationAcceptedSyntax.response input gate width
      have source := RegistrationCanonicalDecoder.response input recordValue bytes admitted
      by_cases shape : RegistrationSerializerResponseBytes.ResponseShape recordValue
      · rw [ite_eq_left shape] at source
        exact ⟨.Some recordValue, source, shape, bytes, admitted⟩
      · rw [ite_eq_right shape] at source
        exact ⟨.None, source, True.intro⟩

set_option backward.isDefEq.respectTransparency false in
theorem init_some [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex)
    (accepted : extraction_decode_init input = .ok (.Some value)) :
    RegistrationSerializerInitBytes.InitShape value ∧ input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value ∧ input.length ≤ 33554432 := by
  obtain ⟨reply, run, facts⟩ := init_total input
  have same := RustM.ok.inj (run.symm.trans accepted)
  simpa only [same, InitResult] using facts

set_option backward.isDefEq.respectTransparency false in
theorem init_iff [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.initkex) :
    extraction_decode_init input = .ok (.Some value) ↔
      RegistrationSerializerInitBytes.InitShape value ∧ input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value ∧ input.length ≤ 33554432 := by
  constructor
  · exact init_some input value
  · rintro ⟨shape, contents, admitted⟩
    have source := RegistrationCanonicalDecoder.init input value contents admitted
    rw [ite_eq_left shape] at source
    exact source

set_option backward.isDefEq.respectTransparency false in
theorem init_none_iff [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    extraction_decode_init input = .ok .None ↔
      ¬ ∃ value : transport.initkex, RegistrationSerializerInitBytes.InitShape value ∧
        input.val = 136#u8 :: RegistrationSerializerInitBytes.payload value ∧ input.length ≤ 33554432 := by
  constructor
  · intro rejected ⟨value, valid⟩
    have accepted := (init_iff input value).mpr valid
    have impossible := RustM.ok.inj (rejected.symm.trans accepted)
    cases impossible
  · intro malformed
    obtain ⟨reply, run, facts⟩ := init_total input
    cases reply with
    | none => exact run
    | some value => exact False.elim (malformed ⟨value, facts⟩)

set_option backward.isDefEq.respectTransparency false in
theorem response_some [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse)
    (accepted : extraction_decode_response input = .ok (.Some value)) :
    RegistrationSerializerResponseBytes.ResponseShape value ∧ input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value ∧ input.length ≤ 33554432 := by
  obtain ⟨reply, run, facts⟩ := response_total input
  have same := RustM.ok.inj (run.symm.trans accepted)
  simpa only [same, ResponseResult] using facts

set_option backward.isDefEq.respectTransparency false in
theorem response_iff [RegistrationValidatorPrimitive.Operations] (input : Slice U8) (value : transport.kexresponse) :
    extraction_decode_response input = .ok (.Some value) ↔
      RegistrationSerializerResponseBytes.ResponseShape value ∧ input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value ∧ input.length ≤ 33554432 := by
  constructor
  · exact response_some input value
  · rintro ⟨shape, contents, admitted⟩
    have source := RegistrationCanonicalDecoder.response input value contents admitted
    rw [ite_eq_left shape] at source
    exact source

set_option backward.isDefEq.respectTransparency false in
theorem response_none_iff [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    extraction_decode_response input = .ok .None ↔
      ¬ ∃ value : transport.kexresponse, RegistrationSerializerResponseBytes.ResponseShape value ∧
        input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload value ∧ input.length ≤ 33554432 := by
  constructor
  · intro rejected ⟨value, valid⟩
    have accepted := (response_iff input value).mpr valid
    have impossible := RustM.ok.inj (rejected.symm.trans accepted)
    cases impossible
  · intro malformed
    obtain ⟨reply, run, facts⟩ := response_total input
    cases reply with
    | none => exact run
    | some value => exact False.elim (malformed ⟨value, facts⟩)
end BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.width_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.width_false

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_preflight_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_preflight_none

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_preflight_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_preflight_none

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_nonminimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_nonminimal

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_nonminimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_nonminimal

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_total

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_some

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_iff

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.init_none_iff

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_some

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_iff

/-- info: 'BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_none_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal.response_none_iff
