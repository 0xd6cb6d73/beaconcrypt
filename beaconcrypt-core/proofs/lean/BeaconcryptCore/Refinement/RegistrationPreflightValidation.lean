-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseRawTrace
import BeaconcryptCore.Refinement.RegistrationLooseOrderTrace
import BeaconcryptCore.Refinement.RegistrationPreflightRecords
import BeaconcryptCore.Refinement.RegistrationPublicDecoderControl
import BeaconcryptCore.Refinement.RegistrationSchemaAtoms
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightValidation
open beaconcrypt_parse cbordetveraux RegistrationPreflightSix RegistrationPreflightCoverage
open RegistrationLooseFieldSpan

def tagValue (response : Bool) : U8 := if response then 1#u8 else 0#u8

def tagForm (response : Bool) : RegistrationLooseArgument.Form :=
  .short (tagValue response) (by cases response <;> decide)

theorem atoms (input head : Slice U8) (response : Bool) (a0 a1 a2 a3 a4 a5 : U8)
    (allowed0 : a0 = 0#u8 ∨ a0 = 2#u8) (allowed1 : a1 = 0#u8 ∨ a1 = 2#u8)
    (allowed2 : a2 = 0#u8 ∨ a2 = 2#u8) (allowed3 : a3 = 0#u8 ∨ a3 = 2#u8)
    (allowed4 : a4 = 0#u8 ∨ a4 = 2#u8) (allowed5 : a5 = 0#u8 ∨ a5 = 2#u8)
    (headBytes : head.val = [136#u8, 2#u8, tagValue response])
    (accepted : preflight input head (kinds a0 a1 a2 a3 a4 a5) = .ok (.Some ())) :
    ∃ values : List Atom, values.length = 8 ∧
      input.val = RegistrationHeaderCanonical.encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes values ∧
      input.length ≤ 33554432 := by
  obtain ⟨admitted, ⟨⟨begin, work⟩⟩⟩ := accepted_path input head a0 a1 a2 a3 a4 a5 accepted
  obtain ⟨fields, length, _, contents⟩ := six_atoms input head a0 a1 a2 a3 a4 a5
    allowed0 allowed1 allowed2 allowed3 allowed4 allowed5 begin work
  let values := [Atom.uint (.short 2#u8 (by decide)), Atom.uint (tagForm response)] ++ fields
  have rendered : atomsBytes values = [2#u8, tagValue response] ++ atomsBytes fields := by
    cases response <;> rfl
  refine ⟨values, ?_, ?_, admitted⟩
  · simp only [values, List.length_append, List.length_cons, List.length_nil, length]
  · rw [RegistrationSchemaAtoms.array_header, rendered]
    simpa only [headBytes, List.cons_append, List.nil_append] using contents

theorem checks [RegistrationValidatorPrimitive.Operations]
    (input head : Slice U8) (response : Bool) (a0 a1 a2 a3 a4 a5 : U8)
    (allowed0 : a0 = 0#u8 ∨ a0 = 2#u8) (allowed1 : a1 = 0#u8 ∨ a1 = 2#u8)
    (allowed2 : a2 = 0#u8 ∨ a2 = 2#u8) (allowed3 : a3 = 0#u8 ∨ a3 = 2#u8)
    (allowed4 : a4 = 0#u8 ∨ a4 = 2#u8) (allowed5 : a5 = 0#u8 ∨ a5 = 2#u8)
    (headBytes : head.val = [136#u8, 2#u8, tagValue response])
    (accepted : preflight input head (kinds a0 a1 a2 a3 a4 a5) = .ok (.Some ())) :
    cbor_validate input = .ok input.len ∧ extraction_canonical_scan_1 input = .ok true := by
  obtain ⟨values, length, contents, _⟩ := atoms input head response a0 a1 a2 a3 a4 a5
    allowed0 allowed1 allowed2 allowed3 allowed4 allowed5 headBytes accepted
  exact ⟨RegistrationLooseRawTrace.validate input values length contents,
    RegistrationLooseOrderTrace.scan input values length contents⟩

set_option backward.isDefEq.respectTransparency false in
theorem init_checks [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input RegistrationPreflightRecords.initStart
      ((Array.repeat 6#usize 2#u8).to_slice) = .ok (.Some ())) :
    cbor_validate input = .ok input.len ∧ extraction_canonical_scan_1 input = .ok true := by
  rw [RegistrationPublicDecoderControl.preflight_array, ← RegistrationPreflightRecords.init_kinds_source] at accepted
  exact checks input RegistrationPreflightRecords.initStart false 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) rfl accepted

set_option backward.isDefEq.respectTransparency false in
theorem response_checks [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (accepted : registration_validator_primitive.preflightSlice input RegistrationPreflightRecords.responseStart
      ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ())) :
    cbor_validate input = .ok input.len ∧ extraction_canonical_scan_1 input = .ok true := by
  rw [RegistrationPublicDecoderControl.preflight_array, ← RegistrationPreflightRecords.response_kinds_source] at accepted
  exact checks input RegistrationPreflightRecords.responseStart true 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8
    (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) rfl accepted
end BeaconcryptCore.Refinement.RegistrationPreflightValidation

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightValidation.atoms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightValidation.atoms

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightValidation.checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightValidation.checks

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightValidation.init_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightValidation.init_checks

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightValidation.response_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightValidation.response_checks
