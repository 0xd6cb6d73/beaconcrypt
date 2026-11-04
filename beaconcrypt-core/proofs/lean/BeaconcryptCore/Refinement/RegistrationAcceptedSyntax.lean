-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationLooseWidthTrace
import BeaconcryptCore.Refinement.RegistrationPreflightValidation
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationAcceptedSyntax
open beaconcrypt_parse cbordetveraux RegistrationPreflightRecords RegistrationPreflightSix
open RegistrationLooseArgument RegistrationLooseFieldSpan RegistrationLooseWidthTrace

set_option backward.isDefEq.respectTransparency false in
theorem bstr_field (input tail : Slice U8)
    (accepted : extraction_preflight_field input 2#u8 = .ok (.Some tail)) :
    ∃ form : Form, ∃ payload : Slice U8, ∃ _ : value form = UScalar.cast .U64 payload.len,
      input.val = (bytes 2#u8 form ++ payload.val) ++ tail.val := by
  obtain ⟨atom, kind, contents⟩ := bytes_span input tail accepted
  cases atom with
  | uint form =>
    have unequal : (0#u8 : U8) ≠ 2#u8 := by decide
    exact False.elim (unequal kind)
  | bytes form payload size => exact ⟨form, payload, size, contents⟩

set_option backward.isDefEq.respectTransparency false in
theorem uint_field (input tail : Slice U8)
    (accepted : extraction_preflight_field input 0#u8 = .ok (.Some tail)) :
    ∃ form : Form, input.val = bytes 0#u8 form ++ tail.val := by
  obtain ⟨atom, kind, contents⟩ := uint_span input tail accepted
  cases atom with
  | uint form => exact ⟨form, contents⟩
  | bytes form payload size =>
    have unequal : (2#u8 : U8) ≠ 0#u8 := by decide
    exact False.elim (unequal kind)

set_option backward.isDefEq.respectTransparency false in
theorem init [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input initStart ((Array.repeat 6#usize 2#u8).to_slice) = .ok (.Some ()))
    (width : extraction_canonical_scan_0 input = .ok true) :
    ∃ recordValue : transport.initkex, input.val = 136#u8 :: RegistrationSerializerInitBytes.payload recordValue ∧ input.length ≤ 33554432 := by
  rw [RegistrationPublicDecoderControl.preflight_array, ← init_kinds_source] at gate
  obtain ⟨admitted, ⟨⟨begin, work⟩⟩⟩ := RegistrationPreflightCoverage.accepted_path input initStart 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8 gate
  have headBytes := strip_span input initStart begin.tail begin.source
  obtain ⟨form0, payload0, size0, bytes0⟩ := bstr_field begin.tail work.first.tail work.first.source
  obtain ⟨form1, payload1, size1, bytes1⟩ := bstr_field work.first.tail work.second.tail work.second.source
  obtain ⟨form2, payload2, size2, bytes2⟩ := bstr_field work.second.tail work.third.tail work.third.source
  obtain ⟨form3, payload3, size3, bytes3⟩ := bstr_field work.third.tail work.fourth.tail work.fourth.source
  obtain ⟨form4, payload4, size4, bytes4⟩ := bstr_field work.fourth.tail work.fifth.tail work.fifth.source
  obtain ⟨form5, payload5, size5, bytes5⟩ := bstr_field work.fifth.tail work.sixth.tail work.sixth.source
  let recordValue : transport.initkex := ⟨payload0, payload1, payload2, payload3, payload4, payload5⟩
  let values := [Atom.uint (.short 2#u8 (by decide)), Atom.uint (.short 0#u8 (by decide)), Atom.bytes form0 payload0 size0, Atom.bytes form1 payload1 size1, Atom.bytes form2 payload2 size2, Atom.bytes form3 payload3 size3, Atom.bytes form4 payload4 size4, Atom.bytes form5 payload5 size5]
  have raw : input.val = RegistrationHeaderCanonical.encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes values := by
    rw [headBytes, bytes0, bytes1, bytes2, bytes3, bytes4, bytes5, work.consumed, RegistrationSchemaAtoms.array_header]
    rfl
  have minimal : values.all atomMinimal = true :=
    RustM.ok.inj ((scan input values rfl raw).symm.trans width)
  have canonical := atoms_canonical values minimal
  have mapped : values.map canonicalAtom = RegistrationSchemaAtoms.initAtoms recordValue := rfl
  refine ⟨recordValue, ?_, admitted⟩
  rw [raw, canonical, mapped, RegistrationSchemaAtoms.init_bytes, RegistrationSchemaAtoms.array_header]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem response [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (gate : registration_validator_primitive.preflightSlice input responseStart ((Array.make 6#usize [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8]).to_slice) = .ok (.Some ()))
    (width : extraction_canonical_scan_0 input = .ok true) :
    ∃ recordValue : transport.kexresponse, input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload recordValue ∧ input.length ≤ 33554432 := by
  rw [RegistrationPublicDecoderControl.preflight_array, ← response_kinds_source] at gate
  obtain ⟨admitted, ⟨⟨begin, work⟩⟩⟩ := RegistrationPreflightCoverage.accepted_path input responseStart 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8 gate
  have headBytes := strip_span input responseStart begin.tail begin.source
  obtain ⟨form0, payload0, size0, bytes0⟩ := bstr_field begin.tail work.first.tail work.first.source
  obtain ⟨form1, payload1, size1, bytes1⟩ := bstr_field work.first.tail work.second.tail work.second.source
  obtain ⟨form2, payload2, size2, bytes2⟩ := bstr_field work.second.tail work.third.tail work.third.source
  obtain ⟨form3, payload3, size3, bytes3⟩ := bstr_field work.third.tail work.fourth.tail work.fourth.source
  obtain ⟨form4, bytes4⟩ := uint_field work.fourth.tail work.fifth.tail work.fifth.source
  obtain ⟨form5, payload5, size5, bytes5⟩ := bstr_field work.fifth.tail work.sixth.tail work.sixth.source
  let recordValue : transport.kexresponse := ⟨payload0, payload1, payload2, payload3, value form4, payload5⟩
  let values := [Atom.uint (.short 2#u8 (by decide)), Atom.uint (.short 1#u8 (by decide)), Atom.bytes form0 payload0 size0, Atom.bytes form1 payload1 size1, Atom.bytes form2 payload2 size2, Atom.bytes form3 payload3 size3, Atom.uint form4, Atom.bytes form5 payload5 size5]
  have raw : input.val = RegistrationHeaderCanonical.encodedBytes cbor_major_type_array 8#u64 ++ atomsBytes values := by
    rw [headBytes, bytes0, bytes1, bytes2, bytes3, bytes4, bytes5, work.consumed, RegistrationSchemaAtoms.array_header]
    rfl
  have minimal : values.all atomMinimal = true :=
    RustM.ok.inj ((scan input values rfl raw).symm.trans width)
  have canonical := atoms_canonical values minimal
  have mapped : values.map canonicalAtom = RegistrationSchemaAtoms.responseAtoms recordValue := rfl
  refine ⟨recordValue, ?_, admitted⟩
  rw [raw, canonical, mapped, RegistrationSchemaAtoms.response_bytes, RegistrationSchemaAtoms.array_header]
  rfl
end BeaconcryptCore.Refinement.RegistrationAcceptedSyntax

/-- info: 'BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.bstr_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.bstr_field

/-- info: 'BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.uint_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.uint_field

/-- info: 'BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.init

/-- info: 'BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAcceptedSyntax.response
