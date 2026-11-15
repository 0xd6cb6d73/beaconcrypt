-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightSix
import BeaconcryptCore.Refinement.Transport
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! The actual unrolled four-field handwritten preflight composes source prefix stripping and four source field transitions. Successful transitions retain the returned slices, and the final original empty-input check is executed before returning Some unit. The source complete-message admission guard is retained; concrete record constructors discharge every transition. -/
namespace BeaconcryptCore.Refinement.RegistrationPreflightFour
open beaconcrypt_parse cbordetveraux
open RegistrationHeaderCanonical RegistrationPreflightFields

def kinds (a0 a1 a2 a3 : U8) : Array U8 4#usize := Array.make 4#usize [a0, a1, a2, a3]

abbrev Start := RegistrationPreflightSix.Start
abbrev Stage := RegistrationPreflightSix.Stage

structure Chain (input : Slice U8) (a0 a1 a2 a3 : U8) where
  first : Stage input a0
  second : Stage first.tail a1
  third : Stage second.tail a2
  fourth : Stage third.tail a3
  consumed : fourth.tail.val = []

set_option backward.isDefEq.respectTransparency false in
theorem start (input head : Slice U8) (rest : List U8) (contents : input.val = head.val ++ rest) :
    ∃ begin : Start input head, begin.tail.val = rest := by
  obtain ⟨tail, bytes, source⟩ := RegistrationPreflightFields.strip input head rest contents
  exact ⟨⟨tail, source⟩, bytes⟩

set_option backward.isDefEq.respectTransparency false in
theorem uint_stage (input : Slice U8) (value : U64) (rest : List U8)
    (contents : input.val = encodedBytes cbor_major_type_uint64 value ++ rest) :
    ∃ work : Stage input 0#u8, work.tail.val = rest := by
  obtain ⟨tail, bytes, source⟩ := RegistrationPreflightFields.field_uint input value rest contents
  exact ⟨⟨tail, source⟩, bytes⟩

set_option backward.isDefEq.respectTransparency false in
theorem bytes_stage (input payload : Slice U8) (rest : List U8)
    (contents : input.val = (encodedBytes cbor_major_type_byte_string (UScalar.cast .U64 payload.len) ++ payload.val) ++ rest) :
    ∃ work : Stage input 2#u8, work.tail.val = rest := by
  obtain ⟨tail, bytes, source⟩ := RegistrationPreflightFields.field_bytes input payload rest contents
  exact ⟨⟨tail, source⟩, bytes⟩

set_option backward.isDefEq.respectTransparency false in
theorem run (input head : Slice U8) (a0 a1 a2 a3 : U8)
    (begin : Start input head) (work : Chain begin.tail a0 a1 a2 a3)
    (admitted : input.length ≤ 33_554_432) :
    extraction_preflight_four input head (kinds a0 a1 a2 a3) = .ok (.Some ()) := by
  have cap : beaconcrypt_core.transport.complete_message_size_admitted input.len = .ok true := by
    rw [BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact]
    simp only [Slice.len_val, admitted, decide_true]
  have zero : work.fourth.tail.len = 0#usize := by
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val, Slice.length, work.consumed]
    rfl
  have done : core.slice.Slice.is_empty work.fourth.tail = .ok true := by
    simp [core.slice.Slice.is_empty, core.slice.Slice.len, rust_primitives.slice.slice_length, zero]
  simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap,
    begin.source, kinds, Array.make, Array.index_usize,
    work.first.source, work.second.source, work.third.source,
    work.fourth.source,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    done, RegistrationCodecStandardSlices.then_some_unit_true, bind_tc_ok]
end BeaconcryptCore.Refinement.RegistrationPreflightFour

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFour.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFour.start

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFour.uint_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFour.uint_stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFour.bytes_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFour.bytes_stage

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightFour.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightFour.run
