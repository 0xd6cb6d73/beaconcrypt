-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightTotal
import BeaconcryptCore.Refinement.RegistrationPreflightFour
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour
open beaconcrypt_parse RegistrationPreflightFour RegistrationPreflightTotal
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem accepted_path (input start : Slice U8) (a0 a1 a2 a3 : U8)
    (accepted : extraction_preflight_four input start (kinds a0 a1 a2 a3) = .ok (.Some ())) :
    input.length ≤ 33554432 ∧ Nonempty (Σ begin : Start input start, Chain begin.tail a0 a1 a2 a3) := by
  by_cases admitted : input.length ≤ 33554432
  · have cap : beaconcrypt_core.transport.complete_message_size_admitted input.len = .ok true := by
      rw [BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact]
      simp only [Slice.len_val, admitted, decide_true]
    obtain ⟨r0, run0⟩ := strip_total input start
    cases r0 with
    | none => simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
    | some tail0 =>
      obtain ⟨r1, run1⟩ := field_total tail0 a0
      cases r1 with
      | none => simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
      | some tail1 =>
        obtain ⟨r2, run2⟩ := field_total tail1 a1
        cases r2 with
        | none => simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
        | some tail2 =>
          obtain ⟨r3, run3⟩ := field_total tail2 a2
          cases r3 with
          | none => simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
          | some tail3 =>
            obtain ⟨r4, run4⟩ := field_total tail3 a3
            cases r4 with
            | none => simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
            | some tail4 =>
              simp [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightFour.kinds, Array.make, Array.index_usize, core.slice.Slice.is_empty, RegistrationCodecStandardSlices.thenSomeUnit] at accepted
              let begin : Start input start := ⟨tail0, run0⟩
              let work : Chain begin.tail a0 a1 a2 a3 := {
                first := ⟨tail1, run1⟩
                second := ⟨tail2, run2⟩
                third := ⟨tail3, run3⟩
                fourth := ⟨tail4, run4⟩
                consumed := accepted }
              exact ⟨admitted, ⟨⟨begin, work⟩⟩⟩
  · simp only [extraction_preflight_four, core.slice.Slice.len, rust_primitives.slice.slice_length,
      BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact,
      bind_tc_ok, Slice.len_val, admitted, decide_false, Bool.false_eq_true, ↓reduceIte] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible

theorem accepted_iff (input start : Slice U8) (a0 a1 a2 a3 : U8) :
    extraction_preflight_four input start (kinds a0 a1 a2 a3) = .ok (.Some ()) ↔
      input.length ≤ 33554432 ∧ Nonempty (Σ begin : Start input start, Chain begin.tail a0 a1 a2 a3) := by
  constructor
  · exact accepted_path input start a0 a1 a2 a3
  · rintro ⟨admitted, ⟨⟨begin, work⟩⟩⟩
    exact RegistrationPreflightFour.run input start a0 a1 a2 a3 begin work admitted
end BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour.accepted_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour.accepted_path

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour.accepted_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightCoverageFour.accepted_iff
