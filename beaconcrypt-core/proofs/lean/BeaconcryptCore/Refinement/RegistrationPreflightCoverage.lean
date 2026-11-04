-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationPreflightTotal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightCoverage
open beaconcrypt_parse RegistrationPreflightSix RegistrationPreflightTotal
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
theorem accepted_path (input start : Slice U8) (a0 a1 a2 a3 a4 a5 : U8)
    (accepted : preflight input start (kinds a0 a1 a2 a3 a4 a5) = .ok (.Some ())) :
    input.length ≤ 33554432 ∧ Nonempty (Σ begin : Start input start, Chain begin.tail a0 a1 a2 a3 a4 a5) := by
  by_cases admitted : input.length ≤ 33554432
  · have cap : beaconcrypt_core.transport.complete_message_size_admitted input.len = .ok true := by
      rw [BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact]
      simp only [Slice.len_val, admitted, decide_true]
    obtain ⟨r0, run0⟩ := strip_total input start
    cases r0 with
    | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
    | some tail0 =>
      obtain ⟨r1, run1⟩ := field_total tail0 a0
      cases r1 with
      | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
      | some tail1 =>
        obtain ⟨r2, run2⟩ := field_total tail1 a1
        cases r2 with
        | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
        | some tail2 =>
          obtain ⟨r3, run3⟩ := field_total tail2 a2
          cases r3 with
          | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
          | some tail3 =>
            obtain ⟨r4, run4⟩ := field_total tail3 a3
            cases r4 with
            | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
            | some tail4 =>
              obtain ⟨r5, run5⟩ := field_total tail4 a4
              cases r5 with
              | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
              | some tail5 =>
                obtain ⟨r6, run6⟩ := field_total tail5 a5
                cases r6 with
                | none => simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, run6, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual] at accepted
                | some tail6 =>
                  simp [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length, cap, bind_tc_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, run0, run1, run2, run3, run4, run5, run6, RegistrationPreflightSix.kinds, Array.make, Array.index_usize, core.slice.Slice.is_empty, RegistrationCodecStandardSlices.thenSomeUnit] at accepted
                  let begin : Start input start := ⟨tail0, run0⟩
                  let work : Chain begin.tail a0 a1 a2 a3 a4 a5 := {
                    first := ⟨tail1, run1⟩
                    second := ⟨tail2, run2⟩
                    third := ⟨tail3, run3⟩
                    fourth := ⟨tail4, run4⟩
                    fifth := ⟨tail5, run5⟩
                    sixth := ⟨tail6, run6⟩
                    consumed := accepted }
                  exact ⟨admitted, ⟨⟨begin, work⟩⟩⟩
  · simp only [preflight, core.slice.Slice.len, rust_primitives.slice.slice_length,
      BeaconcryptCore.Refinement.Transport.complete_message_size_admitted_exact,
      bind_tc_ok, Slice.len_val, admitted, decide_false, Bool.false_eq_true, ↓reduceIte] at accepted
    have impossible := RustM.ok.inj accepted
    cases impossible

theorem accepted_iff (input start : Slice U8) (a0 a1 a2 a3 a4 a5 : U8) :
    preflight input start (kinds a0 a1 a2 a3 a4 a5) = .ok (.Some ()) ↔
      input.length ≤ 33554432 ∧ Nonempty (Σ begin : Start input start, Chain begin.tail a0 a1 a2 a3 a4 a5) := by
  constructor
  · exact accepted_path input start a0 a1 a2 a3 a4 a5
  · rintro ⟨admitted, ⟨⟨begin, work⟩⟩⟩
    exact RegistrationPreflightSix.run input start a0 a1 a2 a3 a4 a5 begin work admitted
end BeaconcryptCore.Refinement.RegistrationPreflightCoverage

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightCoverage.accepted_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightCoverage.accepted_path

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightCoverage.accepted_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightCoverage.accepted_iff
